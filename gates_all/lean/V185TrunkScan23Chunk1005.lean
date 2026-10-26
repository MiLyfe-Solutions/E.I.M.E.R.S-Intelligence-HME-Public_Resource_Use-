import V185TrunkScan23Chunk1004

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5951050 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_5951050 : Nat := 118140960795 + 5951050 * 2 ^ 59
def prefixEnd_5951050 : Nat := 4983230072969 + 3 ^ 40 * 5951050 * 2
def baseEnd_5951050 : Nat := 3055749048939046723206625

theorem tailTrace_5951050 : CollatzResearch.WordTrace tailWord_5951050 prefixEnd_5951050 3055749048939046723206625 := by
  unfold tailWord_5951050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54263156272592420817170651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144701750060246455512455069 54263156272592420817170651)
  ·
    refine ⟨81394734408888631225755977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54263156272592420817170651 81394734408888631225755977)
    ·
      refine ⟨61046050806666473419316983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81394734408888631225755977 61046050806666473419316983)
      ·
        refine ⟨91569076209999710128975475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61046050806666473419316983 91569076209999710128975475)
        ·
          refine ⟨137353614314999565193463213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91569076209999710128975475 137353614314999565193463213)
          ·
            refine ⟨51507605368124836947548705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137353614314999565193463213 51507605368124836947548705)
            ·
              refine ⟨38630704026093627710661529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51507605368124836947548705 38630704026093627710661529)
              ·
                refine ⟨28973028019570220782996147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38630704026093627710661529 28973028019570220782996147)
                ·
                  refine ⟨43459542029355331174494221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28973028019570220782996147 43459542029355331174494221)
                  ·
                    refine ⟨16297328261008249190435333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43459542029355331174494221 16297328261008249190435333)
                    ·
                      refine ⟨3055749048939046723206625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16297328261008249190435333 3055749048939046723206625)
                      ·
                        rfl

theorem cell23_5951050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_5951050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951050 prefixEnd_5951050 := by exact prefixLift 5951050
  have htrace : WordTrace (prefixWord ++ tailWord_5951050) baseStart_5951050 baseEnd_5951050 := by
    simpa [prefixWord, tailWord_5951050, baseEnd_5951050] using wordTrace_append hprefix tailTrace_5951050
  have hstable : (prefixWord ++ tailWord_5951050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951050).length < 2 ^ (prefixWord ++ tailWord_5951050).sum := by decide
  have hdescent : baseEnd_5951050 < baseStart_5951050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951094 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_5951094 : Nat := 118140960795 + 5951094 * 2 ^ 59
def prefixEnd_5951094 : Nat := 4983230072969 + 3 ^ 40 * 5951094 * 2
def baseEnd_5951094 : Nat := 1018590547362614850352141

theorem tailTrace_5951094 : CollatzResearch.WordTrace tailWord_5951094 prefixEnd_5951094 1018590547362614850352141 := by
  unfold tailWord_5951094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565889368888142423955271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144702819934806852522189557 13565889368888142423955271)
  ·
    refine ⟨20348834053332213635932907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13565889368888142423955271 20348834053332213635932907)
    ·
      refine ⟨30523251079998320453899361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20348834053332213635932907 30523251079998320453899361)
      ·
        refine ⟨22892438309998740340424521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30523251079998320453899361 22892438309998740340424521)
        ·
          refine ⟨17169328732499055255318391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22892438309998740340424521 17169328732499055255318391)
          ·
            refine ⟨25753993098748582882977587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17169328732499055255318391 25753993098748582882977587)
            ·
              refine ⟨38630989648122874324466381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25753993098748582882977587 38630989648122874324466381)
              ·
                refine ⟨14486621118046077871674893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38630989648122874324466381 14486621118046077871674893)
                ·
                  refine ⟨5432482919267279201878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14486621118046077871674893 5432482919267279201878085)
                  ·
                    refine ⟨1018590547362614850352141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432482919267279201878085 1018590547362614850352141)
                    ·
                      rfl

theorem cell23_5951094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_5951094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951094 prefixEnd_5951094 := by exact prefixLift 5951094
  have htrace : WordTrace (prefixWord ++ tailWord_5951094) baseStart_5951094 baseEnd_5951094 := by
    simpa [prefixWord, tailWord_5951094, baseEnd_5951094] using wordTrace_append hprefix tailTrace_5951094
  have hstable : (prefixWord ++ tailWord_5951094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951094).length < 2 ^ (prefixWord ++ tailWord_5951094).sum := by decide
  have hdescent : baseEnd_5951094 < baseStart_5951094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951120 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_5951120 : Nat := 118140960795 + 5951120 * 2 ^ 59
def prefixEnd_5951120 : Nat := 4983230072969 + 3 ^ 40 * 5951120 * 2
def baseEnd_5951120 : Nat := 1018594997528287149777101

theorem tailTrace_5951120 : CollatzResearch.WordTrace tailWord_5951120 prefixEnd_5951120 1018594997528287149777101 := by
  unfold tailWord_5951120
  simp only [CollatzResearch.WordTrace]
  refine ⟨108527589100058042611865407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144703452133410723482487209 108527589100058042611865407)
  ·
    refine ⟨162791383650087063917798111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108527589100058042611865407 162791383650087063917798111)
    ·
      refine ⟨244187075475130595876697167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162791383650087063917798111 244187075475130595876697167)
      ·
        refine ⟨366280613212695893815045751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244187075475130595876697167 366280613212695893815045751)
        ·
          refine ⟨549420919819043840722568627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366280613212695893815045751 549420919819043840722568627)
          ·
            refine ⟨824131379728565761083852941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549420919819043840722568627 824131379728565761083852941)
            ·
              refine ⟨309049267398212160406444853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 824131379728565761083852941 309049267398212160406444853)
              ·
                refine ⟨28973368818582390038104205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 309049267398212160406444853 28973368818582390038104205)
                ·
                  refine ⟨10865013306968396264289077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28973368818582390038104205 10865013306968396264289077)
                  ·
                    refine ⟨1018594997528287149777101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10865013306968396264289077 1018594997528287149777101)
                    ·
                      rfl

theorem cell23_5951120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_5951120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951120 prefixEnd_5951120 := by exact prefixLift 5951120
  have htrace : WordTrace (prefixWord ++ tailWord_5951120) baseStart_5951120 baseEnd_5951120 := by
    simpa [prefixWord, tailWord_5951120, baseEnd_5951120] using wordTrace_append hprefix tailTrace_5951120
  have hstable : (prefixWord ++ tailWord_5951120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951120).length < 2 ^ (prefixWord ++ tailWord_5951120).sum := by decide
  have hdescent : baseEnd_5951120 < baseStart_5951120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951158 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_5951158 : Nat := 118140960795 + 5951158 * 2 ^ 59
def prefixEnd_5951158 : Nat := 4983230072969 + 3 ^ 40 * 5951158 * 2
def baseEnd_5951158 : Nat := 339533833872192477850681

theorem tailTrace_5951158 : CollatzResearch.WordTrace tailWord_5951158 prefixEnd_5951158 339533833872192477850681 := by
  unfold tailWord_5951158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13566035260873651107100883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144704376115985611809076085 13566035260873651107100883)
  ·
    refine ⟨20349052891310476660651325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13566035260873651107100883 20349052891310476660651325)
    ·
      refine ⟨7630894834241428747744247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20349052891310476660651325 7630894834241428747744247)
      ·
        refine ⟨11446342251362143121616371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630894834241428747744247 11446342251362143121616371)
        ·
          refine ⟨17169513377043214682424557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11446342251362143121616371 17169513377043214682424557)
          ·
            refine ⟨6438567516391205505909209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17169513377043214682424557 6438567516391205505909209)
            ·
              refine ⟨4828925637293404129431907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6438567516391205505909209 4828925637293404129431907)
              ·
                refine ⟨7243388455940106194147861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828925637293404129431907 7243388455940106194147861)
                ·
                  refine ⟨339533833872192477850681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7243388455940106194147861 339533833872192477850681)
                  ·
                    rfl

theorem cell23_5951158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_5951158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951158 prefixEnd_5951158 := by exact prefixLift 5951158
  have htrace : WordTrace (prefixWord ++ tailWord_5951158) baseStart_5951158 baseEnd_5951158 := by
    simpa [prefixWord, tailWord_5951158, baseEnd_5951158] using wordTrace_append hprefix tailTrace_5951158
  have hstable : (prefixWord ++ tailWord_5951158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951158).length < 2 ^ (prefixWord ++ tailWord_5951158).sum := by decide
  have hdescent : baseEnd_5951158 < baseStart_5951158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951194 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_5951194 : Nat := 118140960795 + 5951194 * 2 ^ 59
def prefixEnd_5951194 : Nat := 4983230072969 + 3 ^ 40 * 5951194 * 2
def baseEnd_5951194 : Nat := 3055822990153294159805963

theorem tailTrace_5951194 : CollatzResearch.WordTrace tailWord_5951194 prefixEnd_5951194 3055822990153294159805963 := by
  unfold tailWord_5951194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54264469300461998965481159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144705251467898663907949757 54264469300461998965481159)
  ·
    refine ⟨81396703950692998448221739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54264469300461998965481159 81396703950692998448221739)
    ·
      refine ⟨122095055926039497672332609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81396703950692998448221739 122095055926039497672332609)
      ·
        refine ⟨91571291944529623254249457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122095055926039497672332609 91571291944529623254249457)
        ·
          refine ⟨68678468958397217440687093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91571291944529623254249457 68678468958397217440687093)
          ·
            refine ⟨6438606464849739135064415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68678468958397217440687093 6438606464849739135064415)
            ·
              refine ⟨9657909697274608702596623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438606464849739135064415 9657909697274608702596623)
              ·
                refine ⟨14486864545911913053894935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9657909697274608702596623 14486864545911913053894935)
                ·
                  refine ⟨21730296818867869580842403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14486864545911913053894935 21730296818867869580842403)
                  ·
                    refine ⟨32595445228301804371263605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21730296818867869580842403 32595445228301804371263605)
                    ·
                      refine ⟨3055822990153294159805963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32595445228301804371263605 3055822990153294159805963)
                      ·
                        rfl

theorem cell23_5951194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_5951194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951194 prefixEnd_5951194 := by exact prefixLift 5951194
  have htrace : WordTrace (prefixWord ++ tailWord_5951194) baseStart_5951194 baseEnd_5951194 := by
    simpa [prefixWord, tailWord_5951194, baseEnd_5951194] using wordTrace_append hprefix tailTrace_5951194
  have hstable : (prefixWord ++ tailWord_5951194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951194).length < 2 ^ (prefixWord ++ tailWord_5951194).sum := by decide
  have hdescent : baseEnd_5951194 < baseStart_5951194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951197 : List Nat := [1, 4, 3, 3, 12]
def baseStart_5951197 : Nat := 118140960795 + 5951197 * 2 ^ 59
def prefixEnd_5951197 : Nat := 4983230072969 + 3 ^ 40 * 5951197 * 2
def baseEnd_5951197 : Nat := 4191803196975662068681

theorem tailTrace_5951197 : CollatzResearch.WordTrace tailWord_5951197 prefixEnd_5951197 4191803196975662068681 := by
  unfold tailWord_5951197
  simp only [CollatzResearch.WordTrace]
  refine ⟨217057986620837127374283845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144705324413891418249522563 217057986620837127374283845)
  ·
    refine ⟨40698372491406961382678221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217057986620837127374283845 40698372491406961382678221)
    ·
      refine ⟨15261889684277610518504333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40698372491406961382678221 15261889684277610518504333)
      ·
        refine ⟨5723208631604103944439125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15261889684277610518504333 5723208631604103944439125)
        ·
          refine ⟨4191803196975662068681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5723208631604103944439125 4191803196975662068681)
          ·
            rfl

theorem cell23_5951197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 12].length) (baseStart_5951197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951197 prefixEnd_5951197 := by exact prefixLift 5951197
  have htrace : WordTrace (prefixWord ++ tailWord_5951197) baseStart_5951197 baseEnd_5951197 := by
    simpa [prefixWord, tailWord_5951197, baseEnd_5951197] using wordTrace_append hprefix tailTrace_5951197
  have hstable : (prefixWord ++ tailWord_5951197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951197).length < 2 ^ (prefixWord ++ tailWord_5951197).sum := by decide
  have hdescent : baseEnd_5951197 < baseStart_5951197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951201 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 2, 4]
def baseStart_5951201 : Nat := 118140960795 + 5951201 * 2 ^ 59
def prefixEnd_5951201 : Nat := 4983230072969 + 3 ^ 40 * 5951201 * 2
def baseEnd_5951201 : Nat := 1018608861505958544139477

theorem tailTrace_5951201 : CollatzResearch.WordTrace tailWord_5951201 prefixEnd_5951201 1018608861505958544139477 := by
  unfold tailWord_5951201
  simp only [CollatzResearch.WordTrace]
  refine ⟨217058132512822636057429457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144705421675215090704952971 217058132512822636057429457)
  ·
    refine ⟨162793599384616977043072093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217058132512822636057429457 162793599384616977043072093)
    ·
      refine ⟨61047599769231366391152035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162793599384616977043072093 61047599769231366391152035)
      ·
        refine ⟨91571399653847049586728053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61047599769231366391152035 91571399653847049586728053)
        ·
          refine ⟨8584818717548160898755755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91571399653847049586728053 8584818717548160898755755)
          ·
            refine ⟨12877228076322241348133633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8584818717548160898755755 12877228076322241348133633)
            ·
              refine ⟨9657921057241681011100225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12877228076322241348133633 9657921057241681011100225)
              ·
                refine ⟨7243440792931260758325169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9657921057241681011100225 7243440792931260758325169)
                ·
                  refine ⟨5432580594698445568743877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243440792931260758325169 5432580594698445568743877)
                  ·
                    refine ⟨1018608861505958544139477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432580594698445568743877 1018608861505958544139477)
                    ·
                      rfl

theorem cell23_5951201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_5951201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951201 prefixEnd_5951201 := by exact prefixLift 5951201
  have htrace : WordTrace (prefixWord ++ tailWord_5951201) baseStart_5951201 baseEnd_5951201 := by
    simpa [prefixWord, tailWord_5951201, baseEnd_5951201] using wordTrace_append hprefix tailTrace_5951201
  have hstable : (prefixWord ++ tailWord_5951201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951201).length < 2 ^ (prefixWord ++ tailWord_5951201).sum := by decide
  have hdescent : baseEnd_5951201 < baseStart_5951201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951252 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5951252 : Nat := 118140960795 + 5951252 * 2 ^ 59
def prefixEnd_5951252 : Nat := 4983230072969 + 3 ^ 40 * 5951252 * 2
def baseEnd_5951252 : Nat := 1018617590677084977626899

theorem tailTrace_5951252 : CollatzResearch.WordTrace tailWord_5951252 prefixEnd_5951252 1018617590677084977626899 := by
  unfold tailWord_5951252
  simp only [CollatzResearch.WordTrace]
  refine ⟨108529996317818935883768005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144706661757091914511690673 108529996317818935883768005)
  ·
    refine ⟨20349374309591050478206501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108529996317818935883768005 20349374309591050478206501)
    ·
      refine ⟨3815507683048321964663719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20349374309591050478206501 3815507683048321964663719)
      ·
        refine ⟨5723261524572482946995579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815507683048321964663719 5723261524572482946995579)
        ·
          refine ⟨8584892286858724420493369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723261524572482946995579 8584892286858724420493369)
          ·
            refine ⟨6438669215144043315370027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8584892286858724420493369 6438669215144043315370027)
            ·
              refine ⟨9658003822716064973055041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438669215144043315370027 9658003822716064973055041)
              ·
                refine ⟨7243502867037048729791281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9658003822716064973055041 7243502867037048729791281)
                ·
                  refine ⟨5432627150277786547343461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243502867037048729791281 5432627150277786547343461)
                  ·
                    refine ⟨1018617590677084977626899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432627150277786547343461 1018617590677084977626899)
                    ·
                      rfl

theorem cell23_5951252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5951252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951252 prefixEnd_5951252 := by exact prefixLift 5951252
  have htrace : WordTrace (prefixWord ++ tailWord_5951252) baseStart_5951252 baseEnd_5951252 := by
    simpa [prefixWord, tailWord_5951252, baseEnd_5951252] using wordTrace_append hprefix tailTrace_5951252
  have hstable : (prefixWord ++ tailWord_5951252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951252).length < 2 ^ (prefixWord ++ tailWord_5951252).sum := by decide
  have hdescent : baseEnd_5951252 < baseStart_5951252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951258 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_5951258 : Nat := 118140960795 + 5951258 * 2 ^ 59
def prefixEnd_5951258 : Nat := 4983230072969 + 3 ^ 40 * 5951258 * 2
def baseEnd_5951258 : Nat := 3055855852915181909405669

theorem tailTrace_5951258 : CollatzResearch.WordTrace tailWord_5951258 prefixEnd_5951258 3055855852915181909405669 := by
  unfold tailWord_5951258
  simp only [CollatzResearch.WordTrace]
  refine ⟨54265052868404033698063607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144706807649077423194836285 54265052868404033698063607)
  ·
    refine ⟨81397579302606050547095411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54265052868404033698063607 81397579302606050547095411)
    ·
      refine ⟨122096368953909075820643117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81397579302606050547095411 122096368953909075820643117)
      ·
        refine ⟨45786138357715903432741169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122096368953909075820643117 45786138357715903432741169)
        ·
          refine ⟨34339603768286927574555877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45786138357715903432741169 34339603768286927574555877)
          ·
            refine ⟨6438675706553798920229227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34339603768286927574555877 6438675706553798920229227)
            ·
              refine ⟨9658013559830698380343841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438675706553798920229227 9658013559830698380343841)
              ·
                refine ⟨7243510169873023785257881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9658013559830698380343841 7243510169873023785257881)
                ·
                  refine ⟨5432632627404767838943411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243510169873023785257881 5432632627404767838943411)
                  ·
                    refine ⟨8148948941107151758415117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5432632627404767838943411 8148948941107151758415117)
                    ·
                      refine ⟨3055855852915181909405669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8148948941107151758415117 3055855852915181909405669)
                      ·
                        rfl

theorem cell23_5951258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_5951258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951258 prefixEnd_5951258 := by exact prefixLift 5951258
  have htrace : WordTrace (prefixWord ++ tailWord_5951258) baseStart_5951258 baseEnd_5951258 := by
    simpa [prefixWord, tailWord_5951258, baseEnd_5951258] using wordTrace_append hprefix tailTrace_5951258
  have hstable : (prefixWord ++ tailWord_5951258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951258).length < 2 ^ (prefixWord ++ tailWord_5951258).sum := by decide
  have hdescent : baseEnd_5951258 < baseStart_5951258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951267 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 3]
def baseStart_5951267 : Nat := 118140960795 + 5951267 * 2 ^ 59
def prefixEnd_5951267 : Nat := 4983230072969 + 3 ^ 40 * 5951267 * 2
def baseEnd_5951267 : Nat := 3055860474241072374193127

theorem tailTrace_5951267 : CollatzResearch.WordTrace tailWord_5951267 prefixEnd_5951267 3055860474241072374193127 := by
  unfold tailWord_5951267
  simp only [CollatzResearch.WordTrace]
  refine ⟨217060539730583529329332055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144707026487055686219554703 217060539730583529329332055)
  ·
    refine ⟨325590809595875293993998083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217060539730583529329332055 325590809595875293993998083)
    ·
      refine ⟨488386214393812940990997125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325590809595875293993998083 488386214393812940990997125)
      ·
        refine ⟨91572415198839926435811961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 488386214393812940990997125 91572415198839926435811961)
        ·
          refine ⟨68679311399129944826858971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91572415198839926435811961 68679311399129944826858971)
          ·
            refine ⟨103018967098694917240288457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68679311399129944826858971 103018967098694917240288457)
            ·
              refine ⟨77264225324021187930216343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103018967098694917240288457 77264225324021187930216343)
              ·
                refine ⟨115896337986031781895324515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77264225324021187930216343 115896337986031781895324515)
                ·
                  refine ⟨173844506979047672842986773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115896337986031781895324515 173844506979047672842986773)
                  ·
                    refine ⟨8148961264642859664515005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173844506979047672842986773 8148961264642859664515005)
                    ·
                      refine ⟨3055860474241072374193127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8148961264642859664515005 3055860474241072374193127)
                      ·
                        rfl

theorem cell23_5951267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_5951267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951267 prefixEnd_5951267 := by exact prefixLift 5951267
  have htrace : WordTrace (prefixWord ++ tailWord_5951267) baseStart_5951267 baseEnd_5951267 := by
    simpa [prefixWord, tailWord_5951267, baseEnd_5951267] using wordTrace_append hprefix tailTrace_5951267
  have hstable : (prefixWord ++ tailWord_5951267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951267).length < 2 ^ (prefixWord ++ tailWord_5951267).sum := by decide
  have hdescent : baseEnd_5951267 < baseStart_5951267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951281 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 1, 4, 2]
def baseStart_5951281 : Nat := 118140960795 + 5951281 * 2 ^ 59
def prefixEnd_5951281 : Nat := 4983230072969 + 3 ^ 40 * 5951281 * 2
def baseEnd_5951281 : Nat := 3055867662970235319418063

theorem tailTrace_5951281 : CollatzResearch.WordTrace tailWord_5951281 prefixEnd_5951281 3055867662970235319418063 := by
  unfold tailWord_5951281
  simp only [CollatzResearch.WordTrace]
  refine ⟨217061050352532809720341697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144707366901688539813561131 217061050352532809720341697)
  ·
    refine ⟨162795787764399607290256273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217061050352532809720341697 162795787764399607290256273)
    ·
      refine ⟨122096840823299705467692205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162795787764399607290256273 122096840823299705467692205)
      ·
        refine ⟨45786315308737389550384577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122096840823299705467692205 45786315308737389550384577)
        ·
          refine ⟨34339736481553042162788433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45786315308737389550384577 34339736481553042162788433)
          ·
            refine ⟨25754802361164781622091325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34339736481553042162788433 25754802361164781622091325)
            ·
              refine ⟨9658050885436793108284247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25754802361164781622091325 9658050885436793108284247)
              ·
                refine ⟨14487076328155189662426371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9658050885436793108284247 14487076328155189662426371)
                ·
                  refine ⟨21730614492232784493639557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14487076328155189662426371 21730614492232784493639557)
                  ·
                    refine ⟨4074490217293647092557417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21730614492232784493639557 4074490217293647092557417)
                    ·
                      refine ⟨3055867662970235319418063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074490217293647092557417 3055867662970235319418063)
                      ·
                        rfl

theorem cell23_5951281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_5951281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951281 prefixEnd_5951281 := by exact prefixLift 5951281
  have htrace : WordTrace (prefixWord ++ tailWord_5951281) baseStart_5951281 baseEnd_5951281 := by
    simpa [prefixWord, tailWord_5951281, baseEnd_5951281] using wordTrace_append hprefix tailTrace_5951281
  have hstable : (prefixWord ++ tailWord_5951281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951281).length < 2 ^ (prefixWord ++ tailWord_5951281).sum := by decide
  have hdescent : baseEnd_5951281 < baseStart_5951281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951321 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 5]
def baseStart_5951321 : Nat := 118140960795 + 5951321 * 2 ^ 59
def prefixEnd_5951321 : Nat := 4983230072969 + 3 ^ 40 * 5951321 * 2
def baseEnd_5951321 : Nat := 339543133577379462546431

theorem tailTrace_5951321 : CollatzResearch.WordTrace tailWord_5951321 prefixEnd_5951321 339543133577379462546431 := by
  unfold tailWord_5951321
  simp only [CollatzResearch.WordTrace]
  refine ⟨217062509272387896551797817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144708339514925264367865211 217062509272387896551797817)
  ·
    refine ⟨162796881954290922413848363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217062509272387896551797817 162796881954290922413848363)
    ·
      refine ⟨244195322931436383620772545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162796881954290922413848363 244195322931436383620772545)
      ·
        refine ⟨183146492198577287715579409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244195322931436383620772545 183146492198577287715579409)
        ·
          refine ⟨137359869148932965786684557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183146492198577287715579409 137359869148932965786684557)
          ·
            refine ⟨51509950930849862170006709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137359869148932965786684557 51509950930849862170006709)
            ·
              refine ⟨4829057899767174578438129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51509950930849862170006709 4829057899767174578438129)
              ·
                refine ⟨3621793424825380933828597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4829057899767174578438129 3621793424825380933828597)
                ·
                  refine ⟨339543133577379462546431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3621793424825380933828597 339543133577379462546431)
                  ·
                    rfl

theorem cell23_5951321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 5].length) (baseStart_5951321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951321 prefixEnd_5951321 := by exact prefixLift 5951321
  have htrace : WordTrace (prefixWord ++ tailWord_5951321) baseStart_5951321 baseEnd_5951321 := by
    simpa [prefixWord, tailWord_5951321, baseEnd_5951321] using wordTrace_append hprefix tailTrace_5951321
  have hstable : (prefixWord ++ tailWord_5951321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951321).length < 2 ^ (prefixWord ++ tailWord_5951321).sum := by decide
  have hdescent : baseEnd_5951321 < baseStart_5951321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951327 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_5951327 : Nat := 118140960795 + 5951327 * 2 ^ 59
def prefixEnd_5951327 : Nat := 4983230072969 + 3 ^ 40 * 5951327 * 2
def baseEnd_5951327 : Nat := 3055891283080342139442851

theorem tailTrace_5951327 : CollatzResearch.WordTrace tailWord_5951327 prefixEnd_5951327 3055891283080342139442851 := by
  unfold tailWord_5951327
  simp only [CollatzResearch.WordTrace]
  refine ⟨217062728110366159576516235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144708485406910773051010823 217062728110366159576516235)
  ·
    refine ⟨325594092165549239364774353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217062728110366159576516235 325594092165549239364774353)
    ·
      refine ⟨244195569124161929523580765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325594092165549239364774353 244195569124161929523580765)
      ·
        refine ⟨91573338421560723571342787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244195569124161929523580765 91573338421560723571342787)
        ·
          refine ⟨137360007632341085357014181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91573338421560723571342787 137360007632341085357014181)
          ·
            refine ⟨25755001431063953504440159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137360007632341085357014181 25755001431063953504440159)
            ·
              refine ⟨38632502146595930256660239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25755001431063953504440159 38632502146595930256660239)
              ·
                refine ⟨57948753219893895384990359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38632502146595930256660239 57948753219893895384990359)
                ·
                  refine ⟨86923129829840843077485539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57948753219893895384990359 86923129829840843077485539)
                  ·
                    refine ⟨130384694744761264616228309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86923129829840843077485539 130384694744761264616228309)
                    ·
                      refine ⟨3055891283080342139442851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130384694744761264616228309 3055891283080342139442851)
                      ·
                        rfl

theorem cell23_5951327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_5951327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951327 prefixEnd_5951327 := by exact prefixLift 5951327
  have htrace : WordTrace (prefixWord ++ tailWord_5951327) baseStart_5951327 baseEnd_5951327 := by
    simpa [prefixWord, tailWord_5951327, baseEnd_5951327] using wordTrace_append hprefix tailTrace_5951327
  have hstable : (prefixWord ++ tailWord_5951327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951327).length < 2 ^ (prefixWord ++ tailWord_5951327).sum := by decide
  have hdescent : baseEnd_5951327 < baseStart_5951327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951332 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_5951332 : Nat := 118140960795 + 5951332 * 2 ^ 59
def prefixEnd_5951332 : Nat := 4983230072969 + 3 ^ 40 * 5951332 * 2
def baseEnd_5951332 : Nat := 3055893850483614619880329

theorem tailTrace_5951332 : CollatzResearch.WordTrace tailWord_5951332 prefixEnd_5951332 3055893850483614619880329 := by
  unfold tailWord_5951332
  simp only [CollatzResearch.WordTrace]
  refine ⟨108531455237674022715224125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144708606983565363620298833 108531455237674022715224125)
  ·
    refine ⟨40699295714127758518209047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108531455237674022715224125 40699295714127758518209047)
    ·
      refine ⟨61048943571191637777313571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40699295714127758518209047 61048943571191637777313571)
      ·
        refine ⟨91573415356787456665970357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61048943571191637777313571 91573415356787456665970357)
        ·
          refine ⟨8585007689698824062434721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91573415356787456665970357 8585007689698824062434721)
          ·
            refine ⟨6438755767274118046826041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8585007689698824062434721 6438755767274118046826041)
            ·
              refine ⟨4829066825455588535119531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6438755767274118046826041 4829066825455588535119531)
              ·
                refine ⟨7243600238183382802679297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829066825455588535119531 7243600238183382802679297)
                ·
                  refine ⟨5432700178637537102009473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243600238183382802679297 5432700178637537102009473)
                  ·
                    refine ⟨4074525133978152826507105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432700178637537102009473 4074525133978152826507105)
                    ·
                      refine ⟨3055893850483614619880329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074525133978152826507105 3055893850483614619880329)
                      ·
                        rfl

theorem cell23_5951332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_5951332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951332 prefixEnd_5951332 := by exact prefixLift 5951332
  have htrace : WordTrace (prefixWord ++ tailWord_5951332) baseStart_5951332 baseEnd_5951332 := by
    simpa [prefixWord, tailWord_5951332, baseEnd_5951332] using wordTrace_append hprefix tailTrace_5951332
  have hstable : (prefixWord ++ tailWord_5951332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951332).length < 2 ^ (prefixWord ++ tailWord_5951332).sum := by decide
  have hdescent : baseEnd_5951332 < baseStart_5951332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951337 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_5951337 : Nat := 118140960795 + 5951337 * 2 ^ 59
def prefixEnd_5951337 : Nat := 4983230072969 + 3 ^ 40 * 5951337 * 2
def baseEnd_5951337 : Nat := 3055896417886887100317805

theorem tailTrace_5951337 : CollatzResearch.WordTrace tailWord_5951337 prefixEnd_5951337 3055896417886887100317805 := by
  unfold tailWord_5951337
  simp only [CollatzResearch.WordTrace]
  refine ⟨217063092840329931284380265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144708728560219954189586843 217063092840329931284380265)
  ·
    refine ⟨162797319630247448463285199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217063092840329931284380265 162797319630247448463285199)
    ·
      refine ⟨244195979445371172694927799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162797319630247448463285199 244195979445371172694927799)
      ·
        refine ⟨366293969168056759042391699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244195979445371172694927799 366293969168056759042391699)
        ·
          refine ⟨549440953752085138563587549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366293969168056759042391699 549440953752085138563587549)
          ·
            refine ⟨206040357657031926961345331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549440953752085138563587549 206040357657031926961345331)
            ·
              refine ⟨309060536485547890442017997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206040357657031926961345331 309060536485547890442017997)
              ·
                refine ⟨115897701182080458915756749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309060536485547890442017997 115897701182080458915756749)
                ·
                  refine ⟨43461637943280172093408781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115897701182080458915756749 43461637943280172093408781)
                  ·
                    refine ⟨16298114228730064535028293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43461637943280172093408781 16298114228730064535028293)
                    ·
                      refine ⟨3055896417886887100317805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16298114228730064535028293 3055896417886887100317805)
                      ·
                        rfl

theorem cell23_5951337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_5951337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951337 prefixEnd_5951337 := by exact prefixLift 5951337
  have htrace : WordTrace (prefixWord ++ tailWord_5951337) baseStart_5951337 baseEnd_5951337 := by
    simpa [prefixWord, tailWord_5951337, baseEnd_5951337] using wordTrace_append hprefix tailTrace_5951337
  have hstable : (prefixWord ++ tailWord_5951337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951337).length < 2 ^ (prefixWord ++ tailWord_5951337).sum := by decide
  have hdescent : baseEnd_5951337 < baseStart_5951337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951354 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_5951354 : Nat := 118140960795 + 5951354 * 2 ^ 59
def prefixEnd_5951354 : Nat := 4983230072969 + 3 ^ 40 * 5951354 * 2
def baseEnd_5951354 : Nat := 3055905147058013533805227

theorem tailTrace_5951354 : CollatzResearch.WordTrace tailWord_5951354 prefixEnd_5951354 3055905147058013533805227 := by
  unfold tailWord_5951354
  simp only [CollatzResearch.WordTrace]
  refine ⟨54265928220317085796937279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144709141920845562125166077 54265928220317085796937279)
  ·
    refine ⟨81398892330475628695405919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54265928220317085796937279 81398892330475628695405919)
    ·
      refine ⟨122098338495713443043108879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81398892330475628695405919 122098338495713443043108879)
      ·
        refine ⟨183147507743570164564663319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122098338495713443043108879 183147507743570164564663319)
        ·
          refine ⟨274721261615355246846994979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183147507743570164564663319 274721261615355246846994979)
          ·
            refine ⟨412081892423032870270492469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274721261615355246846994979 412081892423032870270492469)
            ·
              refine ⟨38632677414659331587858669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 412081892423032870270492469 38632677414659331587858669)
              ·
                refine ⟨14487254030497249345447001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38632677414659331587858669 14487254030497249345447001)
                ·
                  refine ⟨10865440522872937009085251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14487254030497249345447001 10865440522872937009085251)
                  ·
                    refine ⟨16298160784309405513627877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10865440522872937009085251 16298160784309405513627877)
                    ·
                      refine ⟨3055905147058013533805227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16298160784309405513627877 3055905147058013533805227)
                      ·
                        rfl

theorem cell23_5951354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_5951354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951354 prefixEnd_5951354 := by exact prefixLift 5951354
  have htrace : WordTrace (prefixWord ++ tailWord_5951354) baseStart_5951354 baseEnd_5951354 := by
    simpa [prefixWord, tailWord_5951354, baseEnd_5951354] using wordTrace_append hprefix tailTrace_5951354
  have hstable : (prefixWord ++ tailWord_5951354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951354).length < 2 ^ (prefixWord ++ tailWord_5951354).sum := by decide
  have hdescent : baseEnd_5951354 < baseStart_5951354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951377 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 8]
def baseStart_5951377 : Nat := 118140960795 + 5951377 * 2 ^ 59
def prefixEnd_5951377 : Nat := 4983230072969 + 3 ^ 40 * 5951377 * 2
def baseEnd_5951377 : Nat := 339546328568118549313069

theorem tailTrace_5951377 : CollatzResearch.WordTrace tailWord_5951377 prefixEnd_5951377 339546328568118549313069 := by
  unfold tailWord_5951377
  simp only [CollatzResearch.WordTrace]
  refine ⟨217064551760185018115836385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144709701173456678743890923 217064551760185018115836385)
  ·
    refine ⟨162798413820138763586877289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217064551760185018115836385 162798413820138763586877289)
    ·
      refine ⟨122098810365104072690157967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162798413820138763586877289 122098810365104072690157967)
      ·
        refine ⟨183148215547656109035236951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122098810365104072690157967 183148215547656109035236951)
        ·
          refine ⟨274722323321484163552855427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183148215547656109035236951 274722323321484163552855427)
          ·
            refine ⟨412083484982226245329283141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274722323321484163552855427 412083484982226245329283141)
            ·
              refine ⟨77265653434167420999240589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 412083484982226245329283141 77265653434167420999240589)
              ·
                refine ⟨28974620037812782874715221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77265653434167420999240589 28974620037812782874715221)
                ·
                  refine ⟨339546328568118549313069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28974620037812782874715221 339546328568118549313069)
                  ·
                    rfl

theorem cell23_5951377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_5951377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951377 prefixEnd_5951377 := by exact prefixLift 5951377
  have htrace : WordTrace (prefixWord ++ tailWord_5951377) baseStart_5951377 baseEnd_5951377 := by
    simpa [prefixWord, tailWord_5951377, baseEnd_5951377] using wordTrace_append hprefix tailTrace_5951377
  have hstable : (prefixWord ++ tailWord_5951377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951377).length < 2 ^ (prefixWord ++ tailWord_5951377).sum := by decide
  have hdescent : baseEnd_5951377 < baseStart_5951377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951388 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5951388 : Nat := 118140960795 + 5951388 * 2 ^ 59
def prefixEnd_5951388 : Nat := 4983230072969 + 3 ^ 40 * 5951388 * 2
def baseEnd_5951388 : Nat := 3055922605400266400780071

theorem tailTrace_5951388 : CollatzResearch.WordTrace tailWord_5951388 prefixEnd_5951388 3055922605400266400780071 := by
  unfold tailWord_5951388
  simp only [CollatzResearch.WordTrace]
  refine ⟨108532476481572583497243409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144709968642096777996324545 108532476481572583497243409)
  ·
    refine ⟨81399357361179437622932557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108532476481572583497243409 81399357361179437622932557)
    ·
      refine ⟨30524759010442289108599709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81399357361179437622932557 30524759010442289108599709)
      ·
        refine ⟨11446784628915858415724891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30524759010442289108599709 11446784628915858415724891)
        ·
          refine ⟨17170176943373787623587337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11446784628915858415724891 17170176943373787623587337)
          ·
            refine ⟨12877632707530340717690503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17170176943373787623587337 12877632707530340717690503)
            ·
              refine ⟨19316449061295511076535755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12877632707530340717690503 19316449061295511076535755)
              ·
                refine ⟨28974673591943266614803633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19316449061295511076535755 28974673591943266614803633)
                ·
                  refine ⟨21731005193957449961102725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28974673591943266614803633 21731005193957449961102725)
                  ·
                    refine ⟨4074563473867021867706761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21731005193957449961102725 4074563473867021867706761)
                    ·
                      refine ⟨3055922605400266400780071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074563473867021867706761 3055922605400266400780071)
                      ·
                        rfl

theorem cell23_5951388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5951388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951388 prefixEnd_5951388 := by exact prefixLift 5951388
  have htrace : WordTrace (prefixWord ++ tailWord_5951388) baseStart_5951388 baseEnd_5951388 := by
    simpa [prefixWord, tailWord_5951388, baseEnd_5951388] using wordTrace_append hprefix tailTrace_5951388
  have hstable : (prefixWord ++ tailWord_5951388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951388).length < 2 ^ (prefixWord ++ tailWord_5951388).sum := by decide
  have hdescent : baseEnd_5951388 < baseStart_5951388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951431 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_5951431 : Nat := 118140960795 + 5951431 * 2 ^ 59
def prefixEnd_5951431 : Nat := 4983230072969 + 3 ^ 40 * 5951431 * 2
def baseEnd_5951431 : Nat := 3055944685068409732542373

theorem tailTrace_5951431 : CollatzResearch.WordTrace tailWord_5951431 prefixEnd_5951431 3055944685068409732542373 := by
  unfold tailWord_5951431
  simp only [CollatzResearch.WordTrace]
  refine ⟨217066521301989385338302147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144711014201326256892201431 217066521301989385338302147)
  ·
    refine ⟨325599781952984078007453221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217066521301989385338302147 325599781952984078007453221)
    ·
      refine ⟨61049959116184514626397479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325599781952984078007453221 61049959116184514626397479)
      ·
        refine ⟨91574938674276771939596219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61049959116184514626397479 91574938674276771939596219)
        ·
          refine ⟨137362408011415157909394329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91574938674276771939596219 137362408011415157909394329)
          ·
            refine ⟨103021806008561368432045747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137362408011415157909394329 103021806008561368432045747)
            ·
              refine ⟨154532709012842052648068621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103021806008561368432045747 154532709012842052648068621)
              ·
                refine ⟨57949765879815769743025733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154532709012842052648068621 57949765879815769743025733)
                ·
                  refine ⟨10865581102465456826817325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57949765879815769743025733 10865581102465456826817325)
                  ·
                    refine ⟨4074592913424546310056497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10865581102465456826817325 4074592913424546310056497)
                    ·
                      refine ⟨3055944685068409732542373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074592913424546310056497 3055944685068409732542373)
                      ·
                        rfl

theorem cell23_5951431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_5951431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951431 prefixEnd_5951431 := by exact prefixLift 5951431
  have htrace : WordTrace (prefixWord ++ tailWord_5951431) baseStart_5951431 baseEnd_5951431 := by
    simpa [prefixWord, tailWord_5951431, baseEnd_5951431] using wordTrace_append hprefix tailTrace_5951431
  have hstable : (prefixWord ++ tailWord_5951431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951431).length < 2 ^ (prefixWord ++ tailWord_5951431).sum := by decide
  have hdescent : baseEnd_5951431 < baseStart_5951431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951438 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_5951438 : Nat := 118140960795 + 5951438 * 2 ^ 59
def prefixEnd_5951438 : Nat := 4983230072969 + 3 ^ 40 * 5951438 * 2
def baseEnd_5951438 : Nat := 3055948279432991205154841

theorem tailTrace_5951438 : CollatzResearch.WordTrace tailWord_5951438 prefixEnd_5951438 3055948279432991205154841 := by
  unfold tailWord_5951438
  simp only [CollatzResearch.WordTrace]
  refine ⟨27133347076620503191725871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144711184408642683689204645 27133347076620503191725871)
  ·
    refine ⟨40700020614930754787588807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27133347076620503191725871 40700020614930754787588807)
    ·
      refine ⟨61050030922396132181383211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40700020614930754787588807 61050030922396132181383211)
      ·
        refine ⟨91575046383594198272074817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61050030922396132181383211 91575046383594198272074817)
        ·
          refine ⟨68681284787695648704056113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91575046383594198272074817 68681284787695648704056113)
          ·
            refine ⟨51510963590771736528042085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68681284787695648704056113 51510963590771736528042085)
            ·
              refine ⟨9658305673269700599007891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51510963590771736528042085 9658305673269700599007891)
              ·
                refine ⟨14487458509904550898511837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9658305673269700599007891 14487458509904550898511837)
                ·
                  refine ⟨5432796941214206586941939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14487458509904550898511837 5432796941214206586941939)
                  ·
                    refine ⟨8149195411821309880412909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5432796941214206586941939 8149195411821309880412909)
                    ·
                      refine ⟨3055948279432991205154841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8149195411821309880412909 3055948279432991205154841)
                      ·
                        rfl

theorem cell23_5951438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_5951438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951438 prefixEnd_5951438 := by exact prefixLift 5951438
  have htrace : WordTrace (prefixWord ++ tailWord_5951438) baseStart_5951438 baseEnd_5951438 := by
    simpa [prefixWord, tailWord_5951438, baseEnd_5951438] using wordTrace_append hprefix tailTrace_5951438
  have hstable : (prefixWord ++ tailWord_5951438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951438).length < 2 ^ (prefixWord ++ tailWord_5951438).sum := by decide
  have hdescent : baseEnd_5951438 < baseStart_5951438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951464 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5951464 : Nat := 118140960795 + 5951464 * 2 ^ 59
def prefixEnd_5951464 : Nat := 4983230072969 + 3 ^ 40 * 5951464 * 2
def baseEnd_5951464 : Nat := 3055961629930008103429721

theorem tailTrace_5951464 : CollatzResearch.WordTrace tailWord_5951464 prefixEnd_5951464 3055961629930008103429721 := by
  unfold tailWord_5951464
  simp only [CollatzResearch.WordTrace]
  refine ⟨108533862455434915987126723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144711816607246554649502297 108533862455434915987126723)
  ·
    refine ⟨162800793683152373980690085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108533862455434915987126723 162800793683152373980690085)
    ·
      refine ⟨30525148815591070121379391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162800793683152373980690085 30525148815591070121379391)
      ·
        refine ⟨45787723223386605182069087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30525148815591070121379391 45787723223386605182069087)
        ·
          refine ⟨68681584835079907773103631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45787723223386605182069087 68681584835079907773103631)
          ·
            refine ⟨103022377252619861659655447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68681584835079907773103631 103022377252619861659655447)
            ·
              refine ⟨154533565878929792489483171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103022377252619861659655447 154533565878929792489483171)
              ·
                refine ⟨231800348818394688734224757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154533565878929792489483171 231800348818394688734224757)
                ·
                  refine ⟨21731282701724502068833571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231800348818394688734224757 21731282701724502068833571)
                  ·
                    refine ⟨32596924052586753103250357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21731282701724502068833571 32596924052586753103250357)
                    ·
                      refine ⟨3055961629930008103429721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32596924052586753103250357 3055961629930008103429721)
                      ·
                        rfl

theorem cell23_5951464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5951464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951464 prefixEnd_5951464 := by exact prefixLift 5951464
  have htrace : WordTrace (prefixWord ++ tailWord_5951464) baseStart_5951464 baseEnd_5951464 := by
    simpa [prefixWord, tailWord_5951464, baseEnd_5951464] using wordTrace_append hprefix tailTrace_5951464
  have hstable : (prefixWord ++ tailWord_5951464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951464).length < 2 ^ (prefixWord ++ tailWord_5951464).sum := by decide
  have hdescent : baseEnd_5951464 < baseStart_5951464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951481 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_5951481 : Nat := 118140960795 + 5951481 * 2 ^ 59
def prefixEnd_5951481 : Nat := 4983230072969 + 3 ^ 40 * 5951481 * 2
def baseEnd_5951481 : Nat := 3055970359101134536917143

theorem tailTrace_5951481 : CollatzResearch.WordTrace tailWord_5951481 prefixEnd_5951481 3055970359101134536917143 := by
  unfold tailWord_5951481
  simp only [CollatzResearch.WordTrace]
  refine ⟨217068344951808243877622297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144712229967872162585081531 217068344951808243877622297)
  ·
    refine ⟨162801258713856182908216723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217068344951808243877622297 162801258713856182908216723)
    ·
      refine ⟨244201888070784274362325085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162801258713856182908216723 244201888070784274362325085)
      ·
        refine ⟨91575708026544102885871907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244201888070784274362325085 91575708026544102885871907)
        ·
          refine ⟨137363562039816154328807861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91575708026544102885871907 137363562039816154328807861)
          ·
            refine ⟨12877833941232764468325737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137363562039816154328807861 12877833941232764468325737)
            ·
              refine ⟨9658375455924573351244303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12877833941232764468325737 9658375455924573351244303)
              ·
                refine ⟨14487563183886860026866455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9658375455924573351244303 14487563183886860026866455)
                ·
                  refine ⟨21731344775830290040299683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14487563183886860026866455 21731344775830290040299683)
                  ·
                    refine ⟨32597017163745435060449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21731344775830290040299683 32597017163745435060449525)
                    ·
                      refine ⟨3055970359101134536917143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32597017163745435060449525 3055970359101134536917143)
                      ·
                        rfl

theorem cell23_5951481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_5951481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951481 prefixEnd_5951481 := by exact prefixLift 5951481
  have htrace : WordTrace (prefixWord ++ tailWord_5951481) baseStart_5951481 baseEnd_5951481 := by
    simpa [prefixWord, tailWord_5951481, baseEnd_5951481] using wordTrace_append hprefix tailTrace_5951481
  have hstable : (prefixWord ++ tailWord_5951481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951481).length < 2 ^ (prefixWord ++ tailWord_5951481).sum := by decide
  have hdescent : baseEnd_5951481 < baseStart_5951481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951495 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5951495 : Nat := 118140960795 + 5951495 * 2 ^ 59
def prefixEnd_5951495 : Nat := 4983230072969 + 3 ^ 40 * 5951495 * 2
def baseEnd_5951495 : Nat := 3055977547830297482142079

theorem tailTrace_5951495 : CollatzResearch.WordTrace tailWord_5951495 prefixEnd_5951495 3055977547830297482142079 := by
  unfold tailWord_5951495
  simp only [CollatzResearch.WordTrace]
  refine ⟨217068855573757524268631939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144712570382505016179087959 217068855573757524268631939)
  ·
    refine ⟨325603283360636286402947909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217068855573757524268631939 325603283360636286402947909)
    ·
      refine ⟨61050615630119303700552733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325603283360636286402947909 61050615630119303700552733)
      ·
        refine ⟨22893980861294738887707275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61050615630119303700552733 22893980861294738887707275)
        ·
          refine ⟨34340971291942108331560913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22893980861294738887707275 34340971291942108331560913)
          ·
            refine ⟨25755728468956581248670685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34340971291942108331560913 25755728468956581248670685)
            ·
              refine ⟨9658398175858717968251507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25755728468956581248670685 9658398175858717968251507)
              ·
                refine ⟨14487597263788076952377261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9658398175858717968251507 14487597263788076952377261)
                ·
                  refine ⟨5432848973920528857141473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14487597263788076952377261 5432848973920528857141473)
                  ·
                    refine ⟨4074636730440396642856105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432848973920528857141473 4074636730440396642856105)
                    ·
                      refine ⟨3055977547830297482142079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074636730440396642856105 3055977547830297482142079)
                      ·
                        rfl

theorem cell23_5951495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5951495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951495 prefixEnd_5951495 := by exact prefixLift 5951495
  have htrace : WordTrace (prefixWord ++ tailWord_5951495) baseStart_5951495 baseEnd_5951495 := by
    simpa [prefixWord, tailWord_5951495, baseEnd_5951495] using wordTrace_append hprefix tailTrace_5951495
  have hstable : (prefixWord ++ tailWord_5951495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951495).length < 2 ^ (prefixWord ++ tailWord_5951495).sum := by decide
  have hdescent : baseEnd_5951495 < baseStart_5951495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951568 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 8, 2, 2]
def baseStart_5951568 : Nat := 118140960795 + 5951568 * 2 ^ 59
def prefixEnd_5951568 : Nat := 4983230072969 + 3 ^ 40 * 5951568 * 2
def baseEnd_5951568 : Nat := 3056015031918075696529243

theorem tailTrace_5951568 : CollatzResearch.WordTrace tailWord_5951568 prefixEnd_5951568 3056015031918075696529243 := by
  unfold tailWord_5951568
  simp only [CollatzResearch.WordTrace]
  refine ⟨108535759051246528868019679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144714345401662038490692905 108535759051246528868019679)
  ·
    refine ⟨162803638576869793302029519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108535759051246528868019679 162803638576869793302029519)
    ·
      refine ⟨244205457865304689953044279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162803638576869793302029519 244205457865304689953044279)
      ·
        refine ⟨366308186797957034929566419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244205457865304689953044279 366308186797957034929566419)
        ·
          refine ⟨549462280196935552394349629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366308186797957034929566419 549462280196935552394349629)
          ·
            refine ⟨206048355073850832147881111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549462280196935552394349629 206048355073850832147881111)
            ·
              refine ⟨309072532610776248221821667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206048355073850832147881111 309072532610776248221821667)
              ·
                refine ⟨463608798916164372332732501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309072532610776248221821667 463608798916164372332732501)
                ·
                  refine ⟨5432915612298801238274209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 463608798916164372332732501 5432915612298801238274209)
                  ·
                    refine ⟨4074686709224100928705657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432915612298801238274209 4074686709224100928705657)
                    ·
                      refine ⟨3056015031918075696529243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074686709224100928705657 3056015031918075696529243)
                      ·
                        rfl

theorem cell23_5951568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 2, 2].length) (baseStart_5951568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951568 prefixEnd_5951568 := by exact prefixLift 5951568
  have htrace : WordTrace (prefixWord ++ tailWord_5951568) baseStart_5951568 baseEnd_5951568 := by
    simpa [prefixWord, tailWord_5951568, baseEnd_5951568] using wordTrace_append hprefix tailTrace_5951568
  have hstable : (prefixWord ++ tailWord_5951568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951568).length < 2 ^ (prefixWord ++ tailWord_5951568).sum := by decide
  have hdescent : baseEnd_5951568 < baseStart_5951568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951601 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_5951601 : Nat := 118140960795 + 5951601 * 2 ^ 59
def prefixEnd_5951601 : Nat := 4983230072969 + 3 ^ 40 * 5951601 * 2
def baseEnd_5951601 : Nat := 3056031976779674067416591

theorem tailTrace_5951601 : CollatzResearch.WordTrace tailWord_5951601 prefixEnd_5951601 3056031976779674067416591 := by
  unfold tailWord_5951601
  simp only [CollatzResearch.WordTrace]
  refine ⟨217072721711373504371990657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144715147807582336247993771 217072721711373504371990657)
  ·
    refine ⟨162804541283530128278992993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217072721711373504371990657 162804541283530128278992993)
    ·
      refine ⟨122103405962647596209244745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162804541283530128278992993 122103405962647596209244745)
      ·
        refine ⟨91577554471985697156933559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122103405962647596209244745 91577554471985697156933559)
        ·
          refine ⟨137366331707978545735400339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91577554471985697156933559 137366331707978545735400339)
          ·
            refine ⟨206049497561967818603100509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137366331707978545735400339 206049497561967818603100509)
            ·
              refine ⟨77268561585737931976162691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206049497561967818603100509 77268561585737931976162691)
              ·
                refine ⟨115902842378606897964244037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77268561585737931976162691 115902842378606897964244037)
                ·
                  refine ⟨21731782945988793368295757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115902842378606897964244037 21731782945988793368295757)
                  ·
                    refine ⟨8149418604745797513110909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21731782945988793368295757 8149418604745797513110909)
                    ·
                      refine ⟨3056031976779674067416591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8149418604745797513110909 3056031976779674067416591)
                      ·
                        rfl

theorem cell23_5951601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_5951601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951601 prefixEnd_5951601 := by exact prefixLift 5951601
  have htrace : WordTrace (prefixWord ++ tailWord_5951601) baseStart_5951601 baseEnd_5951601 := by
    simpa [prefixWord, tailWord_5951601, baseEnd_5951601] using wordTrace_append hprefix tailTrace_5951601
  have hstable : (prefixWord ++ tailWord_5951601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951601).length < 2 ^ (prefixWord ++ tailWord_5951601).sum := by decide
  have hdescent : baseEnd_5951601 < baseStart_5951601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951602 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_5951602 : Nat := 118140960795 + 5951602 * 2 ^ 59
def prefixEnd_5951602 : Nat := 4983230072969 + 3 ^ 40 * 5951602 * 2
def baseEnd_5951602 : Nat := 3056032490260328563504087

theorem tailTrace_5951602 : CollatzResearch.WordTrace tailWord_5951602 prefixEnd_5951602 3056032490260328563504087 := by
  unfold tailWord_5951602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54268189546092470385694265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144715172122913254361851373 54268189546092470385694265)
  ·
    refine ⟨40701142159569352789270699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54268189546092470385694265 40701142159569352789270699)
    ·
      refine ⟨61051713239354029183906049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40701142159569352789270699 61051713239354029183906049)
      ·
        refine ⟨45788784929515521887929537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61051713239354029183906049 45788784929515521887929537)
        ·
          refine ⟨34341588697136641415947153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45788784929515521887929537 34341588697136641415947153)
          ·
            refine ⟨25756191522852481061960365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34341588697136641415947153 25756191522852481061960365)
            ·
              refine ⟨9658571821069680398235137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25756191522852481061960365 9658571821069680398235137)
              ·
                refine ⟨7243928865802260298676353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9658571821069680398235137 7243928865802260298676353)
                ·
                  refine ⟨5432946649351695224007265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243928865802260298676353 5432946649351695224007265)
                  ·
                    refine ⟨4074709987013771418005449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5432946649351695224007265 4074709987013771418005449)
                    ·
                      refine ⟨3056032490260328563504087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074709987013771418005449 3056032490260328563504087)
                      ·
                        rfl

theorem cell23_5951602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_5951602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951602 prefixEnd_5951602 := by exact prefixLift 5951602
  have htrace : WordTrace (prefixWord ++ tailWord_5951602) baseStart_5951602 baseEnd_5951602 := by
    simpa [prefixWord, tailWord_5951602, baseEnd_5951602] using wordTrace_append hprefix tailTrace_5951602
  have hstable : (prefixWord ++ tailWord_5951602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951602).length < 2 ^ (prefixWord ++ tailWord_5951602).sum := by decide
  have hdescent : baseEnd_5951602 < baseStart_5951602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951621 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_5951621 : Nat := 118140960795 + 5951621 * 2 ^ 59
def prefixEnd_5951621 : Nat := 4983230072969 + 3 ^ 40 * 5951621 * 2
def baseEnd_5951621 : Nat := 1018680748797587996388833

theorem tailTrace_5951621 : CollatzResearch.WordTrace tailWord_5951621 prefixEnd_5951621 1018680748797587996388833 := by
  unfold tailWord_5951621
  simp only [CollatzResearch.WordTrace]
  refine ⟨217073451171301047787718717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144715634114200698525145811 217073451171301047787718717)
  ·
    refine ⟨81402544189237892920394519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217073451171301047787718717 81402544189237892920394519)
    ·
      refine ⟨122103816283856839380591779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81402544189237892920394519 122103816283856839380591779)
      ·
        refine ⟨183155724425785259070887669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122103816283856839380591779 183155724425785259070887669)
        ·
          refine ⟨17170849164917368037895719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183155724425785259070887669 17170849164917368037895719)
          ·
            refine ⟨25756273747376052056843579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17170849164917368037895719 25756273747376052056843579)
            ·
              refine ⟨38634410621064078085265369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25756273747376052056843579 38634410621064078085265369)
              ·
                refine ⟨28975807965798058563949027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38634410621064078085265369 28975807965798058563949027)
                ·
                  refine ⟨43463711948697087845923541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28975807965798058563949027 43463711948697087845923541)
                  ·
                    refine ⟨1018680748797587996388833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43463711948697087845923541 1018680748797587996388833)
                    ·
                      rfl

theorem cell23_5951621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_5951621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951621 prefixEnd_5951621 := by exact prefixLift 5951621
  have htrace : WordTrace (prefixWord ++ tailWord_5951621) baseStart_5951621 baseEnd_5951621 := by
    simpa [prefixWord, tailWord_5951621, baseEnd_5951621] using wordTrace_append hprefix tailTrace_5951621
  have hstable : (prefixWord ++ tailWord_5951621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951621).length < 2 ^ (prefixWord ++ tailWord_5951621).sum := by decide
  have hdescent : baseEnd_5951621 < baseStart_5951621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951641 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_5951641 : Nat := 118140960795 + 5951641 * 2 ^ 59
def prefixEnd_5951641 : Nat := 4983230072969 + 3 ^ 40 * 5951641 * 2
def baseEnd_5951641 : Nat := 3056052516005853910916407

theorem tailTrace_5951641 : CollatzResearch.WordTrace tailWord_5951641 prefixEnd_5951641 3056052516005853910916407 := by
  unfold tailWord_5951641
  simp only [CollatzResearch.WordTrace]
  refine ⟨217074180631228591203446777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144716120420819060802297851 217074180631228591203446777)
  ·
    refine ⟨162805635473421443402585083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217074180631228591203446777 162805635473421443402585083)
    ·
      refine ⟨244208453210132165103877625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162805635473421443402585083 244208453210132165103877625)
      ·
        refine ⟨183156339907599123827908219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244208453210132165103877625 183156339907599123827908219)
        ·
          refine ⟨274734509861398685741862329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183156339907599123827908219 274734509861398685741862329)
          ·
            refine ⟨206050882396049014306396747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274734509861398685741862329 206050882396049014306396747)
            ·
              refine ⟨309076323594073521459595121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206050882396049014306396747 309076323594073521459595121)
              ·
                refine ⟨231807242695555141094696341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309076323594073521459595121 231807242695555141094696341)
                ·
                  refine ⟨10865964501354147238813891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231807242695555141094696341 10865964501354147238813891)
                  ·
                    refine ⟨16298946752031220858220837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10865964501354147238813891 16298946752031220858220837)
                    ·
                      refine ⟨3056052516005853910916407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16298946752031220858220837 3056052516005853910916407)
                      ·
                        rfl

theorem cell23_5951641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_5951641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951641 prefixEnd_5951641 := by exact prefixLift 5951641
  have htrace : WordTrace (prefixWord ++ tailWord_5951641) baseStart_5951641 baseEnd_5951641 := by
    simpa [prefixWord, tailWord_5951641, baseEnd_5951641] using wordTrace_append hprefix tailTrace_5951641
  have hstable : (prefixWord ++ tailWord_5951641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951641).length < 2 ^ (prefixWord ++ tailWord_5951641).sum := by decide
  have hdescent : baseEnd_5951641 < baseStart_5951641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951642 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_5951642 : Nat := 118140960795 + 5951642 * 2 ^ 59
def prefixEnd_5951642 : Nat := 4983230072969 + 3 ^ 40 * 5951642 * 2
def baseEnd_5951642 : Nat := 339561447720723156333767

theorem tailTrace_5951642 : CollatzResearch.WordTrace tailWord_5951642 prefixEnd_5951642 339561447720723156333767 := by
  unfold tailWord_5951642
  simp only [CollatzResearch.WordTrace]
  refine ⟨54268554276056242093558295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144716144736149978916155453 54268554276056242093558295)
  ·
    refine ⟨81402831414084363140337443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54268554276056242093558295 81402831414084363140337443)
    ·
      refine ⟨122104247121126544710506165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81402831414084363140337443 122104247121126544710506165)
      ·
        refine ⟨11447273167605613566609953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122104247121126544710506165 11447273167605613566609953)
        ·
          refine ⟨8585454875704210174957465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11447273167605613566609953 8585454875704210174957465)
          ·
            refine ⟨6439091156778157631218099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8585454875704210174957465 6439091156778157631218099)
            ·
              refine ⟨9658636735167236446827149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439091156778157631218099 9658636735167236446827149)
              ·
                refine ⟨3621988775687713667560181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9658636735167236446827149 3621988775687713667560181)
                ·
                  refine ⟨339561447720723156333767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3621988775687713667560181 339561447720723156333767)
                  ·
                    rfl

theorem cell23_5951642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_5951642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951642 prefixEnd_5951642 := by exact prefixLift 5951642
  have htrace : WordTrace (prefixWord ++ tailWord_5951642) baseStart_5951642 baseEnd_5951642 := by
    simpa [prefixWord, tailWord_5951642, baseEnd_5951642] using wordTrace_append hprefix tailTrace_5951642
  have hstable : (prefixWord ++ tailWord_5951642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951642).length < 2 ^ (prefixWord ++ tailWord_5951642).sum := by decide
  have hdescent : baseEnd_5951642 < baseStart_5951642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951655 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5951655 : Nat := 118140960795 + 5951655 * 2 ^ 59
def prefixEnd_5951655 : Nat := 4983230072969 + 3 ^ 40 * 5951655 * 2
def baseEnd_5951655 : Nat := 1018686568245005618713781

theorem tailTrace_5951655 : CollatzResearch.WordTrace tailWord_5951655 prefixEnd_5951655 1018686568245005618713781 := by
  unfold tailWord_5951655
  simp only [CollatzResearch.WordTrace]
  refine ⟨217074691253177871594456419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144716460835451914396304279 217074691253177871594456419)
  ·
    refine ⟨325612036879766807391684629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217074691253177871594456419 325612036879766807391684629)
    ·
      refine ⟨15263064228739069096485217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 325612036879766807391684629 15263064228739069096485217)
      ·
        refine ⟨11447298171554301822363913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15263064228739069096485217 11447298171554301822363913)
        ·
          refine ⟨8585473628665726366772935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11447298171554301822363913 8585473628665726366772935)
          ·
            refine ⟨12878210442998589550159403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8585473628665726366772935 12878210442998589550159403)
            ·
              refine ⟨19317315664497884325239105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12878210442998589550159403 19317315664497884325239105)
              ·
                refine ⟨14487986748373413243929329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19317315664497884325239105 14487986748373413243929329)
                ·
                  refine ⟨10865990061280059932946997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14487986748373413243929329 10865990061280059932946997)
                  ·
                    refine ⟨1018686568245005618713781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10865990061280059932946997 1018686568245005618713781)
                    ·
                      rfl

theorem cell23_5951655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5951655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951655 prefixEnd_5951655 := by exact prefixLift 5951655
  have htrace : WordTrace (prefixWord ++ tailWord_5951655) baseStart_5951655 baseEnd_5951655 := by
    simpa [prefixWord, tailWord_5951655, baseEnd_5951655] using wordTrace_append hprefix tailTrace_5951655
  have hstable : (prefixWord ++ tailWord_5951655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951655).length < 2 ^ (prefixWord ++ tailWord_5951655).sum := by decide
  have hdescent : baseEnd_5951655 < baseStart_5951655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951692 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5951692 : Nat := 118140960795 + 5951692 * 2 ^ 59
def prefixEnd_5951692 : Nat := 4983230072969 + 3 ^ 40 * 5951692 * 2
def baseEnd_5951692 : Nat := 3056078703519233211378673

theorem tailTrace_5951692 : CollatzResearch.WordTrace tailWord_5951692 prefixEnd_5951692 3056078703519233211378673 := by
  unfold tailWord_5951692
  simp only [CollatzResearch.WordTrace]
  refine ⟨108538020377021913456776665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144717360502695884609035553 108538020377021913456776665)
  ·
    refine ⟨81403515282766435092582499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108538020377021913456776665 81403515282766435092582499)
    ·
      refine ⟨122105272924149652638873749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81403515282766435092582499 122105272924149652638873749)
      ·
        refine ⟨5723684668319514967447207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122105272924149652638873749 5723684668319514967447207)
        ·
          refine ⟨8585527002479272451170811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723684668319514967447207 8585527002479272451170811)
          ·
            refine ⟨12878290503718908676756217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8585527002479272451170811 12878290503718908676756217)
            ·
              refine ⟨9658717877789181507567163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12878290503718908676756217 9658717877789181507567163)
              ·
                refine ⟨14488076816683772261350745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9658717877789181507567163 14488076816683772261350745)
                ·
                  refine ⟨10866057612512829196013059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14488076816683772261350745 10866057612512829196013059)
                  ·
                    refine ⟨16299086418769243794019589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10866057612512829196013059 16299086418769243794019589)
                    ·
                      refine ⟨3056078703519233211378673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16299086418769243794019589 3056078703519233211378673)
                      ·
                        rfl

theorem cell23_5951692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5951692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951692 prefixEnd_5951692 := by exact prefixLift 5951692
  have htrace : WordTrace (prefixWord ++ tailWord_5951692) baseStart_5951692 baseEnd_5951692 := by
    simpa [prefixWord, tailWord_5951692, baseEnd_5951692] using wordTrace_append hprefix tailTrace_5951692
  have hstable : (prefixWord ++ tailWord_5951692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951692).length < 2 ^ (prefixWord ++ tailWord_5951692).sum := by decide
  have hdescent : baseEnd_5951692 < baseStart_5951692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951719 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 1, 4]
def baseStart_5951719 : Nat := 118140960795 + 5951719 * 2 ^ 59
def prefixEnd_5951719 : Nat := 4983230072969 + 3 ^ 40 * 5951719 * 2
def baseEnd_5951719 : Nat := 1018697522498968201913683

theorem tailTrace_5951719 : CollatzResearch.WordTrace tailWord_5951719 prefixEnd_5951719 1018697522498968201913683 := by
  unfold tailWord_5951719
  simp only [CollatzResearch.WordTrace]
  refine ⟨217077025524946010524786211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144718017016630673683190807 217077025524946010524786211)
  ·
    refine ⟨325615538287419015787179317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217077025524946010524786211 325615538287419015787179317)
    ·
      refine ⟨30526456714445532730048061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325615538287419015787179317 30526456714445532730048061)
      ·
        refine ⟨11447421267917074773768023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30526456714445532730048061 11447421267917074773768023)
        ·
          refine ⟨17171131901875612160652035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11447421267917074773768023 17171131901875612160652035)
          ·
            refine ⟨25756697852813418240978053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17171131901875612160652035 25756697852813418240978053)
            ·
              refine ⟨4829380847402515920183385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25756697852813418240978053 4829380847402515920183385)
              ·
                refine ⟨3622035635551886940137539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4829380847402515920183385 3622035635551886940137539)
                ·
                  refine ⟨5433053453327830410206309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622035635551886940137539 5433053453327830410206309)
                  ·
                    refine ⟨1018697522498968201913683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5433053453327830410206309 1018697522498968201913683)
                    ·
                      rfl

theorem cell23_5951719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_5951719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951719 prefixEnd_5951719 := by exact prefixLift 5951719
  have htrace : WordTrace (prefixWord ++ tailWord_5951719) baseStart_5951719 baseEnd_5951719 := by
    simpa [prefixWord, tailWord_5951719, baseEnd_5951719] using wordTrace_append hprefix tailTrace_5951719
  have hstable : (prefixWord ++ tailWord_5951719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951719).length < 2 ^ (prefixWord ++ tailWord_5951719).sum := by decide
  have hdescent : baseEnd_5951719 < baseStart_5951719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951742 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5951742 : Nat := 118140960795 + 5951742 * 2 ^ 59
def prefixEnd_5951742 : Nat := 4983230072969 + 3 ^ 40 * 5951742 * 2
def baseEnd_5951742 : Nat := 3056104377551958015753443

theorem tailTrace_5951742 : CollatzResearch.WordTrace tailWord_5951742 prefixEnd_5951742 3056104377551958015753443 := by
  unfold tailWord_5951742
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134733050482835681609185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144718576269241790301915653 27134733050482835681609185)
  ·
    refine ⟨20351049787862126761206889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27134733050482835681609185 20351049787862126761206889)
    ·
      refine ⟨15263287340896595070905167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20351049787862126761206889 15263287340896595070905167)
      ·
        refine ⟨22894931011344892606357751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15263287340896595070905167 22894931011344892606357751)
        ·
          refine ⟨34342396517017338909536627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22894931011344892606357751 34342396517017338909536627)
          ·
            refine ⟨51513594775526008364304941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34342396517017338909536627 51513594775526008364304941)
            ·
              refine ⟨19317598040822253136614353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51513594775526008364304941 19317598040822253136614353)
              ·
                refine ⟨14488198530616689852460765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19317598040822253136614353 14488198530616689852460765)
                ·
                  refine ⟨5433074448981258694672787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14488198530616689852460765 5433074448981258694672787)
                  ·
                    refine ⟨8149611673471888042009181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433074448981258694672787 8149611673471888042009181)
                    ·
                      refine ⟨3056104377551958015753443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8149611673471888042009181 3056104377551958015753443)
                      ·
                        rfl

theorem cell23_5951742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5951742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951742 prefixEnd_5951742 := by exact prefixLift 5951742
  have htrace : WordTrace (prefixWord ++ tailWord_5951742) baseStart_5951742 baseEnd_5951742 := by
    simpa [prefixWord, tailWord_5951742, baseEnd_5951742] using wordTrace_append hprefix tailTrace_5951742
  have hstable : (prefixWord ++ tailWord_5951742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951742).length < 2 ^ (prefixWord ++ tailWord_5951742).sum := by decide
  have hdescent : baseEnd_5951742 < baseStart_5951742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951752 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_5951752 : Nat := 118140960795 + 5951752 * 2 ^ 59
def prefixEnd_5951752 : Nat := 4983230072969 + 3 ^ 40 * 5951752 * 2
def baseEnd_5951752 : Nat := 3056109512358502976628397

theorem tailTrace_5951752 : CollatzResearch.WordTrace tailWord_5951752 prefixEnd_5951752 3056109512358502976628397 := by
  unfold tailWord_5951752
  simp only [CollatzResearch.WordTrace]
  refine ⟨108539114566913228580368755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144718819422550971440491673 108539114566913228580368755)
  ·
    refine ⟨162808671850369842870553133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108539114566913228580368755 162808671850369842870553133)
    ·
      refine ⟨61053251943888691076457425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162808671850369842870553133 61053251943888691076457425)
      ·
        refine ⟨45789938957916518307343069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61053251943888691076457425 45789938957916518307343069)
        ·
          refine ⟨17171227109218694365253651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45789938957916518307343069 17171227109218694365253651)
          ·
            refine ⟨25756840663828041547880477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17171227109218694365253651 25756840663828041547880477)
            ·
              refine ⟨9658815248935515580455179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25756840663828041547880477 9658815248935515580455179)
              ·
                refine ⟨14488222873403273370682769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9658815248935515580455179 14488222873403273370682769)
                ·
                  refine ⟨10866167155052455028012077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14488222873403273370682769 10866167155052455028012077)
                  ·
                    refine ⟨4074812683144670635504529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10866167155052455028012077 4074812683144670635504529)
                    ·
                      refine ⟨3056109512358502976628397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074812683144670635504529 3056109512358502976628397)
                      ·
                        rfl

theorem cell23_5951752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_5951752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951752 prefixEnd_5951752 := by exact prefixLift 5951752
  have htrace : WordTrace (prefixWord ++ tailWord_5951752) baseStart_5951752 baseEnd_5951752 := by
    simpa [prefixWord, tailWord_5951752, baseEnd_5951752] using wordTrace_append hprefix tailTrace_5951752
  have hstable : (prefixWord ++ tailWord_5951752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951752).length < 2 ^ (prefixWord ++ tailWord_5951752).sum := by decide
  have hdescent : baseEnd_5951752 < baseStart_5951752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951758 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_5951758 : Nat := 118140960795 + 5951758 * 2 ^ 59
def prefixEnd_5951758 : Nat := 4983230072969 + 3 ^ 40 * 5951758 * 2
def baseEnd_5951758 : Nat := 1018704197747476651051123

theorem tailTrace_5951758 : CollatzResearch.WordTrace tailWord_5951758 prefixEnd_5951758 1018704197747476651051123 := by
  unfold tailWord_5951758
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134805996475590023181991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144718965314536480123637285 27134805996475590023181991)
  ·
    refine ⟨40702208994713385034772987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27134805996475590023181991 40702208994713385034772987)
    ·
      refine ⟨61053313492070077552159481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40702208994713385034772987 61053313492070077552159481)
      ·
        refine ⟨45789985119052558164119611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61053313492070077552159481 45789985119052558164119611)
        ·
          refine ⟨68684977678578837246179417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45789985119052558164119611 68684977678578837246179417)
          ·
            refine ⟨51513733258934127934634563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68684977678578837246179417 51513733258934127934634563)
            ·
              refine ⟨77270599888401191901951845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51513733258934127934634563 77270599888401191901951845)
              ·
                refine ⟨14488237479075223481615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77270599888401191901951845 14488237479075223481615971)
                ·
                  refine ⟨21732356218612835222423957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14488237479075223481615971 21732356218612835222423957)
                  ·
                    refine ⟨1018704197747476651051123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21732356218612835222423957 1018704197747476651051123)
                    ·
                      rfl

theorem cell23_5951758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_5951758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951758 prefixEnd_5951758 := by exact prefixLift 5951758
  have htrace : WordTrace (prefixWord ++ tailWord_5951758) baseStart_5951758 baseEnd_5951758 := by
    simpa [prefixWord, tailWord_5951758, baseEnd_5951758] using wordTrace_append hprefix tailTrace_5951758
  have hstable : (prefixWord ++ tailWord_5951758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951758).length < 2 ^ (prefixWord ++ tailWord_5951758).sum := by decide
  have hdescent : baseEnd_5951758 < baseStart_5951758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951768 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_5951768 : Nat := 118140960795 + 5951768 * 2 ^ 59
def prefixEnd_5951768 : Nat := 4983230072969 + 3 ^ 40 * 5951768 * 2
def baseEnd_5951768 : Nat := 3056117728048974914028323

theorem tailTrace_5951768 : CollatzResearch.WordTrace tailWord_5951768 prefixEnd_5951768 3056117728048974914028323 := by
  unfold tailWord_5951768
  simp only [CollatzResearch.WordTrace]
  refine ⟨108539406350884245946659979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144719208467845661262213305 108539406350884245946659979)
  ·
    refine ⟨162809109526326368919989969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108539406350884245946659979 162809109526326368919989969)
    ·
      refine ⟨122106832144744776689992477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162809109526326368919989969 122106832144744776689992477)
      ·
        refine ⟨45790062054279291258747179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122106832144744776689992477 45790062054279291258747179)
        ·
          refine ⟨68685093081418936888120769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45790062054279291258747179 68685093081418936888120769)
          ·
            refine ⟨51513819811064202666090577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68685093081418936888120769 51513819811064202666090577)
            ·
              refine ⟨38635364858298151999567933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51513819811064202666090577 38635364858298151999567933)
              ·
                refine ⟨14488261821861806999837975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38635364858298151999567933 14488261821861806999837975)
                ·
                  refine ⟨21732392732792710499756963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14488261821861806999837975 21732392732792710499756963)
                  ·
                    refine ⟨32598589099189065749635445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21732392732792710499756963 32598589099189065749635445)
                    ·
                      refine ⟨3056117728048974914028323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32598589099189065749635445 3056117728048974914028323)
                      ·
                        rfl

theorem cell23_5951768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_5951768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951768 prefixEnd_5951768 := by exact prefixLift 5951768
  have htrace : WordTrace (prefixWord ++ tailWord_5951768) baseStart_5951768 baseEnd_5951768 := by
    simpa [prefixWord, tailWord_5951768, baseEnd_5951768] using wordTrace_append hprefix tailTrace_5951768
  have hstable : (prefixWord ++ tailWord_5951768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951768).length < 2 ^ (prefixWord ++ tailWord_5951768).sum := by decide
  have hdescent : baseEnd_5951768 < baseStart_5951768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951775 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 4, 4]
def baseStart_5951775 : Nat := 118140960795 + 5951775 * 2 ^ 59
def prefixEnd_5951775 : Nat := 4983230072969 + 3 ^ 40 * 5951775 * 2
def baseEnd_5951775 : Nat := 1018707107471185462213597

theorem tailTrace_5951775 : CollatzResearch.WordTrace tailWord_5951775 prefixEnd_5951775 1018707107471185462213597 := by
  unfold tailWord_5951775
  simp only [CollatzResearch.WordTrace]
  refine ⟨217079068012743132088824779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144719378675162088059216519 217079068012743132088824779)
  ·
    refine ⟨325618602019114698133237169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217079068012743132088824779 325618602019114698133237169)
    ·
      refine ⟨244213951514336023599927877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325618602019114698133237169 244213951514336023599927877)
      ·
        refine ⟨45790115908938004424986477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244213951514336023599927877 45790115908938004424986477)
        ·
          refine ⟨17171293465851751659369929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45790115908938004424986477 17171293465851751659369929)
          ·
            refine ⟨12878470099388813744527447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17171293465851751659369929 12878470099388813744527447)
            ·
              refine ⟨19317705149083220616791171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12878470099388813744527447 19317705149083220616791171)
              ·
                refine ⟨28976557723624830925186757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19317705149083220616791171 28976557723624830925186757)
                ·
                  refine ⟨5433104573179655798472517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28976557723624830925186757 5433104573179655798472517)
                  ·
                    refine ⟨1018707107471185462213597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5433104573179655798472517 1018707107471185462213597)
                    ·
                      rfl

theorem cell23_5951775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_5951775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951775 prefixEnd_5951775 := by exact prefixLift 5951775
  have htrace : WordTrace (prefixWord ++ tailWord_5951775) baseStart_5951775 baseEnd_5951775 := by
    simpa [prefixWord, tailWord_5951775, baseEnd_5951775] using wordTrace_append hprefix tailTrace_5951775
  have hstable : (prefixWord ++ tailWord_5951775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951775).length < 2 ^ (prefixWord ++ tailWord_5951775).sum := by decide
  have hdescent : baseEnd_5951775 < baseStart_5951775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951802 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_5951802 : Nat := 118140960795 + 5951802 * 2 ^ 59
def prefixEnd_5951802 : Nat := 4983230072969 + 3 ^ 40 * 5951802 * 2
def baseEnd_5951802 : Nat := 3056135186391227781003167

theorem tailTrace_5951802 : CollatzResearch.WordTrace tailWord_5951802 prefixEnd_5951802 3056135186391227781003167 := by
  unfold tailWord_5951802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54270013195911328925014415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144720035189096877133371773 54270013195911328925014415)
  ·
    refine ⟨81405019793866993387521623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54270013195911328925014415 81405019793866993387521623)
    ·
      refine ⟨122107529690800490081282435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81405019793866993387521623 122107529690800490081282435)
      ·
        refine ⟨183161294536200735121923653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122107529690800490081282435 183161294536200735121923653)
        ·
          refine ⟨34342742725537637835360685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183161294536200735121923653 34342742725537637835360685)
          ·
            refine ⟨12878528522076614188260257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34342742725537637835360685 12878528522076614188260257)
            ·
              refine ⟨9658896391557460641195193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12878528522076614188260257 9658896391557460641195193)
              ·
                refine ⟨7244172293668095480896395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9658896391557460641195193 7244172293668095480896395)
                ·
                  refine ⟨10866258440502143221344593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244172293668095480896395 10866258440502143221344593)
                  ·
                    refine ⟨8149693830376607416008445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10866258440502143221344593 8149693830376607416008445)
                    ·
                      refine ⟨3056135186391227781003167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8149693830376607416008445 3056135186391227781003167)
                      ·
                        rfl

theorem cell23_5951802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_5951802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951802 prefixEnd_5951802 := by exact prefixLift 5951802
  have htrace : WordTrace (prefixWord ++ tailWord_5951802) baseStart_5951802 baseEnd_5951802 := by
    simpa [prefixWord, tailWord_5951802, baseEnd_5951802] using wordTrace_append hprefix tailTrace_5951802
  have hstable : (prefixWord ++ tailWord_5951802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951802).length < 2 ^ (prefixWord ++ tailWord_5951802).sum := by decide
  have hdescent : baseEnd_5951802 < baseStart_5951802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951815 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_5951815 : Nat := 118140960795 + 5951815 * 2 ^ 59
def prefixEnd_5951815 : Nat := 4983230072969 + 3 ^ 40 * 5951815 * 2
def baseEnd_5951815 : Nat := 3056141861639736230140607

theorem tailTrace_5951815 : CollatzResearch.WordTrace tailWord_5951815 prefixEnd_5951815 3056141861639736230140607 := by
  unfold tailWord_5951815
  simp only [CollatzResearch.WordTrace]
  refine ⟨217080526932598218920280899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144720351288398812613520599 217080526932598218920280899)
  ·
    refine ⟨325620790398897328380421349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217080526932598218920280899 325620790398897328380421349)
    ·
      refine ⟨61053898199793249071329003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325620790398897328380421349 61053898199793249071329003)
      ·
        refine ⟨91580847299689873606993505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61053898199793249071329003 91580847299689873606993505)
        ·
          refine ⟨68685635474767405205245129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91580847299689873606993505 68685635474767405205245129)
          ·
            refine ⟨51514226606075553903933847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68685635474767405205245129 51514226606075553903933847)
            ·
              refine ⟨77271339909113330855900771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51514226606075553903933847 77271339909113330855900771)
              ·
                refine ⟨115907009863669996283851157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77271339909113330855900771 115907009863669996283851157)
                ·
                  refine ⟨5433141087359531075805523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115907009863669996283851157 5433141087359531075805523)
                  ·
                    refine ⟨8149711631039296613708285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433141087359531075805523 8149711631039296613708285)
                    ·
                      refine ⟨3056141861639736230140607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8149711631039296613708285 3056141861639736230140607)
                      ·
                        rfl

theorem cell23_5951815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_5951815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951815 prefixEnd_5951815 := by exact prefixLift 5951815
  have htrace : WordTrace (prefixWord ++ tailWord_5951815) baseStart_5951815 baseEnd_5951815 := by
    simpa [prefixWord, tailWord_5951815, baseEnd_5951815] using wordTrace_append hprefix tailTrace_5951815
  have hstable : (prefixWord ++ tailWord_5951815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951815).length < 2 ^ (prefixWord ++ tailWord_5951815).sum := by decide
  have hdescent : baseEnd_5951815 < baseStart_5951815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951868 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_5951868 : Nat := 118140960795 + 5951868 * 2 ^ 59
def prefixEnd_5951868 : Nat := 4983230072969 + 3 ^ 40 * 5951868 * 2
def baseEnd_5951868 : Nat := 3056169076114424522777863

theorem tailTrace_5951868 : CollatzResearch.WordTrace tailWord_5951868 prefixEnd_5951868 3056169076114424522777863 := by
  unfold tailWord_5951868
  simp only [CollatzResearch.WordTrace]
  refine ⟨108541230000703104485980129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144721640000937472647973505 108541230000703104485980129)
  ·
    refine ⟨81405922500527328364485097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108541230000703104485980129 81405922500527328364485097)
    ·
      refine ⟨61054441875395496273363823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81405922500527328364485097 61054441875395496273363823)
      ·
        refine ⟨91581662813093244410045735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61054441875395496273363823 91581662813093244410045735)
        ·
          refine ⟨137372494219639866615068603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91581662813093244410045735 137372494219639866615068603)
          ·
            refine ⟨206058741329459799922602905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137372494219639866615068603 206058741329459799922602905)
            ·
              refine ⟨154544055997094849941952179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206058741329459799922602905 154544055997094849941952179)
              ·
                refine ⟨231816083995642274912928269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154544055997094849941952179 231816083995642274912928269)
                ·
                  refine ⟨86931031498365853092348101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231816083995642274912928269 86931031498365853092348101)
                  ·
                    refine ⟨16299568405943597454815269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86931031498365853092348101 16299568405943597454815269)
                    ·
                      refine ⟨3056169076114424522777863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16299568405943597454815269 3056169076114424522777863)
                      ·
                        rfl

theorem cell23_5951868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_5951868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951868 prefixEnd_5951868 := by exact prefixLift 5951868
  have htrace : WordTrace (prefixWord ++ tailWord_5951868) baseStart_5951868 baseEnd_5951868 := by
    simpa [prefixWord, tailWord_5951868, baseEnd_5951868] using wordTrace_append hprefix tailTrace_5951868
  have hstable : (prefixWord ++ tailWord_5951868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951868).length < 2 ^ (prefixWord ++ tailWord_5951868).sum := by decide
  have hdescent : baseEnd_5951868 < baseStart_5951868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951902 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5951902 : Nat := 118140960795 + 5951902 * 2 ^ 59
def prefixEnd_5951902 : Nat := 4983230072969 + 3 ^ 40 * 5951902 * 2
def baseEnd_5951902 : Nat := 3056186534456677389752707

theorem tailTrace_5951902 : CollatzResearch.WordTrace tailWord_5951902 prefixEnd_5951902 3056186534456677389752707 := by
  unfold tailWord_5951902
  simp only [CollatzResearch.WordTrace]
  refine ⟨27135462510410379097337245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144722466722188688519131973 27135462510410379097337245)
  ·
    refine ⟨10175798441403892161501467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27135462510410379097337245 10175798441403892161501467)
    ·
      refine ⟨15263697662105838242252201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10175798441403892161501467 15263697662105838242252201)
      ·
        refine ⟨11447773246579378681689151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15263697662105838242252201 11447773246579378681689151)
        ·
          refine ⟨17171659869869068022533727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11447773246579378681689151 17171659869869068022533727)
          ·
            refine ⟨25757489804803602033800591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17171659869869068022533727 25757489804803602033800591)
            ·
              refine ⟨38636234707205403050700887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25757489804803602033800591 38636234707205403050700887)
              ·
                refine ⟨57954352060808104576051331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38636234707205403050700887 57954352060808104576051331)
                ·
                  refine ⟨86931528091212156864076997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57954352060808104576051331 86931528091212156864076997)
                  ·
                    refine ⟨16299661517102279412014437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86931528091212156864076997 16299661517102279412014437)
                    ·
                      refine ⟨3056186534456677389752707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16299661517102279412014437 3056186534456677389752707)
                      ·
                        rfl

theorem cell23_5951902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5951902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951902 prefixEnd_5951902 := by exact prefixLift 5951902
  have htrace : WordTrace (prefixWord ++ tailWord_5951902) baseStart_5951902 baseEnd_5951902 := by
    simpa [prefixWord, tailWord_5951902, baseEnd_5951902] using wordTrace_append hprefix tailTrace_5951902
  have hstable : (prefixWord ++ tailWord_5951902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951902).length < 2 ^ (prefixWord ++ tailWord_5951902).sum := by decide
  have hdescent : baseEnd_5951902 < baseStart_5951902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951912 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 7]
def baseStart_5951912 : Nat := 118140960795 + 5951912 * 2 ^ 59
def prefixEnd_5951912 : Nat := 4983230072969 + 3 ^ 40 * 5951912 * 2
def baseEnd_5951912 : Nat := 339576852140358038958629

theorem tailTrace_5951912 : CollatzResearch.WordTrace tailWord_5951912 prefixEnd_5951912 339576852140358038958629 := by
  unfold tailWord_5951912
  simp only [CollatzResearch.WordTrace]
  refine ⟨108542032406623402243280995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144722709875497869657707993 108542032406623402243280995)
  ·
    refine ⟨162813048609935103364921493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108542032406623402243280995 162813048609935103364921493)
    ·
      refine ⟨7631861653590707970230695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 162813048609935103364921493 7631861653590707970230695)
      ·
        refine ⟨11447792480386061955346043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7631861653590707970230695 11447792480386061955346043)
        ·
          refine ⟨17171688720579092933019065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11447792480386061955346043 17171688720579092933019065)
          ·
            refine ⟨12878766540434319699764299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17171688720579092933019065 12878766540434319699764299)
            ·
              refine ⟨19318149810651479549646449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12878766540434319699764299 19318149810651479549646449)
              ·
                refine ⟨14488612357988609662234837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19318149810651479549646449 14488612357988609662234837)
                ·
                  refine ⟨339576852140358038958629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14488612357988609662234837 339576852140358038958629)
                  ·
                    rfl

theorem cell23_5951912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 7].length) (baseStart_5951912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951912 prefixEnd_5951912 := by exact prefixLift 5951912
  have htrace : WordTrace (prefixWord ++ tailWord_5951912) baseStart_5951912 baseEnd_5951912 := by
    simpa [prefixWord, tailWord_5951912, baseEnd_5951912] using wordTrace_append hprefix tailTrace_5951912
  have hstable : (prefixWord ++ tailWord_5951912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951912).length < 2 ^ (prefixWord ++ tailWord_5951912).sum := by decide
  have hdescent : baseEnd_5951912 < baseStart_5951912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951940 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5951940 : Nat := 118140960795 + 5951940 * 2 ^ 59
def prefixEnd_5951940 : Nat := 4983230072969 + 3 ^ 40 * 5951940 * 2
def baseEnd_5951940 : Nat := 3056206046721548241077533

theorem tailTrace_5951940 : CollatzResearch.WordTrace tailWord_5951940 prefixEnd_5951940 3056206046721548241077533 := by
  unfold tailWord_5951940
  simp only [CollatzResearch.WordTrace]
  refine ⟨108542543028572682634290637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144723390704763576845720849 108542543028572682634290637)
  ·
    refine ⟨40703453635714755987858989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108542543028572682634290637 40703453635714755987858989)
    ·
      refine ⟨15263795113393033495447121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40703453635714755987858989 15263795113393033495447121)
      ·
        refine ⟨11447846335044775121585341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15263795113393033495447121 11447846335044775121585341)
        ·
          refine ⟨4292942375641790670594503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11447846335044775121585341 4292942375641790670594503)
          ·
            refine ⟨6439413563462686005891755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292942375641790670594503 6439413563462686005891755)
            ·
              refine ⟨9659120345194029008837633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439413563462686005891755 9659120345194029008837633)
              ·
                refine ⟨7244340258895521756628225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9659120345194029008837633 7244340258895521756628225)
                ·
                  refine ⟨5433255194171641317471169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7244340258895521756628225 5433255194171641317471169)
                  ·
                    refine ⟨4074941395628730988103377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5433255194171641317471169 4074941395628730988103377)
                    ·
                      refine ⟨3056206046721548241077533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074941395628730988103377 3056206046721548241077533)
                      ·
                        rfl

theorem cell23_5951940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5951940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951940 prefixEnd_5951940 := by exact prefixLift 5951940
  have htrace : WordTrace (prefixWord ++ tailWord_5951940) baseStart_5951940 baseEnd_5951940 := by
    simpa [prefixWord, tailWord_5951940, baseEnd_5951940] using wordTrace_append hprefix tailTrace_5951940
  have hstable : (prefixWord ++ tailWord_5951940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951940).length < 2 ^ (prefixWord ++ tailWord_5951940).sum := by decide
  have hdescent : baseEnd_5951940 < baseStart_5951940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951945 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_5951945 : Nat := 118140960795 + 5951945 * 2 ^ 59
def prefixEnd_5951945 : Nat := 4983230072969 + 3 ^ 40 * 5951945 * 2
def baseEnd_5951945 : Nat := 3056208614124820721515009

theorem tailTrace_5951945 : CollatzResearch.WordTrace tailWord_5951945 prefixEnd_5951945 3056208614124820721515009 := by
  unfold tailWord_5951945
  simp only [CollatzResearch.WordTrace]
  refine ⟨217085268422127251122513289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144723512281418167415008859 217085268422127251122513289)
  ·
    refine ⟨162813951316595438341884967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217085268422127251122513289 162813951316595438341884967)
    ·
      refine ⟨244220926974893157512827451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162813951316595438341884967 244220926974893157512827451)
      ·
        refine ⟨366331390462339736269241177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244220926974893157512827451 366331390462339736269241177)
        ·
          refine ⟨274748542846754802201930883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366331390462339736269241177 274748542846754802201930883)
          ·
            refine ⟨412122814270132203302896325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274748542846754802201930883 412122814270132203302896325)
            ·
              refine ⟨77273027675649788119293061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 412122814270132203302896325 77273027675649788119293061)
              ·
                refine ⟨14488692689184335272367449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77273027675649788119293061 14488692689184335272367449)
                ·
                  refine ⟨10866519516888251454275587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14488692689184335272367449 10866519516888251454275587)
                  ·
                    refine ⟨16299779275332377181413381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10866519516888251454275587 16299779275332377181413381)
                    ·
                      refine ⟨3056208614124820721515009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16299779275332377181413381 3056208614124820721515009)
                      ·
                        rfl

theorem cell23_5951945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_5951945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951945 prefixEnd_5951945 := by exact prefixLift 5951945
  have htrace : WordTrace (prefixWord ++ tailWord_5951945) baseStart_5951945 baseEnd_5951945 := by
    simpa [prefixWord, tailWord_5951945, baseEnd_5951945] using wordTrace_append hprefix tailTrace_5951945
  have hstable : (prefixWord ++ tailWord_5951945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951945).length < 2 ^ (prefixWord ++ tailWord_5951945).sum := by decide
  have hdescent : baseEnd_5951945 < baseStart_5951945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951962 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2]
def baseStart_5951962 : Nat := 118140960795 + 5951962 * 2 ^ 59
def prefixEnd_5951962 : Nat := 4983230072969 + 3 ^ 40 * 5951962 * 2
def baseEnd_5951962 : Nat := 3056217343295947155002431

theorem tailTrace_5951962 : CollatzResearch.WordTrace tailWord_5951962 prefixEnd_5951962 3056217343295947155002431 := by
  unfold tailWord_5951962
  simp only [CollatzResearch.WordTrace]
  refine ⟨54271472115766415756470535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144723925642043775350588093 54271472115766415756470535)
  ·
    refine ⟨81407208173649623634705803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54271472115766415756470535 81407208173649623634705803)
    ·
      refine ⟨122110812260474435452058705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81407208173649623634705803 122110812260474435452058705)
      ·
        refine ⟨91583109195355826589044029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122110812260474435452058705 91583109195355826589044029)
        ·
          refine ⟨34343665948258434970891511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91583109195355826589044029 34343665948258434970891511)
          ·
            refine ⟨51515498922387652456337267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34343665948258434970891511 51515498922387652456337267)
            ·
              refine ⟨77273248383581478684505901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51515498922387652456337267 77273248383581478684505901)
              ·
                refine ⟨28977468143843054506689713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77273248383581478684505901 28977468143843054506689713)
                ·
                  refine ⟨21733101107882290880017285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28977468143843054506689713 21733101107882290880017285)
                  ·
                    refine ⟨4074956457727929540003241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21733101107882290880017285 4074956457727929540003241)
                    ·
                      refine ⟨3056217343295947155002431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4074956457727929540003241 3056217343295947155002431)
                      ·
                        rfl

theorem cell23_5951962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_5951962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951962 prefixEnd_5951962 := by exact prefixLift 5951962
  have htrace : WordTrace (prefixWord ++ tailWord_5951962) baseStart_5951962 baseEnd_5951962 := by
    simpa [prefixWord, tailWord_5951962, baseEnd_5951962] using wordTrace_append hprefix tailTrace_5951962
  have hstable : (prefixWord ++ tailWord_5951962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951962).length < 2 ^ (prefixWord ++ tailWord_5951962).sum := by decide
  have hdescent : baseEnd_5951962 < baseStart_5951962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951975 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5951975 : Nat := 118140960795 + 5951975 * 2 ^ 59
def prefixEnd_5951975 : Nat := 4983230072969 + 3 ^ 40 * 5951975 * 2
def baseEnd_5951975 : Nat := 3056224018544455604139871

theorem tailTrace_5951975 : CollatzResearch.WordTrace tailWord_5951975 prefixEnd_5951975 3056224018544455604139871 := by
  unfold tailWord_5951975
  simp only [CollatzResearch.WordTrace]
  refine ⟨217086362612018566246105379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144724241741345710830736919 217086362612018566246105379)
  ·
    refine ⟨325629543918027849369158069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217086362612018566246105379 325629543918027849369158069)
    ·
      refine ⟨30527769742315110878358569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325629543918027849369158069 30527769742315110878358569)
      ·
        refine ⟨22895827306736333158768927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30527769742315110878358569 22895827306736333158768927)
        ·
          refine ⟨34343740960104499738153391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22895827306736333158768927 34343740960104499738153391)
          ·
            refine ⟨51515611440156749607230087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34343740960104499738153391 51515611440156749607230087)
            ·
              refine ⟨77273417160235124410845131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51515611440156749607230087 77273417160235124410845131)
              ·
                refine ⟨115910125740352686616267697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77273417160235124410845131 115910125740352686616267697)
                ·
                  refine ⟨86932594305264514962200773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115910125740352686616267697 86932594305264514962200773)
                  ·
                    refine ⟨16299861432237096555412645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86932594305264514962200773 16299861432237096555412645)
                    ·
                      refine ⟨3056224018544455604139871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16299861432237096555412645 3056224018544455604139871)
                      ·
                        rfl

theorem cell23_5951975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5951975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951975 prefixEnd_5951975 := by exact prefixLift 5951975
  have htrace : WordTrace (prefixWord ++ tailWord_5951975) baseStart_5951975 baseEnd_5951975 := by
    simpa [prefixWord, tailWord_5951975, baseEnd_5951975] using wordTrace_append hprefix tailTrace_5951975
  have hstable : (prefixWord ++ tailWord_5951975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951975).length < 2 ^ (prefixWord ++ tailWord_5951975).sum := by decide
  have hdescent : baseEnd_5951975 < baseStart_5951975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5951982 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_5951982 : Nat := 118140960795 + 5951982 * 2 ^ 59
def prefixEnd_5951982 : Nat := 4983230072969 + 3 ^ 40 * 5951982 * 2
def baseEnd_5951982 : Nat := 3056227612909037076752339

theorem tailTrace_5951982 : CollatzResearch.WordTrace tailWord_5951982 prefixEnd_5951982 3056227612909037076752339 := by
  unfold tailWord_5951982
  simp only [CollatzResearch.WordTrace]
  refine ⟨27135827240374150805201275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144724411948662137627740133 27135827240374150805201275)
  ·
    refine ⟨40703740860561226207801913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27135827240374150805201275 40703740860561226207801913)
    ·
      refine ⟨30527805645420919655851435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40703740860561226207801913 30527805645420919655851435)
      ·
        refine ⟨45791708468131379483777153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30527805645420919655851435 45791708468131379483777153)
        ·
          refine ⟨34343781351098534612832865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45791708468131379483777153 34343781351098534612832865)
          ·
            refine ⟨25757836013323900959624649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34343781351098534612832865 25757836013323900959624649)
            ·
              refine ⟨19318377009992925719718487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25757836013323900959624649 19318377009992925719718487)
              ·
                refine ⟨28977565514989388579577731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19318377009992925719718487 28977565514989388579577731)
                ·
                  refine ⟨43466348272484082869366597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28977565514989388579577731 43466348272484082869366597)
                  ·
                    refine ⟨8149940301090765538006237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43466348272484082869366597 8149940301090765538006237)
                    ·
                      refine ⟨3056227612909037076752339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8149940301090765538006237 3056227612909037076752339)
                      ·
                        rfl

theorem cell23_5951982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_5951982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5951982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5951982 prefixEnd_5951982 := by exact prefixLift 5951982
  have htrace : WordTrace (prefixWord ++ tailWord_5951982) baseStart_5951982 baseEnd_5951982 := by
    simpa [prefixWord, tailWord_5951982, baseEnd_5951982] using wordTrace_append hprefix tailTrace_5951982
  have hstable : (prefixWord ++ tailWord_5951982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5951982).length < 2 ^ (prefixWord ++ tailWord_5951982).sum := by decide
  have hdescent : baseEnd_5951982 < baseStart_5951982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5951982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952075 : List Nat := [1, 1, 1, 1, 3, 1, 7, 8]
def baseStart_5952075 : Nat := 118140960795 + 5952075 * 2 ^ 59
def prefixEnd_5952075 : Nat := 4983230072969 + 3 ^ 40 * 5952075 * 2
def baseEnd_5952075 : Nat := 113195383948515007884793

theorem tailTrace_5952075 : CollatzResearch.WordTrace tailWord_5952075 prefixEnd_5952075 113195383948515007884793 := by
  unfold tailWord_5952075
  simp only [CollatzResearch.WordTrace]
  refine ⟨217090009911656283324745679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144726673274437522216497119 217090009911656283324745679)
  ·
    refine ⟨325635014867484424987118519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217090009911656283324745679 325635014867484424987118519)
    ·
      refine ⟨488452522301226637480677779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325635014867484424987118519 488452522301226637480677779)
      ·
        refine ⟨732678783451839956221016669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488452522301226637480677779 732678783451839956221016669)
        ·
          refine ⟨274754543794439983582881251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732678783451839956221016669 274754543794439983582881251)
          ·
            refine ⟨412131815691659975374321877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274754543794439983582881251 412131815691659975374321877)
            ·
              refine ⟨9659339430273280672835669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 412131815691659975374321877 9659339430273280672835669)
              ·
                refine ⟨113195383948515007884793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9659339430273280672835669 113195383948515007884793)
                ·
                  rfl

theorem cell23_5952075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 8].length) (baseStart_5952075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952075 prefixEnd_5952075 := by exact prefixLift 5952075
  have htrace : WordTrace (prefixWord ++ tailWord_5952075) baseStart_5952075 baseEnd_5952075 := by
    simpa [prefixWord, tailWord_5952075, baseEnd_5952075] using wordTrace_append hprefix tailTrace_5952075
  have hstable : (prefixWord ++ tailWord_5952075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952075).length < 2 ^ (prefixWord ++ tailWord_5952075).sum := by decide
  have hdescent : baseEnd_5952075 < baseStart_5952075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952115 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_5952115 : Nat := 118140960795 + 5952115 * 2 ^ 59
def prefixEnd_5952115 : Nat := 4983230072969 + 3 ^ 40 * 5952115 * 2
def baseEnd_5952115 : Nat := 3056295905836085056389227

theorem tailTrace_5952115 : CollatzResearch.WordTrace tailWord_5952115 prefixEnd_5952115 3056295905836085056389227 := by
  unfold tailWord_5952115
  simp only [CollatzResearch.WordTrace]
  refine ⟨217091468831511370156201799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144727645887674246770801199 217091468831511370156201799)
  ·
    refine ⟨325637203247267055234302699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217091468831511370156201799 325637203247267055234302699)
    ·
      refine ⟨488455804870900582851454049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325637203247267055234302699 488455804870900582851454049)
      ·
        refine ⟨366341853653175437138590537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488455804870900582851454049 366341853653175437138590537)
        ·
          refine ⟨274756390239881577853942903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366341853653175437138590537 274756390239881577853942903)
          ·
            refine ⟨412134585359822366780914355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274756390239881577853942903 412134585359822366780914355)
            ·
              refine ⟨618201878039733550171371533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412134585359822366780914355 618201878039733550171371533)
              ·
                refine ⟨231825704264900081314264325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618201878039733550171371533 231825704264900081314264325)
                ·
                  refine ⟨43467319549668765246424561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231825704264900081314264325 43467319549668765246424561)
                  ·
                    refine ⟨32600489662251573934818421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43467319549668765246424561 32600489662251573934818421)
                    ·
                      refine ⟨3056295905836085056389227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32600489662251573934818421 3056295905836085056389227)
                      ·
                        rfl

theorem cell23_5952115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_5952115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952115 prefixEnd_5952115 := by exact prefixLift 5952115
  have htrace : WordTrace (prefixWord ++ tailWord_5952115) baseStart_5952115 baseEnd_5952115 := by
    simpa [prefixWord, tailWord_5952115, baseEnd_5952115] using wordTrace_append hprefix tailTrace_5952115
  have hstable : (prefixWord ++ tailWord_5952115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952115).length < 2 ^ (prefixWord ++ tailWord_5952115).sum := by decide
  have hdescent : baseEnd_5952115 < baseStart_5952115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952130 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5952130 : Nat := 118140960795 + 5952130 * 2 ^ 59
def prefixEnd_5952130 : Nat := 4983230072969 + 3 ^ 40 * 5952130 * 2
def baseEnd_5952130 : Nat := 1018767869348634165900553

theorem tailTrace_5952130 : CollatzResearch.WordTrace tailWord_5952130 prefixEnd_5952130 1018767869348634165900553 := by
  unfold tailWord_5952130
  simp only [CollatzResearch.WordTrace]
  refine ⟨54273003981614256929499461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144728010617638018478665229 54273003981614256929499461)
  ·
    refine ⟨10176188246552673174281149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54273003981614256929499461 10176188246552673174281149)
    ·
      refine ⟨3816070592457252440355431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10176188246552673174281149 3816070592457252440355431)
      ·
        refine ⟨5724105888685878660533147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3816070592457252440355431 5724105888685878660533147)
        ·
          refine ⟨8586158833028817990799721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5724105888685878660533147 8586158833028817990799721)
          ·
            refine ⟨6439619124771613493099791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8586158833028817990799721 6439619124771613493099791)
            ·
              refine ⟨9659428687157420239649687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439619124771613493099791 9659428687157420239649687)
              ·
                refine ⟨14489143030736130359474531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9659428687157420239649687 14489143030736130359474531)
                ·
                  refine ⟨21733714546104195539211797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14489143030736130359474531 21733714546104195539211797)
                  ·
                    refine ⟨1018767869348634165900553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21733714546104195539211797 1018767869348634165900553)
                    ·
                      rfl

theorem cell23_5952130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5952130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952130 prefixEnd_5952130 := by exact prefixLift 5952130
  have htrace : WordTrace (prefixWord ++ tailWord_5952130) baseStart_5952130 baseEnd_5952130 := by
    simpa [prefixWord, tailWord_5952130, baseEnd_5952130] using wordTrace_append hprefix tailTrace_5952130
  have hstable : (prefixWord ++ tailWord_5952130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952130).length < 2 ^ (prefixWord ++ tailWord_5952130).sum := by decide
  have hdescent : baseEnd_5952130 < baseStart_5952130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952154 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5952154 : Nat := 118140960795 + 5952154 * 2 ^ 59
def prefixEnd_5952154 : Nat := 4983230072969 + 3 ^ 40 * 5952154 * 2
def baseEnd_5952154 : Nat := 3056315931581610403801549

theorem tailTrace_5952154 : CollatzResearch.WordTrace tailWord_5952154 prefixEnd_5952154 3056315931581610403801549 := by
  unfold tailWord_5952154
  simp only [CollatzResearch.WordTrace]
  refine ⟨54273222819592519954217879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144728594185580053211247677 54273222819592519954217879)
  ·
    refine ⟨81409834229388779931326819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54273222819592519954217879 81409834229388779931326819)
    ·
      refine ⟨122114751344083169896990229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81409834229388779931326819 122114751344083169896990229)
      ·
        refine ⟨5724128969253898588921417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122114751344083169896990229 5724128969253898588921417)
        ·
          refine ⟨4293096726940423941691063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5724128969253898588921417 4293096726940423941691063)
          ·
            refine ⟨6439645090410635912536595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293096726940423941691063 6439645090410635912536595)
            ·
              refine ⟨9659467635615953868804893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439645090410635912536595 9659467635615953868804893)
              ·
                refine ⟨3622300363355982700801835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9659467635615953868804893 3622300363355982700801835)
                ·
                  refine ⟨5433450545033974051202753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622300363355982700801835 5433450545033974051202753)
                  ·
                    refine ⟨4075087908775480538402065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5433450545033974051202753 4075087908775480538402065)
                    ·
                      refine ⟨3056315931581610403801549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4075087908775480538402065 3056315931581610403801549)
                      ·
                        rfl

theorem cell23_5952154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5952154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952154 prefixEnd_5952154 := by exact prefixLift 5952154
  have htrace : WordTrace (prefixWord ++ tailWord_5952154) baseStart_5952154 baseEnd_5952154 := by
    simpa [prefixWord, tailWord_5952154, baseEnd_5952154] using wordTrace_append hprefix tailTrace_5952154
  have hstable : (prefixWord ++ tailWord_5952154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952154).length < 2 ^ (prefixWord ++ tailWord_5952154).sum := by decide
  have hdescent : baseEnd_5952154 < baseStart_5952154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952155 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_5952155 : Nat := 118140960795 + 5952155 * 2 ^ 59
def prefixEnd_5952155 : Nat := 4983230072969 + 3 ^ 40 * 5952155 * 2
def baseEnd_5952155 : Nat := 3056316445062264899889043

theorem tailTrace_5952155 : CollatzResearch.WordTrace tailWord_5952155 prefixEnd_5952155 3056316445062264899889043 := by
  unfold tailWord_5952155
  simp only [CollatzResearch.WordTrace]
  refine ⟨217092927751366456987657919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144728618500910971325105279 217092927751366456987657919)
  ·
    refine ⟨325639391627049685481486879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217092927751366456987657919 325639391627049685481486879)
    ·
      refine ⟨488459087440574528222230319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325639391627049685481486879 488459087440574528222230319)
      ·
        refine ⟨732688631160861792333345479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488459087440574528222230319 732688631160861792333345479)
        ·
          refine ⟨1099032946741292688500018219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732688631160861792333345479 1099032946741292688500018219)
          ·
            refine ⟨1648549420111939032750027329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099032946741292688500018219 1648549420111939032750027329)
            ·
              refine ⟨1236412065083954274562520497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648549420111939032750027329 1236412065083954274562520497)
              ·
                refine ⟨927309048812965705921890373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236412065083954274562520497 927309048812965705921890373)
                ·
                  refine ⟨173870446652431069860354445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927309048812965705921890373 173870446652431069860354445)
                  ·
                    refine ⟨65201417494661651197632917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173870446652431069860354445 65201417494661651197632917)
                    ·
                      refine ⟨3056316445062264899889043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65201417494661651197632917 3056316445062264899889043)
                      ·
                        rfl

theorem cell23_5952155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_5952155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952155 prefixEnd_5952155 := by exact prefixLift 5952155
  have htrace : WordTrace (prefixWord ++ tailWord_5952155) baseStart_5952155 baseEnd_5952155 := by
    simpa [prefixWord, tailWord_5952155, baseEnd_5952155] using wordTrace_append hprefix tailTrace_5952155
  have hstable : (prefixWord ++ tailWord_5952155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952155).length < 2 ^ (prefixWord ++ tailWord_5952155).sum := by decide
  have hdescent : baseEnd_5952155 < baseStart_5952155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952176 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 2, 2, 2]
def baseStart_5952176 : Nat := 118140960795 + 5952176 * 2 ^ 59
def prefixEnd_5952176 : Nat := 4983230072969 + 3 ^ 40 * 5952176 * 2
def baseEnd_5952176 : Nat := 3056327228156009317726447

theorem tailTrace_5952176 : CollatzResearch.WordTrace tailWord_5952176 prefixEnd_5952176 3056327228156009317726447 := by
  unfold tailWord_5952176
  simp only [CollatzResearch.WordTrace]
  refine ⟨108546846842145188787086191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144729129122860251716114921 108546846842145188787086191)
  ·
    refine ⟨162820270263217783180629287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108546846842145188787086191 162820270263217783180629287)
    ·
      refine ⟨244230405394826674770943931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162820270263217783180629287 244230405394826674770943931)
      ·
        refine ⟨366345608092240012156415897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244230405394826674770943931 366345608092240012156415897)
        ·
          refine ⟨274759206069180009117311923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366345608092240012156415897 274759206069180009117311923)
          ·
            refine ⟨412138809103770013675967885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274759206069180009117311923 412138809103770013675967885)
            ·
              refine ⟨154552053413913755128487957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412138809103770013675967885 154552053413913755128487957)
              ·
                refine ⟨7244627503777207271647873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154552053413913755128487957 7244627503777207271647873)
                ·
                  refine ⟨5433470627832905453735905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7244627503777207271647873 5433470627832905453735905)
                  ·
                    refine ⟨4075102970874679090301929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5433470627832905453735905 4075102970874679090301929)
                    ·
                      refine ⟨3056327228156009317726447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4075102970874679090301929 3056327228156009317726447)
                      ·
                        rfl

theorem cell23_5952176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 2, 2].length) (baseStart_5952176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952176 prefixEnd_5952176 := by exact prefixLift 5952176
  have htrace : WordTrace (prefixWord ++ tailWord_5952176) baseStart_5952176 baseEnd_5952176 := by
    simpa [prefixWord, tailWord_5952176, baseEnd_5952176] using wordTrace_append hprefix tailTrace_5952176
  have hstable : (prefixWord ++ tailWord_5952176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952176).length < 2 ^ (prefixWord ++ tailWord_5952176).sum := by decide
  have hdescent : baseEnd_5952176 < baseStart_5952176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952229 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_5952229 : Nat := 118140960795 + 5952229 * 2 ^ 59
def prefixEnd_5952229 : Nat := 4983230072969 + 3 ^ 40 * 5952229 * 2
def baseEnd_5952229 : Nat := 1018784814210232536787901

theorem tailTrace_5952229 : CollatzResearch.WordTrace tailWord_5952229 prefixEnd_5952229 1018784814210232536787901 := by
  unfold tailWord_5952229
  simp only [CollatzResearch.WordTrace]
  refine ⟨217095626753098367625851741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144730417835398911750567827 217095626753098367625851741)
  ·
    refine ⟨81410860032411887859694403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217095626753098367625851741 81410860032411887859694403)
    ·
      refine ⟨122116290048617831789541605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81410860032411887859694403 122116290048617831789541605)
      ·
        refine ⟨22896804384115843460539051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122116290048617831789541605 22896804384115843460539051)
        ·
          refine ⟨34345206576173765190808577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22896804384115843460539051 34345206576173765190808577)
          ·
            refine ⟨25758904932130323893106433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34345206576173765190808577 25758904932130323893106433)
            ·
              refine ⟨19319178699097742919829825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25758904932130323893106433 19319178699097742919829825)
              ·
                refine ⟨14489384024323307189872369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19319178699097742919829825 14489384024323307189872369)
                ·
                  refine ⟨10867038018242480392404277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14489384024323307189872369 10867038018242480392404277)
                  ·
                    refine ⟨1018784814210232536787901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10867038018242480392404277 1018784814210232536787901)
                    ·
                      rfl

theorem cell23_5952229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_5952229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952229 prefixEnd_5952229 := by exact prefixLift 5952229
  have htrace : WordTrace (prefixWord ++ tailWord_5952229) baseStart_5952229 baseEnd_5952229 := by
    simpa [prefixWord, tailWord_5952229, baseEnd_5952229] using wordTrace_append hprefix tailTrace_5952229
  have hstable : (prefixWord ++ tailWord_5952229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952229).length < 2 ^ (prefixWord ++ tailWord_5952229).sum := by decide
  have hdescent : baseEnd_5952229 < baseStart_5952229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952306 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_5952306 : Nat := 118140960795 + 5952306 * 2 ^ 59
def prefixEnd_5952306 : Nat := 4983230072969 + 3 ^ 40 * 5952306 * 2
def baseEnd_5952306 : Nat := 339599331182343756566761

theorem tailTrace_5952306 : CollatzResearch.WordTrace tailWord_5952306 prefixEnd_5952306 339599331182343756566761 := by
  unfold tailWord_5952306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54274608793454852444101193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144732290115879606517603181 54274608793454852444101193)
  ·
    refine ⟨40705956595091139333075895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54274608793454852444101193 40705956595091139333075895)
    ·
      refine ⟨61058934892636708999613843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40705956595091139333075895 61058934892636708999613843)
      ·
        refine ⟨91588402338955063499420765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61058934892636708999613843 91588402338955063499420765)
        ·
          refine ⟨34345650877108148812282787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91588402338955063499420765 34345650877108148812282787)
          ·
            refine ⟨51518476315662223218424181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34345650877108148812282787 51518476315662223218424181)
            ·
              refine ⟨4829857154593333426727267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51518476315662223218424181 4829857154593333426727267)
              ·
                refine ⟨7244785731890000140090901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829857154593333426727267 7244785731890000140090901)
                ·
                  refine ⟨339599331182343756566761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7244785731890000140090901 339599331182343756566761)
                  ·
                    rfl

theorem cell23_5952306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_5952306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952306 prefixEnd_5952306 := by exact prefixLift 5952306
  have htrace : WordTrace (prefixWord ++ tailWord_5952306) baseStart_5952306 baseEnd_5952306 := by
    simpa [prefixWord, tailWord_5952306, baseEnd_5952306] using wordTrace_append hprefix tailTrace_5952306
  have hstable : (prefixWord ++ tailWord_5952306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952306).length < 2 ^ (prefixWord ++ tailWord_5952306).sum := by decide
  have hdescent : baseEnd_5952306 < baseStart_5952306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952343 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 2, 3, 2]
def baseStart_5952343 : Nat := 118140960795 + 5952343 * 2 ^ 59
def prefixEnd_5952343 : Nat := 4983230072969 + 3 ^ 40 * 5952343 * 2
def baseEnd_5952343 : Nat := 3056412979425310164338179

theorem tailTrace_5952343 : CollatzResearch.WordTrace tailWord_5952343 prefixEnd_5952343 3056412979425310164338179 := by
  unfold tailWord_5952343
  simp only [CollatzResearch.WordTrace]
  refine ⟨217099784674685365095501683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144733189783123576730334455 217099784674685365095501683)
  ·
    refine ⟨325649677012028047643252525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217099784674685365095501683 325649677012028047643252525)
    ·
      refine ⟨122118628879510517866219697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325649677012028047643252525 122118628879510517866219697)
      ·
        refine ⟨91588971659632888399664773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122118628879510517866219697 91588971659632888399664773)
        ·
          refine ⟨17172932186181166574937145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91588971659632888399664773 17172932186181166574937145)
          ·
            refine ⟨12879699139635874931202859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17172932186181166574937145 12879699139635874931202859)
            ·
              refine ⟨19319548709453812396804289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12879699139635874931202859 19319548709453812396804289)
              ·
                refine ⟨14489661532090359297603217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19319548709453812396804289 14489661532090359297603217)
                ·
                  refine ⟨10867246149067769473202413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14489661532090359297603217 10867246149067769473202413)
                  ·
                    refine ⟨4075217305900413552450905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10867246149067769473202413 4075217305900413552450905)
                    ·
                      refine ⟨3056412979425310164338179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4075217305900413552450905 3056412979425310164338179)
                      ·
                        rfl

theorem cell23_5952343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_5952343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952343 prefixEnd_5952343 := by exact prefixLift 5952343
  have htrace : WordTrace (prefixWord ++ tailWord_5952343) baseStart_5952343 baseEnd_5952343 := by
    simpa [prefixWord, tailWord_5952343, baseEnd_5952343] using wordTrace_append hprefix tailTrace_5952343
  have hstable : (prefixWord ++ tailWord_5952343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952343).length < 2 ^ (prefixWord ++ tailWord_5952343).sum := by decide
  have hdescent : baseEnd_5952343 < baseStart_5952343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952369 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_5952369 : Nat := 118140960795 + 5952369 * 2 ^ 59
def prefixEnd_5952369 : Nat := 4983230072969 + 3 ^ 40 * 5952369 * 2
def baseEnd_5952369 : Nat := 3056426329922327062613059

theorem tailTrace_5952369 : CollatzResearch.WordTrace tailWord_5952369 prefixEnd_5952369 3056426329922327062613059 := by
  unfold tailWord_5952369
  simp only [CollatzResearch.WordTrace]
  refine ⟨217100732972591171535948161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144733821981727447690632107 217100732972591171535948161)
  ·
    refine ⟨162825549729443378651961121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217100732972591171535948161 162825549729443378651961121)
    ·
      refine ⟨122119162297082533988970841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162825549729443378651961121 122119162297082533988970841)
      ·
        refine ⟨91589371722811900491728131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122119162297082533988970841 91589371722811900491728131)
        ·
          refine ⟨137384057584217850737592197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91589371722811900491728131 137384057584217850737592197)
          ·
            refine ⟨25759510797040847013298537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137384057584217850737592197 25759510797040847013298537)
            ·
              refine ⟨19319633097780635259973903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25759510797040847013298537 19319633097780635259973903)
              ·
                refine ⟨28979449646670952889960855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19319633097780635259973903 28979449646670952889960855)
                ·
                  refine ⟨43469174470006429334941283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28979449646670952889960855 43469174470006429334941283)
                  ·
                    refine ⟨65203761705009644002411925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43469174470006429334941283 65203761705009644002411925)
                    ·
                      refine ⟨3056426329922327062613059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65203761705009644002411925 3056426329922327062613059)
                      ·
                        rfl

theorem cell23_5952369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_5952369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952369 prefixEnd_5952369 := by exact prefixLift 5952369
  have htrace : WordTrace (prefixWord ++ tailWord_5952369) baseStart_5952369 baseEnd_5952369 := by
    simpa [prefixWord, tailWord_5952369, baseEnd_5952369] using wordTrace_append hprefix tailTrace_5952369
  have hstable : (prefixWord ++ tailWord_5952369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952369).length < 2 ^ (prefixWord ++ tailWord_5952369).sum := by decide
  have hdescent : baseEnd_5952369 < baseStart_5952369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952373 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_5952373 : Nat := 118140960795 + 5952373 * 2 ^ 59
def prefixEnd_5952373 : Nat := 4983230072969 + 3 ^ 40 * 5952373 * 2
def baseEnd_5952373 : Nat := 3056428383844945046963041

theorem tailTrace_5952373 : CollatzResearch.WordTrace tailWord_5952373 prefixEnd_5952373 3056428383844945046963041 := by
  unfold tailWord_5952373
  simp only [CollatzResearch.WordTrace]
  refine ⟨217100878864576680219093773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144733919243051120146062515 217100878864576680219093773)
  ·
    refine ⟨81412829574216255082160165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217100878864576680219093773 81412829574216255082160165)
    ·
      refine ⟨15264905545165547827905031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81412829574216255082160165 15264905545165547827905031)
      ·
        refine ⟨22897358317748321741857547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15264905545165547827905031 22897358317748321741857547)
        ·
          refine ⟨34346037476622482612786321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22897358317748321741857547 34346037476622482612786321)
          ·
            refine ⟨25759528107466861959589741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34346037476622482612786321 25759528107466861959589741)
            ·
              refine ⟨9659823040300073234846153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25759528107466861959589741 9659823040300073234846153)
              ·
                refine ⟨7244867280225054926134615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9659823040300073234846153 7244867280225054926134615)
                ·
                  refine ⟨10867300920337582389201923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244867280225054926134615 10867300920337582389201923)
                  ·
                    refine ⟨16300951380506373583802885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10867300920337582389201923 16300951380506373583802885)
                    ·
                      refine ⟨3056428383844945046963041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16300951380506373583802885 3056428383844945046963041)
                      ·
                        rfl

theorem cell23_5952373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_5952373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952373 prefixEnd_5952373 := by exact prefixLift 5952373
  have htrace : WordTrace (prefixWord ++ tailWord_5952373) baseStart_5952373 baseEnd_5952373 := by
    simpa [prefixWord, tailWord_5952373, baseEnd_5952373] using wordTrace_append hprefix tailTrace_5952373
  have hstable : (prefixWord ++ tailWord_5952373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952373).length < 2 ^ (prefixWord ++ tailWord_5952373).sum := by decide
  have hdescent : baseEnd_5952373 < baseStart_5952373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952376 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_5952376 : Nat := 118140960795 + 5952376 * 2 ^ 59
def prefixEnd_5952376 : Nat := 4983230072969 + 3 ^ 40 * 5952376 * 2
def baseEnd_5952376 : Nat := 3056429924286908535225527

theorem tailTrace_5952376 : CollatzResearch.WordTrace tailWord_5952376 prefixEnd_5952376 3056429924286908535225527 := by
  unfold tailWord_5952376
  simp only [CollatzResearch.WordTrace]
  refine ⟨108550494141782905865726491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144733992189043874487635321 108550494141782905865726491)
  ·
    refine ⟨162825741212674358798589737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108550494141782905865726491 162825741212674358798589737)
    ·
      refine ⟨122119305909505769098942303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162825741212674358798589737 122119305909505769098942303)
      ·
        refine ⟨183178958864258653648413455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122119305909505769098942303 183178958864258653648413455)
        ·
          refine ⟨274768438296387980472620183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183178958864258653648413455 274768438296387980472620183)
          ·
            refine ⟨412152657444581970708930275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274768438296387980472620183 412152657444581970708930275)
            ·
              refine ⟨618228986166872956063395413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412152657444581970708930275 618228986166872956063395413)
              ·
                refine ⟨7244870931643042453867915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 618228986166872956063395413 7244870931643042453867915)
                ·
                  refine ⟨10867306397464563680801873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244870931643042453867915 10867306397464563680801873)
                  ·
                    refine ⟨8150479798098422760601405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10867306397464563680801873 8150479798098422760601405)
                    ·
                      refine ⟨3056429924286908535225527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8150479798098422760601405 3056429924286908535225527)
                      ·
                        rfl

theorem cell23_5952376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_5952376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952376 prefixEnd_5952376 := by exact prefixLift 5952376
  have htrace : WordTrace (prefixWord ++ tailWord_5952376) baseStart_5952376 baseEnd_5952376 := by
    simpa [prefixWord, tailWord_5952376, baseEnd_5952376] using wordTrace_append hprefix tailTrace_5952376
  have hstable : (prefixWord ++ tailWord_5952376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952376).length < 2 ^ (prefixWord ++ tailWord_5952376).sum := by decide
  have hdescent : baseEnd_5952376 < baseStart_5952376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952520 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 5]
def baseStart_5952520 : Nat := 118140960795 + 5952520 * 2 ^ 59
def prefixEnd_5952520 : Nat := 4983230072969 + 3 ^ 40 * 5952520 * 2
def baseEnd_5952520 : Nat := 339611540611239552424985

theorem tailTrace_5952520 : CollatzResearch.WordTrace tailWord_5952520 prefixEnd_5952520 339611540611239552424985 := by
  unfold tailWord_5952520
  simp only [CollatzResearch.WordTrace]
  refine ⟨108553120197522062162347507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144737493596696082883130009 108553120197522062162347507)
  ·
    refine ⟨162829680296283093243521261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108553120197522062162347507 162829680296283093243521261)
    ·
      refine ⟨61061130111106159966320473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162829680296283093243521261 61061130111106159966320473)
      ·
        refine ⟨45795847583329619974740355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61061130111106159966320473 45795847583329619974740355)
        ·
          refine ⟨68693771374994429962110533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45795847583329619974740355 68693771374994429962110533)
          ·
            refine ⟨12880082132811455617895725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68693771374994429962110533 12880082132811455617895725)
            ·
              refine ⟨4830030799804295856710897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12880082132811455617895725 4830030799804295856710897)
              ·
                refine ⟨3622523099853221892533173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830030799804295856710897 3622523099853221892533173)
                ·
                  refine ⟨339611540611239552424985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3622523099853221892533173 339611540611239552424985)
                  ·
                    rfl

theorem cell23_5952520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 5].length) (baseStart_5952520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952520 prefixEnd_5952520 := by exact prefixLift 5952520
  have htrace : WordTrace (prefixWord ++ tailWord_5952520) baseStart_5952520 baseEnd_5952520 := by
    simpa [prefixWord, tailWord_5952520, baseEnd_5952520] using wordTrace_append hprefix tailTrace_5952520
  have hstable : (prefixWord ++ tailWord_5952520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952520).length < 2 ^ (prefixWord ++ tailWord_5952520).sum := by decide
  have hdescent : baseEnd_5952520 < baseStart_5952520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952526 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5952526 : Nat := 118140960795 + 5952526 * 2 ^ 59
def prefixEnd_5952526 : Nat := 4983230072969 + 3 ^ 40 * 5952526 * 2
def baseEnd_5952526 : Nat := 3056506946385082948349837

theorem tailTrace_5952526 : CollatzResearch.WordTrace tailWord_5952526 prefixEnd_5952526 3056506946385082948349837 := by
  unfold tailWord_5952526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27138307404127798418676679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144737639488681591566275621 27138307404127798418676679)
  ·
    refine ⟨40707461106191697628015019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27138307404127798418676679 40707461106191697628015019)
    ·
      refine ⟨61061191659287546442022529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40707461106191697628015019 61061191659287546442022529)
      ·
        refine ⟨45795893744465659831516897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61061191659287546442022529 45795893744465659831516897)
        ·
          refine ⟨34346920308349244873637673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45795893744465659831516897 34346920308349244873637673)
          ·
            refine ⟨25760190231261933655228255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34346920308349244873637673 25760190231261933655228255)
            ·
              refine ⟨38640285346892900482842383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25760190231261933655228255 38640285346892900482842383)
              ·
                refine ⟨57960428020339350724263575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38640285346892900482842383 57960428020339350724263575)
                ·
                  refine ⟨86940642030509026086395363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57960428020339350724263575 86940642030509026086395363)
                  ·
                    refine ⟨130410963045763539129593045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86940642030509026086395363 130410963045763539129593045)
                    ·
                      refine ⟨3056506946385082948349837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130410963045763539129593045 3056506946385082948349837)
                      ·
                        rfl

theorem cell23_5952526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5952526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952526 prefixEnd_5952526 := by exact prefixLift 5952526
  have htrace : WordTrace (prefixWord ++ tailWord_5952526) baseStart_5952526 baseEnd_5952526 := by
    simpa [prefixWord, tailWord_5952526, baseEnd_5952526] using wordTrace_append hprefix tailTrace_5952526
  have hstable : (prefixWord ++ tailWord_5952526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952526).length < 2 ^ (prefixWord ++ tailWord_5952526).sum := by decide
  have hdescent : baseEnd_5952526 < baseStart_5952526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952539 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_5952539 : Nat := 118140960795 + 5952539 * 2 ^ 59
def prefixEnd_5952539 : Nat := 4983230072969 + 3 ^ 40 * 5952539 * 2
def baseEnd_5952539 : Nat := 3056513621633591397487277

theorem tailTrace_5952539 : CollatzResearch.WordTrace tailWord_5952539 prefixEnd_5952539 3056513621633591397487277 := by
  unfold tailWord_5952539
  simp only [CollatzResearch.WordTrace]
  refine ⟨217106933381975290569636671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144737955587983527046424447 217106933381975290569636671)
  ·
    refine ⟨325660400072962935854455007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217106933381975290569636671 325660400072962935854455007)
    ·
      refine ⟨488490600109444403781682511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325660400072962935854455007 488490600109444403781682511)
      ·
        refine ⟨732735900164166605672523767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488490600109444403781682511 732735900164166605672523767)
        ·
          refine ⟨1099103850246249908508785651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732735900164166605672523767 1099103850246249908508785651)
          ·
            refine ⟨1648655775369374862763178477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099103850246249908508785651 1648655775369374862763178477)
            ·
              refine ⟨618245915763515573536191929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1648655775369374862763178477 618245915763515573536191929)
              ·
                refine ⟨463684436822636680152143947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618245915763515573536191929 463684436822636680152143947)
                ·
                  refine ⟨695526655233955020228215921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463684436822636680152143947 695526655233955020228215921)
                  ·
                    refine ⟨521644991425466265171161941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 695526655233955020228215921 521644991425466265171161941)
                    ·
                      refine ⟨3056513621633591397487277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 521644991425466265171161941 3056513621633591397487277)
                      ·
                        rfl

theorem cell23_5952539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_5952539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952539 prefixEnd_5952539 := by exact prefixLift 5952539
  have htrace : WordTrace (prefixWord ++ tailWord_5952539) baseStart_5952539 baseEnd_5952539 := by
    simpa [prefixWord, tailWord_5952539, baseEnd_5952539] using wordTrace_append hprefix tailTrace_5952539
  have hstable : (prefixWord ++ tailWord_5952539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952539).length < 2 ^ (prefixWord ++ tailWord_5952539).sum := by decide
  have hdescent : baseEnd_5952539 < baseStart_5952539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952623 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 1, 5]
def baseStart_5952623 : Nat := 118140960795 + 5952623 * 2 ^ 59
def prefixEnd_5952623 : Nat := 4983230072969 + 3 ^ 40 * 5952623 * 2
def baseEnd_5952623 : Nat := 1018852251336189689612297

theorem tailTrace_5952623 : CollatzResearch.WordTrace tailWord_5952623 prefixEnd_5952623 1018852251336189689612297 := by
  unfold tailWord_5952623
  simp only [CollatzResearch.WordTrace]
  refine ⟨217109997113670972915694523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144739998075780648610463015 217109997113670972915694523)
  ·
    refine ⟨325664995670506459373541785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217109997113670972915694523 325664995670506459373541785)
    ·
      refine ⟨244248746752879844530156339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325664995670506459373541785 244248746752879844530156339)
      ·
        refine ⟨366373120129319766795234509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244248746752879844530156339 366373120129319766795234509)
        ·
          refine ⟨137389920048494912548212941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366373120129319766795234509 137389920048494912548212941)
          ·
            refine ⟨51521220018185592205579853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137389920048494912548212941 51521220018185592205579853)
            ·
              refine ⟨19320457506819597077092445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51521220018185592205579853 19320457506819597077092445)
              ·
                refine ⟨7245171565057348903909667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19320457506819597077092445 7245171565057348903909667)
                ·
                  refine ⟨10867757347586023355864501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7245171565057348903909667 10867757347586023355864501)
                  ·
                    refine ⟨1018852251336189689612297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10867757347586023355864501 1018852251336189689612297)
                    ·
                      rfl

theorem cell23_5952623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_5952623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952623 prefixEnd_5952623 := by exact prefixLift 5952623
  have htrace : WordTrace (prefixWord ++ tailWord_5952623) baseStart_5952623 baseEnd_5952623 := by
    simpa [prefixWord, tailWord_5952623, baseEnd_5952623] using wordTrace_append hprefix tailTrace_5952623
  have hstable : (prefixWord ++ tailWord_5952623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952623).length < 2 ^ (prefixWord ++ tailWord_5952623).sum := by decide
  have hdescent : baseEnd_5952623 < baseStart_5952623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952637 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_5952637 : Nat := 118140960795 + 5952637 * 2 ^ 59
def prefixEnd_5952637 : Nat := 4983230072969 + 3 ^ 40 * 5952637 * 2
def baseEnd_5952637 : Nat := 3056563942737732014061827

theorem tailTrace_5952637 : CollatzResearch.WordTrace tailWord_5952637 prefixEnd_5952637 3056563942737732014061827 := by
  unfold tailWord_5952637
  simp only [CollatzResearch.WordTrace]
  refine ⟨217110507735620253306704165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144740338490413502204469443 217110507735620253306704165)
  ·
    refine ⟨40708220200428797495007031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217110507735620253306704165 40708220200428797495007031)
    ·
      refine ⟨61062330300643196242510547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40708220200428797495007031 61062330300643196242510547)
      ·
        refine ⟨91593495450964794363765821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61062330300643196242510547 91593495450964794363765821)
        ·
          refine ⟨34347560794111797886412183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91593495450964794363765821 34347560794111797886412183)
          ·
            refine ⟨51521341191167696829618275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34347560794111797886412183 51521341191167696829618275)
            ·
              refine ⟨77282011786751545244427413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51521341191167696829618275 77282011786751545244427413)
              ·
                refine ⟨3622594302503978683332535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77282011786751545244427413 3622594302503978683332535)
                ·
                  refine ⟨5433891453755968024998803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622594302503978683332535 5433891453755968024998803)
                  ·
                    refine ⟨8150837180633952037498205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433891453755968024998803 8150837180633952037498205)
                    ·
                      refine ⟨3056563942737732014061827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8150837180633952037498205 3056563942737732014061827)
                      ·
                        rfl

theorem cell23_5952637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_5952637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952637 prefixEnd_5952637 := by exact prefixLift 5952637
  have htrace : WordTrace (prefixWord ++ tailWord_5952637) baseStart_5952637 baseEnd_5952637 := by
    simpa [prefixWord, tailWord_5952637, baseEnd_5952637] using wordTrace_append hprefix tailTrace_5952637
  have hstable : (prefixWord ++ tailWord_5952637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952637).length < 2 ^ (prefixWord ++ tailWord_5952637).sum := by decide
  have hdescent : baseEnd_5952637 < baseStart_5952637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952671 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5952671 : Nat := 118140960795 + 5952671 * 2 ^ 59
def prefixEnd_5952671 : Nat := 4983230072969 + 3 ^ 40 * 5952671 * 2
def baseEnd_5952671 : Nat := 3056581401079984881036671

theorem tailTrace_5952671 : CollatzResearch.WordTrace tailWord_5952671 prefixEnd_5952671 3056581401079984881036671 := by
  unfold tailWord_5952671
  simp only [CollatzResearch.WordTrace]
  refine ⟨217111747817497077113441867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144741165211664718075627911 217111747817497077113441867)
  ·
    refine ⟨325667621726245615670162801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217111747817497077113441867 325667621726245615670162801)
    ·
      refine ⟨244250716294684211752622101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325667621726245615670162801 244250716294684211752622101)
      ·
        refine ⟨11449252326313322425904161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244250716294684211752622101 11449252326313322425904161)
        ·
          refine ⟨8586939244734991819428121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11449252326313322425904161 8586939244734991819428121)
          ·
            refine ⟨6440204433551243864571091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8586939244734991819428121 6440204433551243864571091)
            ·
              refine ⟨9660306650326865796856637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440204433551243864571091 9660306650326865796856637)
              ·
                refine ⟨3622614993872574673821239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9660306650326865796856637 3622614993872574673821239)
                ·
                  refine ⟨5433922490808862010731859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622614993872574673821239 5433922490808862010731859)
                  ·
                    refine ⟨8150883736213293016097789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433922490808862010731859 8150883736213293016097789)
                    ·
                      refine ⟨3056581401079984881036671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8150883736213293016097789 3056581401079984881036671)
                      ·
                        rfl

theorem cell23_5952671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5952671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952671 prefixEnd_5952671 := by exact prefixLift 5952671
  have htrace : WordTrace (prefixWord ++ tailWord_5952671) baseStart_5952671 baseEnd_5952671 := by
    simpa [prefixWord, tailWord_5952671, baseEnd_5952671] using wordTrace_append hprefix tailTrace_5952671
  have hstable : (prefixWord ++ tailWord_5952671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952671).length < 2 ^ (prefixWord ++ tailWord_5952671).sum := by decide
  have hdescent : baseEnd_5952671 < baseStart_5952671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952673 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5952673 : Nat := 118140960795 + 5952673 * 2 ^ 59
def prefixEnd_5952673 : Nat := 4983230072969 + 3 ^ 40 * 5952673 * 2
def baseEnd_5952673 : Nat := 3056582428041293873211661

theorem tailTrace_5952673 : CollatzResearch.WordTrace tailWord_5952673 prefixEnd_5952673 3056582428041293873211661 := by
  unfold tailWord_5952673
  simp only [CollatzResearch.WordTrace]
  refine ⟨217111820763489831455014673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144741213842326554303343115 217111820763489831455014673)
  ·
    refine ⟨162833865572617373591261005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217111820763489831455014673 162833865572617373591261005)
    ·
      refine ⟨61062699589731515096722877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162833865572617373591261005 61062699589731515096722877)
      ·
        refine ⟨22898512346149318161271079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61062699589731515096722877 22898512346149318161271079)
        ·
          refine ⟨34347768519223977241906619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22898512346149318161271079 34347768519223977241906619)
          ·
            refine ⟨51521652778835965862859929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34347768519223977241906619 51521652778835965862859929)
            ·
              refine ⟨38641239584126974397144947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51521652778835965862859929 38641239584126974397144947)
              ·
                refine ⟨57961859376190461595717421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38641239584126974397144947 57961859376190461595717421)
                ·
                  refine ⟨21735697266071423098394033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57961859376190461595717421 21735697266071423098394033)
                  ·
                    refine ⟨16301772949553567323795525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21735697266071423098394033 16301772949553567323795525)
                    ·
                      refine ⟨3056582428041293873211661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16301772949553567323795525 3056582428041293873211661)
                      ·
                        rfl

theorem cell23_5952673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5952673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952673 prefixEnd_5952673 := by exact prefixLift 5952673
  have htrace : WordTrace (prefixWord ++ tailWord_5952673) baseStart_5952673 baseEnd_5952673 := by
    simpa [prefixWord, tailWord_5952673, baseEnd_5952673] using wordTrace_append hprefix tailTrace_5952673
  have hstable : (prefixWord ++ tailWord_5952673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952673).length < 2 ^ (prefixWord ++ tailWord_5952673).sum := by decide
  have hdescent : baseEnd_5952673 < baseStart_5952673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952704 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 2, 4]
def baseStart_5952704 : Nat := 118140960795 + 5952704 * 2 ^ 59
def prefixEnd_5952704 : Nat := 4983230072969 + 3 ^ 40 * 5952704 * 2
def baseEnd_5952704 : Nat := 1018866115313861083974673

theorem tailTrace_5952704 : CollatzResearch.WordTrace tailWord_5952704 prefixEnd_5952704 1018866115313861083974673 := by
  unfold tailWord_5952704
  simp only [CollatzResearch.WordTrace]
  refine ⟨108556475713188761874696583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144741967617585015832928777 108556475713188761874696583)
  ·
    refine ⟨162834713569783142812044875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108556475713188761874696583 162834713569783142812044875)
    ·
      refine ⟨244252070354674714218067313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162834713569783142812044875 244252070354674714218067313)
      ·
        refine ⟨183189052766006035663550485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244252070354674714218067313 183189052766006035663550485)
        ·
          refine ⟨8586986848406532921728929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183189052766006035663550485 8586986848406532921728929)
          ·
            refine ⟨6440240136304899691296697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8586986848406532921728929 6440240136304899691296697)
            ·
              refine ⟨4830180102228674768472523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440240136304899691296697 4830180102228674768472523)
              ·
                refine ⟨7245270153343012152708785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830180102228674768472523 7245270153343012152708785)
                ·
                  refine ⟨5433952615007259114531589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7245270153343012152708785 5433952615007259114531589)
                  ·
                    refine ⟨1018866115313861083974673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5433952615007259114531589 1018866115313861083974673)
                    ·
                      rfl

theorem cell23_5952704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 4].length) (baseStart_5952704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952704 prefixEnd_5952704 := by exact prefixLift 5952704
  have htrace : WordTrace (prefixWord ++ tailWord_5952704) baseStart_5952704 baseEnd_5952704 := by
    simpa [prefixWord, tailWord_5952704, baseEnd_5952704] using wordTrace_append hprefix tailTrace_5952704
  have hstable : (prefixWord ++ tailWord_5952704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952704).length < 2 ^ (prefixWord ++ tailWord_5952704).sum := by decide
  have hdescent : baseEnd_5952704 < baseStart_5952704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952767 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 1, 4, 2]
def baseStart_5952767 : Nat := 118140960795 + 5952767 * 2 ^ 59
def prefixEnd_5952767 : Nat := 4983230072969 + 3 ^ 40 * 5952767 * 2
def baseEnd_5952767 : Nat := 3056630695222816505436229

theorem tailTrace_5952767 : CollatzResearch.WordTrace tailWord_5952767 prefixEnd_5952767 3056630695222816505436229 := by
  unfold tailWord_5952767
  simp only [CollatzResearch.WordTrace]
  refine ⟨217115249225149285508936555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144743499483432857005957703 217115249225149285508936555)
  ·
    refine ⟨325672873837723928263404833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217115249225149285508936555 325672873837723928263404833)
    ·
      refine ⟨244254655378292946197553625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325672873837723928263404833 244254655378292946197553625)
      ·
        refine ⟨183190991533719709648165219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244254655378292946197553625 183190991533719709648165219)
        ·
          refine ⟨274786487300579564472247829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183190991533719709648165219 274786487300579564472247829)
          ·
            refine ⟨12880616592214667084636617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 274786487300579564472247829 12880616592214667084636617)
            ·
              refine ⟨9660462444161000313477463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12880616592214667084636617 9660462444161000313477463)
              ·
                refine ⟨14490693666241500470216195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9660462444161000313477463 14490693666241500470216195)
                ·
                  refine ⟨21736040499362250705324293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14490693666241500470216195 21736040499362250705324293)
                  ·
                    refine ⟨4075507593630422007248305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21736040499362250705324293 4075507593630422007248305)
                    ·
                      refine ⟨3056630695222816505436229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4075507593630422007248305 3056630695222816505436229)
                      ·
                        rfl

theorem cell23_5952767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_5952767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952767 prefixEnd_5952767 := by exact prefixLift 5952767
  have htrace : WordTrace (prefixWord ++ tailWord_5952767) baseStart_5952767 baseEnd_5952767 := by
    simpa [prefixWord, tailWord_5952767, baseEnd_5952767] using wordTrace_append hprefix tailTrace_5952767
  have hstable : (prefixWord ++ tailWord_5952767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952767).length < 2 ^ (prefixWord ++ tailWord_5952767).sum := by decide
  have hdescent : baseEnd_5952767 < baseStart_5952767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952773 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 7]
def baseStart_5952773 : Nat := 118140960795 + 5952773 * 2 ^ 59
def prefixEnd_5952773 : Nat := 4983230072969 + 3 ^ 40 * 5952773 * 2
def baseEnd_5952773 : Nat := 339625975122971497995689

theorem tailTrace_5952773 : CollatzResearch.WordTrace tailWord_5952773 prefixEnd_5952773 339625975122971497995689 := by
  unfold tailWord_5952773
  simp only [CollatzResearch.WordTrace]
  refine ⟨217115468063127548533654973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144743645375418365689103315 217115468063127548533654973)
  ·
    refine ⟨81418300523672830700120615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217115468063127548533654973 81418300523672830700120615)
    ·
      refine ⟨122127450785509246050180923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81418300523672830700120615 122127450785509246050180923)
      ·
        refine ⟨183191176178263869075271385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122127450785509246050180923 183191176178263869075271385)
        ·
          refine ⟨137393382133697901806453539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183191176178263869075271385 137393382133697901806453539)
          ·
            refine ⟨206090073200546852709680309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137393382133697901806453539 206090073200546852709680309)
            ·
              refine ⟨19320944362551267441532529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206090073200546852709680309 19320944362551267441532529)
              ·
                refine ⟨14490708271913450581149397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19320944362551267441532529 14490708271913450581149397)
                ·
                  refine ⟨339625975122971497995689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14490708271913450581149397 339625975122971497995689)
                  ·
                    rfl

theorem cell23_5952773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_5952773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952773 prefixEnd_5952773 := by exact prefixLift 5952773
  have htrace : WordTrace (prefixWord ++ tailWord_5952773) baseStart_5952773 baseEnd_5952773 := by
    simpa [prefixWord, tailWord_5952773, baseEnd_5952773] using wordTrace_append hprefix tailTrace_5952773
  have hstable : (prefixWord ++ tailWord_5952773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952773).length < 2 ^ (prefixWord ++ tailWord_5952773).sum := by decide
  have hdescent : baseEnd_5952773 < baseStart_5952773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952820 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_5952820 : Nat := 118140960795 + 5952820 * 2 ^ 59
def prefixEnd_5952820 : Nat := 4983230072969 + 3 ^ 40 * 5952820 * 2
def baseEnd_5952820 : Nat := 1018885969899168266024495

theorem tailTrace_5952820 : CollatzResearch.WordTrace tailWord_5952820 prefixEnd_5952820 1018885969899168266024495 := by
  unfold tailWord_5952820
  simp only [CollatzResearch.WordTrace]
  refine ⟨108558591146978637780307957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144744788195971517040410609 108558591146978637780307957)
  ·
    refine ⟨10177367920029247291903871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108558591146978637780307957 10177367920029247291903871)
    ·
      refine ⟨15266051880043870937855807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10177367920029247291903871 15266051880043870937855807)
      ·
        refine ⟨22899077820065806406783711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15266051880043870937855807 22899077820065806406783711)
        ·
          refine ⟨34348616730098709610175567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22899077820065806406783711 34348616730098709610175567)
          ·
            refine ⟨51522925095148064415263351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34348616730098709610175567 51522925095148064415263351)
            ·
              refine ⟨77284387642722096622895027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51522925095148064415263351 77284387642722096622895027)
              ·
                refine ⟨115926581464083144934342541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77284387642722096622895027 115926581464083144934342541)
                ·
                  refine ⟨43472468049031179350378453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115926581464083144934342541 43472468049031179350378453)
                  ·
                    refine ⟨1018885969899168266024495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43472468049031179350378453 1018885969899168266024495)
                    ·
                      rfl

theorem cell23_5952820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_5952820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952820 prefixEnd_5952820 := by exact prefixLift 5952820
  have htrace : WordTrace (prefixWord ++ tailWord_5952820) baseStart_5952820 baseEnd_5952820 := by
    simpa [prefixWord, tailWord_5952820, baseEnd_5952820] using wordTrace_append hprefix tailTrace_5952820
  have hstable : (prefixWord ++ tailWord_5952820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952820).length < 2 ^ (prefixWord ++ tailWord_5952820).sum := by decide
  have hdescent : baseEnd_5952820 < baseStart_5952820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952840 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_5952840 : Nat := 118140960795 + 5952840 * 2 ^ 59
def prefixEnd_5952840 : Nat := 4983230072969 + 3 ^ 40 * 5952840 * 2
def baseEnd_5952840 : Nat := 3056668179310594719823393

theorem tailTrace_5952840 : CollatzResearch.WordTrace tailWord_5952840 prefixEnd_5952840 3056668179310594719823393 := by
  unfold tailWord_5952840
  simp only [CollatzResearch.WordTrace]
  refine ⟨108558955876942409488171987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144745274502589879317562649 108558955876942409488171987)
  ·
    refine ⟨162838433815413614232257981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108558955876942409488171987 162838433815413614232257981)
    ·
      refine ⟨61064412680780105337096743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162838433815413614232257981 61064412680780105337096743)
      ·
        refine ⟨91596619021170158005645115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61064412680780105337096743 91596619021170158005645115)
        ·
          refine ⟨137394928531755237008467673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91596619021170158005645115 137394928531755237008467673)
          ·
            refine ⟨103046196398816427756350755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137394928531755237008467673 103046196398816427756350755)
            ·
              refine ⟨154569294598224641634526133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103046196398816427756350755 154569294598224641634526133)
              ·
                refine ⟨14490871368583560153236825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154569294598224641634526133 14490871368583560153236825)
                ·
                  refine ⟨10868153526437670114927619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14490871368583560153236825 10868153526437670114927619)
                  ·
                    refine ⟨16302230289656505172391429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10868153526437670114927619 16302230289656505172391429)
                    ·
                      refine ⟨3056668179310594719823393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16302230289656505172391429 3056668179310594719823393)
                      ·
                        rfl

theorem cell23_5952840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_5952840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952840 prefixEnd_5952840 := by exact prefixLift 5952840
  have htrace : WordTrace (prefixWord ++ tailWord_5952840) baseStart_5952840 baseEnd_5952840 := by
    simpa [prefixWord, tailWord_5952840, baseEnd_5952840] using wordTrace_append hprefix tailTrace_5952840
  have hstable : (prefixWord ++ tailWord_5952840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952840).length < 2 ^ (prefixWord ++ tailWord_5952840).sum := by decide
  have hdescent : baseEnd_5952840 < baseStart_5952840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952867 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 3, 4]
def baseStart_5952867 : Nat := 118140960795 + 5952867 * 2 ^ 59
def prefixEnd_5952867 : Nat := 4983230072969 + 3 ^ 40 * 5952867 * 2
def baseEnd_5952867 : Nat := 1018894014429422038061923

theorem tailTrace_5952867 : CollatzResearch.WordTrace tailWord_5952867 prefixEnd_5952867 1018894014429422038061923 := by
  unfold tailWord_5952867
  simp only [CollatzResearch.WordTrace]
  refine ⟨217118896524787002587576855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144745931016524668391717903 217118896524787002587576855)
  ·
    refine ⟨325678344787180503881365283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217118896524787002587576855 325678344787180503881365283)
    ·
      refine ⟨488517517180770755822047925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325678344787180503881365283 488517517180770755822047925)
      ·
        refine ⟨45798517235697258358316993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 488517517180770755822047925 45798517235697258358316993)
        ·
          refine ⟨34348887926772943768737745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45798517235697258358316993 34348887926772943768737745)
          ·
            refine ⟨25761665945079707826553309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34348887926772943768737745 25761665945079707826553309)
            ·
              refine ⟨9660624729404890434957491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25761665945079707826553309 9660624729404890434957491)
              ·
                refine ⟨14490937094107335652436237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9660624729404890434957491 14490937094107335652436237)
                ·
                  refine ⟨5434101410290250869663589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14490937094107335652436237 5434101410290250869663589)
                  ·
                    refine ⟨1018894014429422038061923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434101410290250869663589 1018894014429422038061923)
                    ·
                      rfl

theorem cell23_5952867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 4].length) (baseStart_5952867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952867 prefixEnd_5952867 := by exact prefixLift 5952867
  have htrace : WordTrace (prefixWord ++ tailWord_5952867) baseStart_5952867 baseEnd_5952867 := by
    simpa [prefixWord, tailWord_5952867, baseEnd_5952867] using wordTrace_append hprefix tailTrace_5952867
  have hstable : (prefixWord ++ tailWord_5952867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952867).length < 2 ^ (prefixWord ++ tailWord_5952867).sum := by decide
  have hdescent : baseEnd_5952867 < baseStart_5952867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952880 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 6]
def baseStart_5952880 : Nat := 118140960795 + 5952880 * 2 ^ 59
def prefixEnd_5952880 : Nat := 4983230072969 + 3 ^ 40 * 5952880 * 2
def baseEnd_5952880 : Nat := 339632079837419395924801

theorem tailTrace_5952880 : CollatzResearch.WordTrace tailWord_5952880 prefixEnd_5952880 339632079837419395924801 := by
  unfold tailWord_5952880
  simp only [CollatzResearch.WordTrace]
  refine ⟨108559685336869952903900047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144746247115826603871866729 108559685336869952903900047)
  ·
    refine ⟨162839528005304929355850071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108559685336869952903900047 162839528005304929355850071)
    ·
      refine ⟨244259292007957394033775107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162839528005304929355850071 244259292007957394033775107)
      ·
        refine ⟨366388938011936091050662661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244259292007957394033775107 366388938011936091050662661)
        ·
          refine ⟨68697925877238017071999249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366388938011936091050662661 68697925877238017071999249)
          ·
            refine ⟨51523444407928512803999437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68697925877238017071999249 51523444407928512803999437)
            ·
              refine ⟨19321291652973192301499789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51523444407928512803999437 19321291652973192301499789)
              ·
                refine ⟨7245484369864947113062421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19321291652973192301499789 7245484369864947113062421)
                ·
                  refine ⟨339632079837419395924801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7245484369864947113062421 339632079837419395924801)
                  ·
                    rfl

theorem cell23_5952880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_5952880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952880 prefixEnd_5952880 := by exact prefixLift 5952880
  have htrace : WordTrace (prefixWord ++ tailWord_5952880) baseStart_5952880 baseEnd_5952880 := by
    simpa [prefixWord, tailWord_5952880, baseEnd_5952880] using wordTrace_append hprefix tailTrace_5952880
  have hstable : (prefixWord ++ tailWord_5952880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952880).length < 2 ^ (prefixWord ++ tailWord_5952880).sum := by decide
  have hdescent : baseEnd_5952880 < baseStart_5952880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952940 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_5952940 : Nat := 118140960795 + 5952940 * 2 ^ 59
def prefixEnd_5952940 : Nat := 4983230072969 + 3 ^ 40 * 5952940 * 2
def baseEnd_5952940 : Nat := 1018906509125348109524311

theorem tailTrace_5952940 : CollatzResearch.WordTrace tailWord_5952940 prefixEnd_5952940 1018906509125348109524311 := by
  unfold tailWord_5952940
  simp only [CollatzResearch.WordTrace]
  refine ⟨108560779526761268027492137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144747706035681690703322849 108560779526761268027492137)
  ·
    refine ⟨81420584645070951020619103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108560779526761268027492137 81420584645070951020619103)
    ·
      refine ⟨122130876967606426530928655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81420584645070951020619103 122130876967606426530928655)
      ·
        refine ⟨183196315451409639796392983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122130876967606426530928655 183196315451409639796392983)
        ·
          refine ⟨274794473177114459694589475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183196315451409639796392983 274794473177114459694589475)
          ·
            refine ⟨412191709765671689541884213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274794473177114459694589475 412191709765671689541884213)
            ·
              refine ⟨38642972790531720894551645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 412191709765671689541884213 38642972790531720894551645)
              ·
                refine ⟨14491114796449395335456867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38642972790531720894551645 14491114796449395335456867)
                ·
                  refine ⟨21736672194674093003185301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14491114796449395335456867 21736672194674093003185301)
                  ·
                    refine ⟨1018906509125348109524311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21736672194674093003185301 1018906509125348109524311)
                    ·
                      rfl

theorem cell23_5952940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_5952940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952940 prefixEnd_5952940 := by exact prefixLift 5952940
  have htrace : WordTrace (prefixWord ++ tailWord_5952940) baseStart_5952940 baseEnd_5952940 := by
    simpa [prefixWord, tailWord_5952940, baseEnd_5952940] using wordTrace_append hprefix tailTrace_5952940
  have hstable : (prefixWord ++ tailWord_5952940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952940).length < 2 ^ (prefixWord ++ tailWord_5952940).sum := by decide
  have hdescent : baseEnd_5952940 < baseStart_5952940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952941 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5952941 : Nat := 118140960795 + 5952941 * 2 ^ 59
def prefixEnd_5952941 : Nat := 4983230072969 + 3 ^ 40 * 5952941 * 2
def baseEnd_5952941 : Nat := 3056720040856698824660429

theorem tailTrace_5952941 : CollatzResearch.WordTrace tailWord_5952941 prefixEnd_5952941 3056720040856698824660429 := by
  unfold tailWord_5952941
  simp only [CollatzResearch.WordTrace]
  refine ⟨217121595526518913225770677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144747730351012608817180451 217121595526518913225770677)
  ·
    refine ⟨20355149580611148114916001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217121595526518913225770677 20355149580611148114916001)
    ·
      refine ⟨15266362185458361086187001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20355149580611148114916001 15266362185458361086187001)
      ·
        refine ⟨11449771639093770814640251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15266362185458361086187001 11449771639093770814640251)
        ·
          refine ⟨17174657458640656221960377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449771639093770814640251 17174657458640656221960377)
          ·
            refine ⟨12880993093980492166470283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17174657458640656221960377 12880993093980492166470283)
            ·
              refine ⟨19321489640970738249705425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12880993093980492166470283 19321489640970738249705425)
              ·
                refine ⟨14491117230728053687279069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19321489640970738249705425 14491117230728053687279069)
                ·
                  refine ⟨5434168961523020132729651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14491117230728053687279069 5434168961523020132729651)
                  ·
                    refine ⟨8151253442284530199094477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5434168961523020132729651 8151253442284530199094477)
                    ·
                      refine ⟨3056720040856698824660429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8151253442284530199094477 3056720040856698824660429)
                      ·
                        rfl

theorem cell23_5952941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5952941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952941 prefixEnd_5952941 := by exact prefixLift 5952941
  have htrace : WordTrace (prefixWord ++ tailWord_5952941) baseStart_5952941 baseEnd_5952941 := by
    simpa [prefixWord, tailWord_5952941, baseEnd_5952941] using wordTrace_append hprefix tailTrace_5952941
  have hstable : (prefixWord ++ tailWord_5952941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952941).length < 2 ^ (prefixWord ++ tailWord_5952941).sum := by decide
  have hdescent : baseEnd_5952941 < baseStart_5952941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952957 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_5952957 : Nat := 118140960795 + 5952957 * 2 ^ 59
def prefixEnd_5952957 : Nat := 4983230072969 + 3 ^ 40 * 5952957 * 2
def baseEnd_5952957 : Nat := 1018909418849056920686785

theorem tailTrace_5952957 : CollatzResearch.WordTrace tailWord_5952957 prefixEnd_5952957 1018909418849056920686785 := by
  unfold tailWord_5952957
  simp only [CollatzResearch.WordTrace]
  refine ⟨217122179094460947958353125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144748119396307298638902083 217122179094460947958353125)
  ·
    refine ⟨40710408580211427742191211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217122179094460947958353125 40710408580211427742191211)
    ·
      refine ⟨61065612870317141613286817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40710408580211427742191211 61065612870317141613286817)
      ·
        refine ⟨45799209652737856209965113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61065612870317141613286817 45799209652737856209965113)
        ·
          refine ⟨34349407239553392157473835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45799209652737856209965113 34349407239553392157473835)
          ·
            refine ⟨51524110859330088236210753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34349407239553392157473835 51524110859330088236210753)
            ·
              refine ⟨38643083144497566177158065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51524110859330088236210753 38643083144497566177158065)
              ·
                refine ⟨28982312358373174632868549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38643083144497566177158065 28982312358373174632868549)
                ·
                  refine ⟨5434183567194970243662853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28982312358373174632868549 5434183567194970243662853)
                  ·
                    refine ⟨1018909418849056920686785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434183567194970243662853 1018909418849056920686785)
                    ·
                      rfl

theorem cell23_5952957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_5952957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952957 prefixEnd_5952957 := by exact prefixLift 5952957
  have htrace : WordTrace (prefixWord ++ tailWord_5952957) baseStart_5952957 baseEnd_5952957 := by
    simpa [prefixWord, tailWord_5952957, baseEnd_5952957] using wordTrace_append hprefix tailTrace_5952957
  have hstable : (prefixWord ++ tailWord_5952957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952957).length < 2 ^ (prefixWord ++ tailWord_5952957).sum := by decide
  have hdescent : baseEnd_5952957 < baseStart_5952957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952970 : List Nat := [3, 1, 2, 1, 2, 4, 10]
def baseStart_5952970 : Nat := 118140960795 + 5952970 * 2 ^ 59
def prefixEnd_5952970 : Nat := 4983230072969 + 3 ^ 40 * 5952970 * 2
def baseEnd_5952970 : Nat := 37737468293773817422195

theorem tailTrace_5952970 : CollatzResearch.WordTrace tailWord_5952970 prefixEnd_5952970 37737468293773817422195 := by
  unfold tailWord_5952970
  simp only [CollatzResearch.WordTrace]
  refine ⟨54280663310853462794644091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144748435495609234119050909 54280663310853462794644091)
  ·
    refine ⟨81420994966280194191966137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54280663310853462794644091 81420994966280194191966137)
    ·
      refine ⟨61065746224710145643974603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81420994966280194191966137 61065746224710145643974603)
      ·
        refine ⟨91598619337065218465961905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61065746224710145643974603 91598619337065218465961905)
        ·
          refine ⟨68698964502798913849471429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91598619337065218465961905 68698964502798913849471429)
          ·
            refine ⟨12881055844274796346775893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68698964502798913849471429 12881055844274796346775893)
            ·
              refine ⟨37737468293773817422195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12881055844274796346775893 37737468293773817422195)
              ·
                rfl

theorem cell23_5952970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 10].length) (baseStart_5952970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952970 prefixEnd_5952970 := by exact prefixLift 5952970
  have htrace : WordTrace (prefixWord ++ tailWord_5952970) baseStart_5952970 baseEnd_5952970 := by
    simpa [prefixWord, tailWord_5952970, baseEnd_5952970] using wordTrace_append hprefix tailTrace_5952970
  have hstable : (prefixWord ++ tailWord_5952970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952970).length < 2 ^ (prefixWord ++ tailWord_5952970).sum := by decide
  have hdescent : baseEnd_5952970 < baseStart_5952970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952974 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_5952974 : Nat := 118140960795 + 5952974 * 2 ^ 59
def prefixEnd_5952974 : Nat := 4983230072969 + 3 ^ 40 * 5952974 * 2
def baseEnd_5952974 : Nat := 1018912328572765731849259

theorem tailTrace_5952974 : CollatzResearch.WordTrace tailWord_5952974 prefixEnd_5952974 1018912328572765731849259 := by
  unfold tailWord_5952974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27140349891924919982715247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144748532756932906574481317 27140349891924919982715247)
  ·
    refine ⟨40710524837887379974072871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27140349891924919982715247 40710524837887379974072871)
    ·
      refine ⟨61065787256831069961109307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40710524837887379974072871 61065787256831069961109307)
      ·
        refine ⟨91598680885246604941663961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61065787256831069961109307 91598680885246604941663961)
        ·
          refine ⟨68699010663934953706247971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91598680885246604941663961 68699010663934953706247971)
          ·
            refine ⟨103048515995902430559371957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68699010663934953706247971 103048515995902430559371957)
            ·
              refine ⟨9660798374615852864941121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103048515995902430559371957 9660798374615852864941121)
              ·
                refine ⟨7245598780961889648705841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9660798374615852864941121 7245598780961889648705841)
                ·
                  refine ⟨5434199085721417236529381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7245598780961889648705841 5434199085721417236529381)
                  ·
                    refine ⟨1018912328572765731849259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434199085721417236529381 1018912328572765731849259)
                    ·
                      rfl

theorem cell23_5952974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_5952974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952974 prefixEnd_5952974 := by exact prefixLift 5952974
  have htrace : WordTrace (prefixWord ++ tailWord_5952974) baseStart_5952974 baseEnd_5952974 := by
    simpa [prefixWord, tailWord_5952974, baseEnd_5952974] using wordTrace_append hprefix tailTrace_5952974
  have hstable : (prefixWord ++ tailWord_5952974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952974).length < 2 ^ (prefixWord ++ tailWord_5952974).sum := by decide
  have hdescent : baseEnd_5952974 < baseStart_5952974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5952981 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5952981 : Nat := 118140960795 + 5952981 * 2 ^ 59
def prefixEnd_5952981 : Nat := 4983230072969 + 3 ^ 40 * 5952981 * 2
def baseEnd_5952981 : Nat := 3056740580082878668160245

theorem tailTrace_5952981 : CollatzResearch.WordTrace tailWord_5952981 prefixEnd_5952981 3056740580082878668160245 := by
  unfold tailWord_5952981
  simp only [CollatzResearch.WordTrace]
  refine ⟨217123054446374000057226797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144748702964249333371484531 217123054446374000057226797)
  ·
    refine ⟨81421145417390250021460049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217123054446374000057226797 81421145417390250021460049)
    ·
      refine ⟨61065859063042687516095037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81421145417390250021460049 61065859063042687516095037)
      ·
        refine ⟨22899697148641007818535639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61065859063042687516095037 22899697148641007818535639)
        ·
          refine ⟨34349545722961511727803459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22899697148641007818535639 34349545722961511727803459)
          ·
            refine ⟨51524318584442267591705189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34349545722961511727803459 51524318584442267591705189)
            ·
              refine ⟨9660809734582925173444723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51524318584442267591705189 9660809734582925173444723)
              ·
                refine ⟨14491214601874387760167085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9660809734582925173444723 14491214601874387760167085)
                ·
                  refine ⟨5434205475702895410062657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14491214601874387760167085 5434205475702895410062657)
                  ·
                    refine ⟨4075654106777171557546993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5434205475702895410062657 4075654106777171557546993)
                    ·
                      refine ⟨3056740580082878668160245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4075654106777171557546993 3056740580082878668160245)
                      ·
                        rfl

theorem cell23_5952981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5952981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5952981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5952981 prefixEnd_5952981 := by exact prefixLift 5952981
  have htrace : WordTrace (prefixWord ++ tailWord_5952981) baseStart_5952981 baseEnd_5952981 := by
    simpa [prefixWord, tailWord_5952981, baseEnd_5952981] using wordTrace_append hprefix tailTrace_5952981
  have hstable : (prefixWord ++ tailWord_5952981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5952981).length < 2 ^ (prefixWord ++ tailWord_5952981).sum := by decide
  have hdescent : baseEnd_5952981 < baseStart_5952981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5952981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953057 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5953057 : Nat := 118140960795 + 5953057 * 2 ^ 59
def prefixEnd_5953057 : Nat := 4983230072969 + 3 ^ 40 * 5953057 * 2
def baseEnd_5953057 : Nat := 3056779604612620370809895

theorem tailTrace_5953057 : CollatzResearch.WordTrace tailWord_5953057 prefixEnd_5953057 3056779604612620370809895 := by
  unfold tailWord_5953057
  simp only [CollatzResearch.WordTrace]
  refine ⟨217125826394098665036993425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144750550929399110024662283 217125826394098665036993425)
  ·
    refine ⟨162844369795573998777745069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217125826394098665036993425 162844369795573998777745069)
    ·
      refine ⟨61066638673340249541654401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162844369795573998777745069 61066638673340249541654401)
      ·
        refine ⟨45799979005005187156240801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61066638673340249541654401 45799979005005187156240801)
        ·
          refine ⟨34349984253753890367180601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45799979005005187156240801 34349984253753890367180601)
          ·
            refine ⟨25762488190315417775385451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34349984253753890367180601 25762488190315417775385451)
            ·
              refine ⟨38643732285473126663078177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25762488190315417775385451 38643732285473126663078177)
              ·
                refine ⟨28982799214104844997308633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38643732285473126663078177 28982799214104844997308633)
                ·
                  refine ⟨21737099410578633747981475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28982799214104844997308633 21737099410578633747981475)
                  ·
                    refine ⟨32605649115867950621972213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21737099410578633747981475 32605649115867950621972213)
                    ·
                      refine ⟨3056779604612620370809895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32605649115867950621972213 3056779604612620370809895)
                      ·
                        rfl

theorem cell23_5953057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5953057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953057 prefixEnd_5953057 := by exact prefixLift 5953057
  have htrace : WordTrace (prefixWord ++ tailWord_5953057) baseStart_5953057 baseEnd_5953057 := by
    simpa [prefixWord, tailWord_5953057, baseEnd_5953057] using wordTrace_append hprefix tailTrace_5953057
  have hstable : (prefixWord ++ tailWord_5953057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953057).length < 2 ^ (prefixWord ++ tailWord_5953057).sum := by decide
  have hdescent : baseEnd_5953057 < baseStart_5953057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953101 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_5953101 : Nat := 118140960795 + 5953101 * 2 ^ 59
def prefixEnd_5953101 : Nat := 4983230072969 + 3 ^ 40 * 5953101 * 2
def baseEnd_5953101 : Nat := 3056802197761418198659693

theorem tailTrace_5953101 : CollatzResearch.WordTrace tailWord_5953101 prefixEnd_5953101 3056802197761418198659693 := by
  unfold tailWord_5953101
  simp only [CollatzResearch.WordTrace]
  refine ⟨217127431205939260551595157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144751620803959507034396771 217127431205939260551595157)
  ·
    refine ⟨10177848337778402838356023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217127431205939260551595157 10177848337778402838356023)
    ·
      refine ⟨15266772506667604257534035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10177848337778402838356023 15266772506667604257534035)
      ·
        refine ⟨22900158760001406386301053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15266772506667604257534035 22900158760001406386301053)
        ·
          refine ⟨8587559535000527394862895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22900158760001406386301053 8587559535000527394862895)
          ·
            refine ⟨12881339302500791092294343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8587559535000527394862895 12881339302500791092294343)
            ·
              refine ⟨19322008953751186638441515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12881339302500791092294343 19322008953751186638441515)
              ·
                refine ⟨28983013430626779957662273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19322008953751186638441515 28983013430626779957662273)
                ·
                  refine ⟨21737260072970084968246705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28983013430626779957662273 21737260072970084968246705)
                  ·
                    refine ⟨16302945054727563726185029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21737260072970084968246705 16302945054727563726185029)
                    ·
                      refine ⟨3056802197761418198659693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16302945054727563726185029 3056802197761418198659693)
                      ·
                        rfl

theorem cell23_5953101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_5953101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953101 prefixEnd_5953101 := by exact prefixLift 5953101
  have htrace : WordTrace (prefixWord ++ tailWord_5953101) baseStart_5953101 baseEnd_5953101 := by
    simpa [prefixWord, tailWord_5953101, baseEnd_5953101] using wordTrace_append hprefix tailTrace_5953101
  have hstable : (prefixWord ++ tailWord_5953101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953101).length < 2 ^ (prefixWord ++ tailWord_5953101).sum := by decide
  have hdescent : baseEnd_5953101 < baseStart_5953101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953124 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_5953124 : Nat := 118140960795 + 5953124 * 2 ^ 59
def prefixEnd_5953124 : Nat := 4983230072969 + 3 ^ 40 * 5953124 * 2
def baseEnd_5953124 : Nat := 1018938002605490536224029

theorem tailTrace_5953124 : CollatzResearch.WordTrace tailWord_5953124 prefixEnd_5953124 1018938002605490536224029 := by
  unfold tailWord_5953124
  simp only [CollatzResearch.WordTrace]
  refine ⟨108564135042427967739841213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144752180056570623653121617 108564135042427967739841213)
  ·
    refine ⟨40711550640910487902440455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108564135042427967739841213 40711550640910487902440455)
    ·
      refine ⟨61067325961365731853660683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40711550640910487902440455 61067325961365731853660683)
      ·
        refine ⟨91600988942048597780491025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61067325961365731853660683 91600988942048597780491025)
        ·
          refine ⟨68700741706536448335368269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91600988942048597780491025 68700741706536448335368269)
          ·
            refine ⟨25762778139951168125763101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68700741706536448335368269 25762778139951168125763101)
            ·
              refine ⟨9661041802481688047161163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25762778139951168125763101 9661041802481688047161163)
              ·
                refine ⟨14491562703722532070741745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9661041802481688047161163 14491562703722532070741745)
                ·
                  refine ⟨10868672027791899053056309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14491562703722532070741745 10868672027791899053056309)
                  ·
                    refine ⟨1018938002605490536224029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10868672027791899053056309 1018938002605490536224029)
                    ·
                      rfl

theorem cell23_5953124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_5953124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953124 prefixEnd_5953124 := by exact prefixLift 5953124
  have htrace : WordTrace (prefixWord ++ tailWord_5953124) baseStart_5953124 baseEnd_5953124 := by
    simpa [prefixWord, tailWord_5953124, baseEnd_5953124] using wordTrace_append hprefix tailTrace_5953124
  have hstable : (prefixWord ++ tailWord_5953124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953124).length < 2 ^ (prefixWord ++ tailWord_5953124).sum := by decide
  have hdescent : baseEnd_5953124 < baseStart_5953124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953157 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_5953157 : Nat := 118140960795 + 5953157 * 2 ^ 59
def prefixEnd_5953157 : Nat := 4983230072969 + 3 ^ 40 * 5953157 * 2
def baseEnd_5953157 : Nat := 3056830952678069979559435

theorem tailTrace_5953157 : CollatzResearch.WordTrace tailWord_5953157 prefixEnd_5953157 3056830952678069979559435 := by
  unfold tailWord_5953157
  simp only [CollatzResearch.WordTrace]
  refine ⟨217129473693736382115633725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144752982462490921410422483 217129473693736382115633725)
  ·
    refine ⟨81423552635151143293362647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217129473693736382115633725 81423552635151143293362647)
    ·
      refine ⟨122135328952726714940043971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81423552635151143293362647 122135328952726714940043971)
      ·
        refine ⟨183202993429090072410065957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122135328952726714940043971 183202993429090072410065957)
        ·
          refine ⟨34350561267954388576887367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183202993429090072410065957 34350561267954388576887367)
          ·
            refine ⟨51525841901931582865331051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34350561267954388576887367 51525841901931582865331051)
            ·
              refine ⟨77288762852897374297996577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51525841901931582865331051 77288762852897374297996577)
              ·
                refine ⟨57966572139673030723497433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77288762852897374297996577 57966572139673030723497433)
                ·
                  refine ⟨43474929104754773042623075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57966572139673030723497433 43474929104754773042623075)
                  ·
                    refine ⟨65212393657132159563934613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43474929104754773042623075 65212393657132159563934613)
                    ·
                      refine ⟨3056830952678069979559435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65212393657132159563934613 3056830952678069979559435)
                      ·
                        rfl

theorem cell23_5953157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_5953157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953157 prefixEnd_5953157 := by exact prefixLift 5953157
  have htrace : WordTrace (prefixWord ++ tailWord_5953157) baseStart_5953157 baseEnd_5953157 := by
    simpa [prefixWord, tailWord_5953157, baseEnd_5953157] using wordTrace_append hprefix tailTrace_5953157
  have hstable : (prefixWord ++ tailWord_5953157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953157).length < 2 ^ (prefixWord ++ tailWord_5953157).sum := by decide
  have hdescent : baseEnd_5953157 < baseStart_5953157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953188 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_5953188 : Nat := 118140960795 + 5953188 * 2 ^ 59
def prefixEnd_5953188 : Nat := 4983230072969 + 3 ^ 40 * 5953188 * 2
def baseEnd_5953188 : Nat := 1018948956859453119423931

theorem tailTrace_5953188 : CollatzResearch.WordTrace tailWord_5953188 prefixEnd_5953188 1018948956859453119423931 := by
  unfold tailWord_5953188
  simp only [CollatzResearch.WordTrace]
  refine ⟨108565302178312037205006109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144753736237749382940008145 108565302178312037205006109)
  ·
    refine ⟨40711988316867013951877291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108565302178312037205006109 40711988316867013951877291)
    ·
      refine ⟨61067982475300520927815937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40711988316867013951877291 61067982475300520927815937)
      ·
        refine ⟨45800986856475390695861953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61067982475300520927815937 45800986856475390695861953)
        ·
          refine ⟨34350740142356543021896465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45800986856475390695861953 34350740142356543021896465)
          ·
            refine ⟨25763055106767407266422349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34350740142356543021896465 25763055106767407266422349)
            ·
              refine ⟨9661145665037777724908381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25763055106767407266422349 9661145665037777724908381)
              ·
                refine ⟨3622929624389166646840643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9661145665037777724908381 3622929624389166646840643)
                ·
                  refine ⟨5434394436583749970260965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622929624389166646840643 5434394436583749970260965)
                  ·
                    refine ⟨1018948956859453119423931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434394436583749970260965 1018948956859453119423931)
                    ·
                      rfl

theorem cell23_5953188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_5953188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953188 prefixEnd_5953188 := by exact prefixLift 5953188
  have htrace : WordTrace (prefixWord ++ tailWord_5953188) baseStart_5953188 baseEnd_5953188 := by
    simpa [prefixWord, tailWord_5953188, baseEnd_5953188] using wordTrace_append hprefix tailTrace_5953188
  have hstable : (prefixWord ++ tailWord_5953188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953188).length < 2 ^ (prefixWord ++ tailWord_5953188).sum := by decide
  have hdescent : baseEnd_5953188 < baseStart_5953188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953205 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_5953205 : Nat := 118140960795 + 5953205 * 2 ^ 59
def prefixEnd_5953205 : Nat := 4983230072969 + 3 ^ 40 * 5953205 * 2
def baseEnd_5953205 : Nat := 1018951866583161930586405

theorem tailTrace_5953205 : CollatzResearch.WordTrace tailWord_5953205 prefixEnd_5953205 1018951866583161930586405 := by
  unfold tailWord_5953205
  simp only [CollatzResearch.WordTrace]
  refine ⟨217131224397562486313381069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144754149598374990875587379 217131224397562486313381069)
  ·
    refine ⟨81424209149085932367517901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217131224397562486313381069 81424209149085932367517901)
    ·
      refine ⟨30534078430907224637819213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81424209149085932367517901 30534078430907224637819213)
      ·
        refine ⟨11450279411590209239182205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30534078430907224637819213 11450279411590209239182205)
        ·
          refine ⟨4293854779346328464693327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11450279411590209239182205 4293854779346328464693327)
          ·
            refine ⟨6440782169019492697039991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293854779346328464693327 6440782169019492697039991)
            ·
              refine ⟨9661173253529239045559987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440782169019492697039991 9661173253529239045559987)
              ·
                refine ⟨14491759880293858568339981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9661173253529239045559987 14491759880293858568339981)
                ·
                  refine ⟨5434409955110196963127493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14491759880293858568339981 5434409955110196963127493)
                  ·
                    refine ⟨1018951866583161930586405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434409955110196963127493 1018951866583161930586405)
                    ·
                      rfl

theorem cell23_5953205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_5953205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953205 prefixEnd_5953205 := by exact prefixLift 5953205
  have htrace : WordTrace (prefixWord ++ tailWord_5953205) baseStart_5953205 baseEnd_5953205 := by
    simpa [prefixWord, tailWord_5953205, baseEnd_5953205] using wordTrace_append hprefix tailTrace_5953205
  have hstable : (prefixWord ++ tailWord_5953205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953205).length < 2 ^ (prefixWord ++ tailWord_5953205).sum := by decide
  have hdescent : baseEnd_5953205 < baseStart_5953205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953227 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 5, 6]
def baseStart_5953227 : Nat := 118140960795 + 5953227 * 2 ^ 59
def prefixEnd_5953227 : Nat := 4983230072969 + 3 ^ 40 * 5953227 * 2
def baseEnd_5953227 : Nat := 1018955632107961568561371

theorem tailTrace_5953227 : CollatzResearch.WordTrace tailWord_5953227 prefixEnd_5953227 1018955632107961568561371 := by
  unfold tailWord_5953227
  simp only [CollatzResearch.WordTrace]
  refine ⟨217132026803482784070681935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144754684535655189380454623 217132026803482784070681935)
  ·
    refine ⟨325698040205224176106022903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217132026803482784070681935 325698040205224176106022903)
    ·
      refine ⟨488547060307836264159034355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325698040205224176106022903 488547060307836264159034355)
      ·
        refine ⟨732820590461754396238551533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488547060307836264159034355 732820590461754396238551533)
        ·
          refine ⟨274807721423157898589456825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732820590461754396238551533 274807721423157898589456825)
          ·
            refine ⟨206105791067368423942092619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274807721423157898589456825 206105791067368423942092619)
            ·
              refine ⟨309158686601052635913138929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206105791067368423942092619 309158686601052635913138929)
              ·
                refine ⟨231869014950789476934854197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309158686601052635913138929 231869014950789476934854197)
                ·
                  refine ⟨21737720151636513462642581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231869014950789476934854197 21737720151636513462642581)
                  ·
                    refine ⟨1018955632107961568561371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21737720151636513462642581 1018955632107961568561371)
                    ·
                      rfl

theorem cell23_5953227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_5953227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953227 prefixEnd_5953227 := by exact prefixLift 5953227
  have htrace : WordTrace (prefixWord ++ tailWord_5953227) baseStart_5953227 baseEnd_5953227 := by
    simpa [prefixWord, tailWord_5953227, baseEnd_5953227] using wordTrace_append hprefix tailTrace_5953227
  have hstable : (prefixWord ++ tailWord_5953227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953227).length < 2 ^ (prefixWord ++ tailWord_5953227).sum := by decide
  have hdescent : baseEnd_5953227 < baseStart_5953227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953278 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5953278 : Nat := 118140960795 + 5953278 * 2 ^ 59
def prefixEnd_5953278 : Nat := 4983230072969 + 3 ^ 40 * 5953278 * 2
def baseEnd_5953278 : Nat := 1018964361279088002048793

theorem tailTrace_5953278 : CollatzResearch.WordTrace tailWord_5953278 prefixEnd_5953278 1018964361279088002048793 := by
  unfold tailWord_5953278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27141735865787252472598561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144755924617532013187192325 27141735865787252472598561)
  ·
    refine ⟨20356301899340439354448921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27141735865787252472598561 20356301899340439354448921)
    ·
      refine ⟨15267226424505329515836691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20356301899340439354448921 15267226424505329515836691)
      ·
        refine ⟨22900839636757994273755037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15267226424505329515836691 22900839636757994273755037)
        ·
          refine ⟨8587814863784247852658139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22900839636757994273755037 8587814863784247852658139)
          ·
            refine ⟨12881722295676371778987209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8587814863784247852658139 12881722295676371778987209)
            ·
              refine ⟨9661291721757278834240407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12881722295676371778987209 9661291721757278834240407)
              ·
                refine ⟨14491937582635918251360611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9661291721757278834240407 14491937582635918251360611)
                ·
                  refine ⟨21737906373953877377040917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14491937582635918251360611 21737906373953877377040917)
                  ·
                    refine ⟨1018964361279088002048793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21737906373953877377040917 1018964361279088002048793)
                    ·
                      rfl

theorem cell23_5953278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5953278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953278 prefixEnd_5953278 := by exact prefixLift 5953278
  have htrace : WordTrace (prefixWord ++ tailWord_5953278) baseStart_5953278 baseEnd_5953278 := by
    simpa [prefixWord, tailWord_5953278, baseEnd_5953278] using wordTrace_append hprefix tailTrace_5953278
  have hstable : (prefixWord ++ tailWord_5953278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953278).length < 2 ^ (prefixWord ++ tailWord_5953278).sum := by decide
  have hdescent : baseEnd_5953278 < baseStart_5953278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953298 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5953298 : Nat := 118140960795 + 5953298 * 2 ^ 59
def prefixEnd_5953298 : Nat := 4983230072969 + 3 ^ 40 * 5953298 * 2
def baseEnd_5953298 : Nat := 3056903353450353927896287

theorem tailTrace_5953298 : CollatzResearch.WordTrace tailWord_5953298 prefixEnd_5953298 3056903353450353927896287 := by
  unfold tailWord_5953298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54283654096556390799129137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144756410924150375464344365 54283654096556390799129137)
  ·
    refine ⟨40712740572417293099346853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54283654096556390799129137 40712740572417293099346853)
    ·
      refine ⟨7633638857328242456127535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40712740572417293099346853 7633638857328242456127535)
      ·
        refine ⟨11450458285992363684191303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7633638857328242456127535 11450458285992363684191303)
        ·
          refine ⟨17175687428988545526286955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11450458285992363684191303 17175687428988545526286955)
          ·
            refine ⟨25763531143482818289430433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17175687428988545526286955 25763531143482818289430433)
            ·
              refine ⟨19322648357612113717072825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25763531143482818289430433 19322648357612113717072825)
              ·
                refine ⟨14491986268209085287804619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19322648357612113717072825 14491986268209085287804619)
                ·
                  refine ⟨21737979402313627931706929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14491986268209085287804619 21737979402313627931706929)
                  ·
                    refine ⟨16303484551735220948780197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21737979402313627931706929 16303484551735220948780197)
                    ·
                      refine ⟨3056903353450353927896287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16303484551735220948780197 3056903353450353927896287)
                      ·
                        rfl

theorem cell23_5953298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5953298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953298 prefixEnd_5953298 := by exact prefixLift 5953298
  have htrace : WordTrace (prefixWord ++ tailWord_5953298) baseStart_5953298 baseEnd_5953298 := by
    simpa [prefixWord, tailWord_5953298, baseEnd_5953298] using wordTrace_append hprefix tailTrace_5953298
  have hstable : (prefixWord ++ tailWord_5953298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953298).length < 2 ^ (prefixWord ++ tailWord_5953298).sum := by decide
  have hdescent : baseEnd_5953298 < baseStart_5953298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953301 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_5953301 : Nat := 118140960795 + 5953301 * 2 ^ 59
def prefixEnd_5953301 : Nat := 4983230072969 + 3 ^ 40 * 5953301 * 2
def baseEnd_5953301 : Nat := 3056904893892317416158773

theorem tailTrace_5953301 : CollatzResearch.WordTrace tailWord_5953301 prefixEnd_5953301 3056904893892317416158773 := by
  unfold tailWord_5953301
  simp only [CollatzResearch.WordTrace]
  refine ⟨217134725805214694708875757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144756483870143129805917171 217134725805214694708875757)
  ·
    refine ⟨81425522176955510515828409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217134725805214694708875757 81425522176955510515828409)
    ·
      refine ⟨61069141632716632886871307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81425522176955510515828409 61069141632716632886871307)
      ·
        refine ⟨91603712449074949330306961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61069141632716632886871307 91603712449074949330306961)
        ·
          refine ⟨68702784336806211997730221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91603712449074949330306961 68702784336806211997730221)
          ·
            refine ⟨25763544126302329499148833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68702784336806211997730221 25763544126302329499148833)
            ·
              refine ⟨19322658094726747124361625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25763544126302329499148833 19322658094726747124361625)
              ·
                refine ⟨14491993571045060343271219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19322658094726747124361625 14491993571045060343271219)
                ·
                  refine ⟨21737990356567590514906829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14491993571045060343271219 21737990356567590514906829)
                  ·
                    refine ⟨8151746383712846443090061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21737990356567590514906829 8151746383712846443090061)
                    ·
                      refine ⟨3056904893892317416158773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8151746383712846443090061 3056904893892317416158773)
                      ·
                        rfl

theorem cell23_5953301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_5953301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953301 prefixEnd_5953301 := by exact prefixLift 5953301
  have htrace : WordTrace (prefixWord ++ tailWord_5953301) baseStart_5953301 baseEnd_5953301 := by
    simpa [prefixWord, tailWord_5953301, baseEnd_5953301] using wordTrace_append hprefix tailTrace_5953301
  have hstable : (prefixWord ++ tailWord_5953301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953301).length < 2 ^ (prefixWord ++ tailWord_5953301).sum := by decide
  have hdescent : baseEnd_5953301 < baseStart_5953301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953361 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_5953361 : Nat := 118140960795 + 5953361 * 2 ^ 59
def prefixEnd_5953361 : Nat := 4983230072969 + 3 ^ 40 * 5953361 * 2
def baseEnd_5953361 : Nat := 3056935702731587181408497

theorem tailTrace_5953361 : CollatzResearch.WordTrace tailWord_5953361 prefixEnd_5953361 3056935702731587181408497 := by
  unfold tailWord_5953361
  simp only [CollatzResearch.WordTrace]
  refine ⟨217136914184997324956059937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144757942789998216637373291 217136914184997324956059937)
  ·
    refine ⟨162852685638747993717044953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217136914184997324956059937 162852685638747993717044953)
    ·
      refine ⟨122139514229060995287783715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162852685638747993717044953 122139514229060995287783715)
      ·
        refine ⟨183209271343591492931675573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122139514229060995287783715 183209271343591492931675573)
        ·
          refine ⟨17175869188461702462344585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183209271343591492931675573 17175869188461702462344585)
          ·
            refine ⟨12881901891346276846758439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17175869188461702462344585 12881901891346276846758439)
            ·
              refine ⟨19322852837019415270137659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12881901891346276846758439 19322852837019415270137659)
              ·
                refine ⟨28984279255529122905206489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19322852837019415270137659 28984279255529122905206489)
                ·
                  refine ⟨21738209441646842178904867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28984279255529122905206489 21738209441646842178904867)
                  ·
                    refine ⟨32607314162470263268357301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21738209441646842178904867 32607314162470263268357301)
                    ·
                      refine ⟨3056935702731587181408497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32607314162470263268357301 3056935702731587181408497)
                      ·
                        rfl

theorem cell23_5953361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_5953361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953361 prefixEnd_5953361 := by exact prefixLift 5953361
  have htrace : WordTrace (prefixWord ++ tailWord_5953361) baseStart_5953361 baseEnd_5953361 := by
    simpa [prefixWord, tailWord_5953361, baseEnd_5953361] using wordTrace_append hprefix tailTrace_5953361
  have hstable : (prefixWord ++ tailWord_5953361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953361).length < 2 ^ (prefixWord ++ tailWord_5953361).sum := by decide
  have hdescent : baseEnd_5953361 < baseStart_5953361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953386 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5953386 : Nat := 118140960795 + 5953386 * 2 ^ 59
def prefixEnd_5953386 : Nat := 4983230072969 + 3 ^ 40 * 5953386 * 2
def baseEnd_5953386 : Nat := 3056948539747949583595883

theorem tailTrace_5953386 : CollatzResearch.WordTrace tailWord_5953386 prefixEnd_5953386 3056948539747949583595883 := by
  unfold tailWord_5953386
  simp only [CollatzResearch.WordTrace]
  refine ⟨54284456502476688556430003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144758550673271169483813341 54284456502476688556430003)
  ·
    refine ⟨81426684753715032834645005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54284456502476688556430003 81426684753715032834645005)
    ·
      refine ⟨30535006782643137312991877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81426684753715032834645005 30535006782643137312991877)
      ·
        refine ⟨5725313771745588246185977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30535006782643137312991877 5725313771745588246185977)
        ·
          refine ⟨4293985328809191184639483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725313771745588246185977 4293985328809191184639483)
          ·
            refine ⟨6440977993213786776959225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293985328809191184639483 6440977993213786776959225)
            ·
              refine ⟨4830733494910340082719419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440977993213786776959225 4830733494910340082719419)
              ·
                refine ⟨7246100242365510124079129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830733494910340082719419 7246100242365510124079129)
                ·
                  refine ⟨5434575181774132593059347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7246100242365510124079129 5434575181774132593059347)
                  ·
                    refine ⟨8151862772661198889589021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5434575181774132593059347 8151862772661198889589021)
                    ·
                      refine ⟨3056948539747949583595883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8151862772661198889589021 3056948539747949583595883)
                      ·
                        rfl

theorem cell23_5953386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5953386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953386 prefixEnd_5953386 := by exact prefixLift 5953386
  have htrace : WordTrace (prefixWord ++ tailWord_5953386) baseStart_5953386 baseEnd_5953386 := by
    simpa [prefixWord, tailWord_5953386, baseEnd_5953386] using wordTrace_append hprefix tailTrace_5953386
  have hstable : (prefixWord ++ tailWord_5953386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953386).length < 2 ^ (prefixWord ++ tailWord_5953386).sum := by decide
  have hdescent : baseEnd_5953386 < baseStart_5953386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953411 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 2, 5]
def baseStart_5953411 : Nat := 118140960795 + 5953411 * 2 ^ 59
def prefixEnd_5953411 : Nat := 4983230072969 + 3 ^ 40 * 5953411 * 2
def baseEnd_5953411 : Nat := 1018987125588103995261089

theorem tailTrace_5953411 : CollatzResearch.WordTrace tailWord_5953411 prefixEnd_5953411 1018987125588103995261089 := by
  unfold tailWord_5953411
  simp only [CollatzResearch.WordTrace]
  refine ⟨217138737834816183495380087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144759158556544122330253391 217138737834816183495380087)
  ·
    refine ⟨325708106752224275243070131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217138737834816183495380087 325708106752224275243070131)
    ·
      refine ⟨488562160128336412864605197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325708106752224275243070131 488562160128336412864605197)
      ·
        refine ⟨183210810048126154824226949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488562160128336412864605197 183210810048126154824226949)
        ·
          refine ⟨34352026884023654029542553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183210810048126154824226949 34352026884023654029542553)
          ·
            refine ⟨25764020163017740522156915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34352026884023654029542553 25764020163017740522156915)
            ·
              refine ⟨38646030244526610783235373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25764020163017740522156915 38646030244526610783235373)
              ·
                refine ⟨14492261341697479043713265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38646030244526610783235373 14492261341697479043713265)
                ·
                  refine ⟨10869196006273109282784949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14492261341697479043713265 10869196006273109282784949)
                  ·
                    refine ⟨1018987125588103995261089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10869196006273109282784949 1018987125588103995261089)
                    ·
                      rfl

theorem cell23_5953411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 5].length) (baseStart_5953411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953411 prefixEnd_5953411 := by exact prefixLift 5953411
  have htrace : WordTrace (prefixWord ++ tailWord_5953411) baseStart_5953411 baseEnd_5953411 := by
    simpa [prefixWord, tailWord_5953411, baseEnd_5953411] using wordTrace_append hprefix tailTrace_5953411
  have hstable : (prefixWord ++ tailWord_5953411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953411).length < 2 ^ (prefixWord ++ tailWord_5953411).sum := by decide
  have hdescent : baseEnd_5953411 < baseStart_5953411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953428 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5953428 : Nat := 118140960795 + 5953428 * 2 ^ 59
def prefixEnd_5953428 : Nat := 4983230072969 + 3 ^ 40 * 5953428 * 2
def baseEnd_5953428 : Nat := 1018990035311812806423563

theorem tailTrace_5953428 : CollatzResearch.WordTrace tailWord_5953428 prefixEnd_5953428 1018990035311812806423563 := by
  unfold tailWord_5953428
  simp only [CollatzResearch.WordTrace]
  refine ⟨108569678937877297699374469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144759571917169730265832625 108569678937877297699374469)
  ·
    refine ⟨20356814800851993318632713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108569678937877297699374469 20356814800851993318632713)
    ·
      refine ⟨15267611100638994988974535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20356814800851993318632713 15267611100638994988974535)
      ·
        refine ⟨22901416650958492483461803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15267611100638994988974535 22901416650958492483461803)
        ·
          refine ⟨34352124976437738725192705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22901416650958492483461803 34352124976437738725192705)
          ·
            refine ⟨25764093732328304043894529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34352124976437738725192705 25764093732328304043894529)
            ·
              refine ⟨19323070299246228032920897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25764093732328304043894529 19323070299246228032920897)
              ·
                refine ⟨14492302724434671024690673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19323070299246228032920897 14492302724434671024690673)
                ·
                  refine ⟨10869227043326003268518005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14492302724434671024690673 10869227043326003268518005)
                  ·
                    refine ⟨1018990035311812806423563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10869227043326003268518005 1018990035311812806423563)
                    ·
                      rfl

theorem cell23_5953428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5953428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953428 prefixEnd_5953428 := by exact prefixLift 5953428
  have htrace : WordTrace (prefixWord ++ tailWord_5953428) baseStart_5953428 baseEnd_5953428 := by
    simpa [prefixWord, tailWord_5953428, baseEnd_5953428] using wordTrace_append hprefix tailTrace_5953428
  have hstable : (prefixWord ++ tailWord_5953428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953428).length < 2 ^ (prefixWord ++ tailWord_5953428).sum := by decide
  have hdescent : baseEnd_5953428 < baseStart_5953428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953508 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_5953508 : Nat := 118140960795 + 5953508 * 2 ^ 59
def prefixEnd_5953508 : Nat := 4983230072969 + 3 ^ 40 * 5953508 * 2
def baseEnd_5953508 : Nat := 3057011184387798106270321

theorem tailTrace_5953508 : CollatzResearch.WordTrace tailWord_5953508 prefixEnd_5953508 3057011184387798106270321 := by
  unfold tailWord_5953508
  simp only [CollatzResearch.WordTrace]
  refine ⟨108571137857732384530830589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144761517143643179374440785 108571137857732384530830589)
  ·
    refine ⟨40714176696649644199061471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108571137857732384530830589 40714176696649644199061471)
    ·
      refine ⟨61071265044974466298592207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40714176696649644199061471 61071265044974466298592207)
      ·
        refine ⟨91606897567461699447888311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61071265044974466298592207 91606897567461699447888311)
        ·
          refine ⟨137410346351192549171832467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91606897567461699447888311 137410346351192549171832467)
          ·
            refine ⟨206115519526788823757748701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137410346351192549171832467 206115519526788823757748701)
            ·
              refine ⟨77293319822545808909155763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206115519526788823757748701 77293319822545808909155763)
              ·
                refine ⟨115939979733818713363733645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77293319822545808909155763 115939979733818713363733645)
                ·
                  refine ⟨43477492400182017511400117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115939979733818713363733645 43477492400182017511400117)
                  ·
                    refine ⟨4076014912517064141693761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43477492400182017511400117 4076014912517064141693761)
                    ·
                      refine ⟨3057011184387798106270321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076014912517064141693761 3057011184387798106270321)
                      ·
                        rfl

theorem cell23_5953508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_5953508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953508 prefixEnd_5953508 := by exact prefixLift 5953508
  have htrace : WordTrace (prefixWord ++ tailWord_5953508) baseStart_5953508 baseEnd_5953508 := by
    simpa [prefixWord, tailWord_5953508, baseEnd_5953508] using wordTrace_append hprefix tailTrace_5953508
  have hstable : (prefixWord ++ tailWord_5953508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953508).length < 2 ^ (prefixWord ++ tailWord_5953508).sum := by decide
  have hdescent : baseEnd_5953508 < baseStart_5953508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953526 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_5953526 : Nat := 118140960795 + 5953526 * 2 ^ 59
def prefixEnd_5953526 : Nat := 4983230072969 + 3 ^ 40 * 5953526 * 2
def baseEnd_5953526 : Nat := 1019006809013193011948413

theorem tailTrace_5953526 : CollatzResearch.WordTrace tailWord_5953526 prefixEnd_5953526 1019006809013193011948413 := by
  unfold tailWord_5953526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571433264337472383488527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144761954819599705423877621 13571433264337472383488527)
  ·
    refine ⟨20357149896506208575232791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13571433264337472383488527 20357149896506208575232791)
    ·
      refine ⟨30535724844759312862849187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20357149896506208575232791 30535724844759312862849187)
      ·
        refine ⟨45803587267138969294273781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30535724844759312862849187 45803587267138969294273781)
        ·
          refine ⟨4294086306294278371338167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45803587267138969294273781 4294086306294278371338167)
          ·
            refine ⟨6441129459441417557007251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294086306294278371338167 6441129459441417557007251)
            ·
              refine ⟨9661694189162126335510877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441129459441417557007251 9661694189162126335510877)
              ·
                refine ⟨3623135320935797375816579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9661694189162126335510877 3623135320935797375816579)
                ·
                  refine ⟨5434702981403696063724869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623135320935797375816579 5434702981403696063724869)
                  ·
                    refine ⟨1019006809013193011948413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434702981403696063724869 1019006809013193011948413)
                    ·
                      rfl

theorem cell23_5953526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_5953526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953526 prefixEnd_5953526 := by exact prefixLift 5953526
  have htrace : WordTrace (prefixWord ++ tailWord_5953526) baseStart_5953526 baseEnd_5953526 := by
    simpa [prefixWord, tailWord_5953526, baseEnd_5953526] using wordTrace_append hprefix tailTrace_5953526
  have hstable : (prefixWord ++ tailWord_5953526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953526).length < 2 ^ (prefixWord ++ tailWord_5953526).sum := by decide
  have hdescent : baseEnd_5953526 < baseStart_5953526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953531 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 1, 6]
def baseStart_5953531 : Nat := 118140960795 + 5953531 * 2 ^ 59
def prefixEnd_5953531 : Nat := 4983230072969 + 3 ^ 40 * 5953531 * 2
def baseEnd_5953531 : Nat := 1019007664814283838760905

theorem tailTrace_5953531 : CollatzResearch.WordTrace tailWord_5953531 prefixEnd_5953531 1019007664814283838760905 := by
  unfold tailWord_5953531
  simp only [CollatzResearch.WordTrace]
  refine ⟨217143114594381443989748447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144762076396254295993165631 217143114594381443989748447)
  ·
    refine ⟨325714671891572165984622671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217143114594381443989748447 325714671891572165984622671)
    ·
      refine ⟨488572007837358248976934007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325714671891572165984622671 488572007837358248976934007)
      ·
        refine ⟨732858011756037373465401011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488572007837358248976934007 732858011756037373465401011)
        ·
          refine ⟨1099287017634056060198101517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732858011756037373465401011 1099287017634056060198101517)
          ·
            refine ⟨412232631612771022574288069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1099287017634056060198101517 412232631612771022574288069)
            ·
              refine ⟨77293618427394566732679013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 412232631612771022574288069 77293618427394566732679013)
              ·
                refine ⟨14492553455136481262377315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77293618427394566732679013 14492553455136481262377315)
                ·
                  refine ⟨21738830182704721893565973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14492553455136481262377315 21738830182704721893565973)
                  ·
                    refine ⟨1019007664814283838760905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21738830182704721893565973 1019007664814283838760905)
                    ·
                      rfl

theorem cell23_5953531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 6].length) (baseStart_5953531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953531 prefixEnd_5953531 := by exact prefixLift 5953531
  have htrace : WordTrace (prefixWord ++ tailWord_5953531) baseStart_5953531 baseEnd_5953531 := by
    simpa [prefixWord, tailWord_5953531, baseEnd_5953531] using wordTrace_append hprefix tailTrace_5953531
  have hstable : (prefixWord ++ tailWord_5953531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953531).length < 2 ^ (prefixWord ++ tailWord_5953531).sum := by decide
  have hdescent : baseEnd_5953531 < baseStart_5953531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953548 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_5953548 : Nat := 118140960795 + 5953548 * 2 ^ 59
def prefixEnd_5953548 : Nat := 4983230072969 + 3 ^ 40 * 5953548 * 2
def baseEnd_5953548 : Nat := 1019010574537992649923379

theorem tailTrace_5953548 : CollatzResearch.WordTrace tailWord_5953548 prefixEnd_5953548 1019010574537992649923379 := by
  unfold tailWord_5953548
  simp only [CollatzResearch.WordTrace]
  refine ⟨108571867317659927946558649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144762489756879903928744865 108571867317659927946558649)
  ·
    refine ⟨81428900488244945959918987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108571867317659927946558649 81428900488244945959918987)
    ·
      refine ⟨122143350732367418939878481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81428900488244945959918987 122143350732367418939878481)
      ·
        refine ⟨91607513049275564204908861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122143350732367418939878481 91607513049275564204908861)
        ·
          refine ⟨34352817393478336576840823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91607513049275564204908861 34352817393478336576840823)
          ·
            refine ⟨51529226090217504865261235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34352817393478336576840823 51529226090217504865261235)
            ·
              refine ⟨77293839135326257297891853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51529226090217504865261235 77293839135326257297891853)
              ·
                refine ⟨28985189675747346486709445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77293839135326257297891853 28985189675747346486709445)
                ·
                  refine ⟨5434723064202627466258021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28985189675747346486709445 5434723064202627466258021)
                  ·
                    refine ⟨1019010574537992649923379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434723064202627466258021 1019010574537992649923379)
                    ·
                      rfl

theorem cell23_5953548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_5953548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953548 prefixEnd_5953548 := by exact prefixLift 5953548
  have htrace : WordTrace (prefixWord ++ tailWord_5953548) baseStart_5953548 baseEnd_5953548 := by
    simpa [prefixWord, tailWord_5953548, baseEnd_5953548] using wordTrace_append hprefix tailTrace_5953548
  have hstable : (prefixWord ++ tailWord_5953548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953548).length < 2 ^ (prefixWord ++ tailWord_5953548).sum := by decide
  have hdescent : baseEnd_5953548 < baseStart_5953548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953556 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 6]
def baseStart_5953556 : Nat := 118140960795 + 5953556 * 2 ^ 59
def prefixEnd_5953556 : Nat := 4983230072969 + 3 ^ 40 * 5953556 * 2
def baseEnd_5953556 : Nat := 339670647939912657607789

theorem tailTrace_5953556 : CollatzResearch.WordTrace tailWord_5953556 prefixEnd_5953556 339670647939912657607789 := by
  unfold tailWord_5953556
  simp only [CollatzResearch.WordTrace]
  refine ⟨108572013209645436629704261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144762684279527248839605681 108572013209645436629704261)
  ·
    refine ⟨20357252476808519368069549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108572013209645436629704261 20357252476808519368069549)
    ·
      refine ⟨7633969678803194763026081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20357252476808519368069549 7633969678803194763026081)
      ·
        refine ⟨5725477259102396072269561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7633969678803194763026081 5725477259102396072269561)
        ·
          refine ⟨4294107944326797054202171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725477259102396072269561 4294107944326797054202171)
          ·
            refine ⟨6441161916490195581303257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294107944326797054202171 6441161916490195581303257)
            ·
              refine ⟨4830871437367646685977443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6441161916490195581303257 4830871437367646685977443)
              ·
                refine ⟨7246307156051470028966165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830871437367646685977443 7246307156051470028966165)
                ·
                  refine ⟨339670647939912657607789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7246307156051470028966165 339670647939912657607789)
                  ·
                    rfl

theorem cell23_5953556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_5953556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953556 prefixEnd_5953556 := by exact prefixLift 5953556
  have htrace : WordTrace (prefixWord ++ tailWord_5953556) baseStart_5953556 baseEnd_5953556 := by
    simpa [prefixWord, tailWord_5953556, baseEnd_5953556] using wordTrace_append hprefix tailTrace_5953556
  have hstable : (prefixWord ++ tailWord_5953556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953556).length < 2 ^ (prefixWord ++ tailWord_5953556).sum := by decide
  have hdescent : baseEnd_5953556 < baseStart_5953556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953578 : List Nat := [3, 1, 4, 1, 2, 1, 2, 9]
def baseStart_5953578 : Nat := 118140960795 + 5953578 * 2 ^ 59
def prefixEnd_5953578 : Nat := 4983230072969 + 3 ^ 40 * 5953578 * 2
def baseEnd_5953578 : Nat := 113223967704948623422037

theorem tailTrace_5953578 : CollatzResearch.WordTrace tailWord_5953578 prefixEnd_5953578 113223967704948623422037 := by
  unfold tailWord_5953578
  simp only [CollatzResearch.WordTrace]
  refine ⟨54286207206302792754177347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144763219216807447344472925 54286207206302792754177347)
  ·
    refine ⟨81429310809454189131266021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54286207206302792754177347 81429310809454189131266021)
    ·
      refine ⟨15267995776772660462112379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81429310809454189131266021 15267995776772660462112379)
      ·
        refine ⟨22901993665158990693168569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15267995776772660462112379 22901993665158990693168569)
        ·
          refine ⟨17176495248869243019876427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22901993665158990693168569 17176495248869243019876427)
          ·
            refine ⟨25764742873303864529814641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17176495248869243019876427 25764742873303864529814641)
            ·
              refine ⟨19323557154977898397360981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25764742873303864529814641 19323557154977898397360981)
              ·
                refine ⟨113223967704948623422037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19323557154977898397360981 113223967704948623422037)
                ·
                  rfl

theorem cell23_5953578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_5953578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953578 prefixEnd_5953578 := by exact prefixLift 5953578
  have htrace : WordTrace (prefixWord ++ tailWord_5953578) baseStart_5953578 baseEnd_5953578 := by
    simpa [prefixWord, tailWord_5953578, baseEnd_5953578] using wordTrace_append hprefix tailTrace_5953578
  have hstable : (prefixWord ++ tailWord_5953578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953578).length < 2 ^ (prefixWord ++ tailWord_5953578).sum := by decide
  have hdescent : baseEnd_5953578 < baseStart_5953578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953592 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 1, 1, 5]
def baseStart_5953592 : Nat := 118140960795 + 5953592 * 2 ^ 59
def prefixEnd_5953592 : Nat := 4983230072969 + 3 ^ 40 * 5953592 * 2
def baseEnd_5953592 : Nat := 3057054316762775777619935

theorem tailTrace_5953592 : CollatzResearch.WordTrace tailWord_5953592 prefixEnd_5953592 3057054316762775777619935 := by
  unfold tailWord_5953592
  simp only [CollatzResearch.WordTrace]
  refine ⟨108572669723580225703859515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144763559631440300938479353 108572669723580225703859515)
  ·
    refine ⟨162859004585370338555789273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108572669723580225703859515 162859004585370338555789273)
    ·
      refine ⟨122144253439027753916841955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162859004585370338555789273 122144253439027753916841955)
      ·
        refine ⟨183216380158541630875262933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122144253439027753916841955 183216380158541630875262933)
        ·
          refine ⟨4294133909965819473638975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 183216380158541630875262933 4294133909965819473638975)
          ·
            refine ⟨6441200864948729210458463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294133909965819473638975 6441200864948729210458463)
            ·
              refine ⟨9661801297423093815687695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441200864948729210458463 9661801297423093815687695)
              ·
                refine ⟨14492701946134640723531543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9661801297423093815687695 14492701946134640723531543)
                ·
                  refine ⟨21739052919201961085297315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14492701946134640723531543 21739052919201961085297315)
                  ·
                    refine ⟨32608579378802941627945973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21739052919201961085297315 32608579378802941627945973)
                    ·
                      refine ⟨3057054316762775777619935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32608579378802941627945973 3057054316762775777619935)
                      ·
                        rfl

theorem cell23_5953592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_5953592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953592 prefixEnd_5953592 := by exact prefixLift 5953592
  have htrace : WordTrace (prefixWord ++ tailWord_5953592) baseStart_5953592 baseEnd_5953592 := by
    simpa [prefixWord, tailWord_5953592, baseEnd_5953592] using wordTrace_append hprefix tailTrace_5953592
  have hstable : (prefixWord ++ tailWord_5953592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953592).length < 2 ^ (prefixWord ++ tailWord_5953592).sum := by decide
  have hdescent : baseEnd_5953592 < baseStart_5953592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953730 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5953730 : Nat := 118140960795 + 5953730 * 2 ^ 59
def prefixEnd_5953730 : Nat := 4983230072969 + 3 ^ 40 * 5953730 * 2
def baseEnd_5953730 : Nat := 3057125177093096237694301

theorem tailTrace_5953730 : CollatzResearch.WordTrace tailWord_5953730 prefixEnd_5953730 3057125177093096237694301 := by
  unfold tailWord_5953730
  simp only [CollatzResearch.WordTrace]
  refine ⟨54287593180165125244060661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144766915147107000650828429 54287593180165125244060661)
  ·
    refine ⟨5089461860640480491630687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54287593180165125244060661 5089461860640480491630687)
    ·
      refine ⟨7634192790960720737446031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5089461860640480491630687 7634192790960720737446031)
      ·
        refine ⟨11451289186441081106169047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7634192790960720737446031 11451289186441081106169047)
        ·
          refine ⟨17176933779661621659253571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11451289186441081106169047 17176933779661621659253571)
          ·
            refine ⟨25765400669492432488880357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17176933779661621659253571 25765400669492432488880357)
            ·
              refine ⟨4831012625529831091665067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25765400669492432488880357 4831012625529831091665067)
              ·
                refine ⟨7246518938294746637497601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831012625529831091665067 7246518938294746637497601)
                ·
                  refine ⟨5434889203721059978123201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7246518938294746637497601 5434889203721059978123201)
                  ·
                    refine ⟨4076166902790794983592401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5434889203721059978123201 4076166902790794983592401)
                    ·
                      refine ⟨3057125177093096237694301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076166902790794983592401 3057125177093096237694301)
                      ·
                        rfl

theorem cell23_5953730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5953730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953730 prefixEnd_5953730 := by exact prefixLift 5953730
  have htrace : WordTrace (prefixWord ++ tailWord_5953730) baseStart_5953730 baseEnd_5953730 := by
    simpa [prefixWord, tailWord_5953730, baseEnd_5953730] using wordTrace_append hprefix tailTrace_5953730
  have hstable : (prefixWord ++ tailWord_5953730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953730).length < 2 ^ (prefixWord ++ tailWord_5953730).sum := by decide
  have hdescent : baseEnd_5953730 < baseStart_5953730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953745 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 3, 4]
def baseStart_5953745 : Nat := 118140960795 + 5953745 * 2 ^ 59
def prefixEnd_5953745 : Nat := 4983230072969 + 3 ^ 40 * 5953745 * 2
def baseEnd_5953745 : Nat := 1019044293100971226335577

theorem tailTrace_5953745 : CollatzResearch.WordTrace tailWord_5953745 prefixEnd_5953745 1019044293100971226335577 := by
  unfold tailWord_5953745
  simp only [CollatzResearch.WordTrace]
  refine ⟨217150919815606158538038689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144767279877070772358692459 217150919815606158538038689)
  ·
    refine ⟨162863189861704618903529017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217150919815606158538038689 162863189861704618903529017)
    ·
      refine ⟨122147392396278464177646763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162863189861704618903529017 122147392396278464177646763)
      ·
        refine ⟨183221088594417696266470145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122147392396278464177646763 183221088594417696266470145)
        ·
          refine ⟨137415816445813272199852609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183221088594417696266470145 137415816445813272199852609)
          ·
            refine ⟨103061862334359954149889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137415816445813272199852609 103061862334359954149889457)
            ·
              refine ⟨77296396750769965612417093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103061862334359954149889457 77296396750769965612417093)
              ·
                refine ⟨14493074390769368552328205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77296396750769965612417093 14493074390769368552328205)
                ·
                  refine ⟨5434902896538513207123077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14493074390769368552328205 5434902896538513207123077)
                  ·
                    refine ⟨1019044293100971226335577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5434902896538513207123077 1019044293100971226335577)
                    ·
                      rfl

theorem cell23_5953745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_5953745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953745 prefixEnd_5953745 := by exact prefixLift 5953745
  have htrace : WordTrace (prefixWord ++ tailWord_5953745) baseStart_5953745 baseEnd_5953745 := by
    simpa [prefixWord, tailWord_5953745, baseEnd_5953745] using wordTrace_append hprefix tailTrace_5953745
  have hstable : (prefixWord ++ tailWord_5953745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953745).length < 2 ^ (prefixWord ++ tailWord_5953745).sum := by decide
  have hdescent : baseEnd_5953745 < baseStart_5953745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953752 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_5953752 : Nat := 118140960795 + 5953752 * 2 ^ 59
def prefixEnd_5953752 : Nat := 4983230072969 + 3 ^ 40 * 5953752 * 2
def baseEnd_5953752 : Nat := 3057136473667495151619199

theorem tailTrace_5953752 : CollatzResearch.WordTrace tailWord_5953752 prefixEnd_5953752 3057136473667495151619199 := by
  unfold tailWord_5953752
  simp only [CollatzResearch.WordTrace]
  refine ⟨108575587563290399366771755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144767450084387199155695673 108575587563290399366771755)
  ·
    refine ⟨162863381344935599050157633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108575587563290399366771755 162863381344935599050157633)
    ·
      refine ⟨122147536008701699287618225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162863381344935599050157633 122147536008701699287618225)
      ·
        refine ⟨91610652006526274465713669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122147536008701699287618225 91610652006526274465713669)
        ·
          refine ⟨17176997251223676462321313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91610652006526274465713669 17176997251223676462321313)
          ·
            refine ⟨12882747938417757346740985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17176997251223676462321313 12882747938417757346740985)
            ·
              refine ⟨9662060953813318010055739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12882747938417757346740985 9662060953813318010055739)
              ·
                refine ⟨14493091430719977015083609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9662060953813318010055739 14493091430719977015083609)
                ·
                  refine ⟨10869818573039982761312707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14493091430719977015083609 10869818573039982761312707)
                  ·
                    refine ⟨16304727859559974141969061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10869818573039982761312707 16304727859559974141969061)
                    ·
                      refine ⟨3057136473667495151619199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16304727859559974141969061 3057136473667495151619199)
                      ·
                        rfl

theorem cell23_5953752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_5953752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953752 prefixEnd_5953752 := by exact prefixLift 5953752
  have htrace : WordTrace (prefixWord ++ tailWord_5953752) baseStart_5953752 baseEnd_5953752 := by
    simpa [prefixWord, tailWord_5953752, baseEnd_5953752] using wordTrace_append hprefix tailTrace_5953752
  have hstable : (prefixWord ++ tailWord_5953752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953752).length < 2 ^ (prefixWord ++ tailWord_5953752).sum := by decide
  have hdescent : baseEnd_5953752 < baseStart_5953752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953755 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 3]
def baseStart_5953755 : Nat := 118140960795 + 5953755 * 2 ^ 59
def prefixEnd_5953755 : Nat := 4983230072969 + 3 ^ 40 * 5953755 * 2
def baseEnd_5953755 : Nat := 3057138014109458639881685

theorem tailTrace_5953755 : CollatzResearch.WordTrace tailWord_5953755 prefixEnd_5953755 3057138014109458639881685 := by
  unfold tailWord_5953755
  simp only [CollatzResearch.WordTrace]
  refine ⟨217151284545569930245902719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144767523030379953497268479 217151284545569930245902719)
  ·
    refine ⟨325726926818354895368854079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217151284545569930245902719 325726926818354895368854079)
    ·
      refine ⟨488590390227532343053281119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325726926818354895368854079 488590390227532343053281119)
      ·
        refine ⟨732885585341298514579921679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488590390227532343053281119 732885585341298514579921679)
        ·
          refine ⟨1099328378011947771869882519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732885585341298514579921679 1099328378011947771869882519)
          ·
            refine ⟨1648992567017921657804823779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099328378011947771869882519 1648992567017921657804823779)
            ·
              refine ⟨2473488850526882486707235669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648992567017921657804823779 2473488850526882486707235669)
              ·
                refine ⟨14493098733555952070550209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2473488850526882486707235669 14493098733555952070550209)
                ·
                  refine ⟨10869824050166964052912657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14493098733555952070550209 10869824050166964052912657)
                  ·
                    refine ⟨8152368037625223039684493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10869824050166964052912657 8152368037625223039684493)
                    ·
                      refine ⟨3057138014109458639881685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8152368037625223039684493 3057138014109458639881685)
                      ·
                        rfl

theorem cell23_5953755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 3].length) (baseStart_5953755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953755 prefixEnd_5953755 := by exact prefixLift 5953755
  have htrace : WordTrace (prefixWord ++ tailWord_5953755) baseStart_5953755 baseEnd_5953755 := by
    simpa [prefixWord, tailWord_5953755, baseEnd_5953755] using wordTrace_append hprefix tailTrace_5953755
  have hstable : (prefixWord ++ tailWord_5953755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953755).length < 2 ^ (prefixWord ++ tailWord_5953755).sum := by decide
  have hdescent : baseEnd_5953755 < baseStart_5953755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953775 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 6]
def baseStart_5953775 : Nat := 118140960795 + 5953775 * 2 ^ 59
def prefixEnd_5953775 : Nat := 4983230072969 + 3 ^ 40 * 5953775 * 2
def baseEnd_5953775 : Nat := 339683142635838729070177

theorem tailTrace_5953775 : CollatzResearch.WordTrace tailWord_5953775 prefixEnd_5953775 339683142635838729070177 := by
  unfold tailWord_5953775
  simp only [CollatzResearch.WordTrace]
  refine ⟨217152014005497473661630779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144768009336998315774420519 217152014005497473661630779)
  ·
    refine ⟨325728021008246210492446169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217152014005497473661630779 325728021008246210492446169)
    ·
      refine ⟨244296015756184657869334627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325728021008246210492446169 244296015756184657869334627)
      ·
        refine ⟨366444023634276986804001941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244296015756184657869334627 366444023634276986804001941)
        ·
          refine ⟨17177063607856733756437591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 366444023634276986804001941 17177063607856733756437591)
          ·
            refine ⟨25765595411785100634656387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17177063607856733756437591 25765595411785100634656387)
            ·
              refine ⟨38648393117677650951984581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25765595411785100634656387 38648393117677650951984581)
              ·
                refine ⟨7246573709564559553497109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38648393117677650951984581 7246573709564559553497109)
                ·
                  refine ⟨339683142635838729070177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7246573709564559553497109 339683142635838729070177)
                  ·
                    rfl

theorem cell23_5953775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 6].length) (baseStart_5953775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953775 prefixEnd_5953775 := by exact prefixLift 5953775
  have htrace : WordTrace (prefixWord ++ tailWord_5953775) baseStart_5953775 baseEnd_5953775 := by
    simpa [prefixWord, tailWord_5953775, baseEnd_5953775] using wordTrace_append hprefix tailTrace_5953775
  have hstable : (prefixWord ++ tailWord_5953775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953775).length < 2 ^ (prefixWord ++ tailWord_5953775).sum := by decide
  have hdescent : baseEnd_5953775 < baseStart_5953775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953802 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_5953802 : Nat := 118140960795 + 5953802 * 2 ^ 59
def prefixEnd_5953802 : Nat := 4983230072969 + 3 ^ 40 * 5953802 * 2
def baseEnd_5953802 : Nat := 3057162147700219955993969

theorem tailTrace_5953802 : CollatzResearch.WordTrace tailWord_5953802 prefixEnd_5953802 3057162147700219955993969 := by
  unfold tailWord_5953802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54288249694099914318215915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144768665850933104848575773 54288249694099914318215915)
  ·
    refine ⟨81432374541149871477323873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54288249694099914318215915 81432374541149871477323873)
    ·
      refine ⟨61074280905862403607992905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81432374541149871477323873 61074280905862403607992905)
      ·
        refine ⟨45805710679396802705994679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61074280905862403607992905 45805710679396802705994679)
        ·
          refine ⟨68708566019095204058992019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45805710679396802705994679 68708566019095204058992019)
          ·
            refine ⟨103062849028642806088488029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68708566019095204058992019 103062849028642806088488029)
            ·
              refine ⟨38648568385741052283183011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103062849028642806088488029 38648568385741052283183011)
              ·
                refine ⟨57972852578611578424774517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38648568385741052283183011 57972852578611578424774517)
                ·
                  refine ⟨5434954929244835477322611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57972852578611578424774517 5434954929244835477322611)
                  ·
                    refine ⟨8152432393867253215983917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5434954929244835477322611 8152432393867253215983917)
                    ·
                      refine ⟨3057162147700219955993969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8152432393867253215983917 3057162147700219955993969)
                      ·
                        rfl

theorem cell23_5953802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_5953802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953802 prefixEnd_5953802 := by exact prefixLift 5953802
  have htrace : WordTrace (prefixWord ++ tailWord_5953802) baseStart_5953802 baseEnd_5953802 := by
    simpa [prefixWord, tailWord_5953802, baseEnd_5953802] using wordTrace_append hprefix tailTrace_5953802
  have hstable : (prefixWord ++ tailWord_5953802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953802).length < 2 ^ (prefixWord ++ tailWord_5953802).sum := by decide
  have hdescent : baseEnd_5953802 < baseStart_5953802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953819 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 1, 1, 3]
def baseStart_5953819 : Nat := 118140960795 + 5953819 * 2 ^ 59
def prefixEnd_5953819 : Nat := 4983230072969 + 3 ^ 40 * 5953819 * 2
def baseEnd_5953819 : Nat := 3057170876871346389481391

theorem tailTrace_5953819 : CollatzResearch.WordTrace tailWord_5953819 prefixEnd_5953819 3057170876871346389481391 := by
  unfold tailWord_5953819
  simp only [CollatzResearch.WordTrace]
  refine ⟨217153618817338069176232511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144769079211558712784155007 217153618817338069176232511)
  ·
    refine ⟨325730428226007103764348767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217153618817338069176232511 325730428226007103764348767)
    ·
      refine ⟨488595642339010655646523151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325730428226007103764348767 488595642339010655646523151)
      ·
        refine ⟨732893463508515983469784727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488595642339010655646523151 732893463508515983469784727)
        ·
          refine ⟨1099340195262773975204677091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732893463508515983469784727 1099340195262773975204677091)
          ·
            refine ⟨1649010292894160962807015637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099340195262773975204677091 1649010292894160962807015637)
            ·
              refine ⟨38648678739706897565789429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1649010292894160962807015637 38648678739706897565789429)
              ·
                refine ⟨3623313631847521646792759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38648678739706897565789429 3623313631847521646792759)
                ·
                  refine ⟨5434970447771282470189139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623313631847521646792759 5434970447771282470189139)
                  ·
                    refine ⟨8152455671656923705283709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5434970447771282470189139 8152455671656923705283709)
                    ·
                      refine ⟨3057170876871346389481391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8152455671656923705283709 3057170876871346389481391)
                      ·
                        rfl

theorem cell23_5953819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 1, 3].length) (baseStart_5953819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953819 prefixEnd_5953819 := by exact prefixLift 5953819
  have htrace : WordTrace (prefixWord ++ tailWord_5953819) baseStart_5953819 baseEnd_5953819 := by
    simpa [prefixWord, tailWord_5953819, baseEnd_5953819] using wordTrace_append hprefix tailTrace_5953819
  have hstable : (prefixWord ++ tailWord_5953819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953819).length < 2 ^ (prefixWord ++ tailWord_5953819).sum := by decide
  have hdescent : baseEnd_5953819 < baseStart_5953819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953855 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_5953855 : Nat := 118140960795 + 5953855 * 2 ^ 59
def prefixEnd_5953855 : Nat := 4983230072969 + 3 ^ 40 * 5953855 * 2
def baseEnd_5953855 : Nat := 3057189362174908248631225

theorem tailTrace_5953855 : CollatzResearch.WordTrace tailWord_5953855 prefixEnd_5953855 3057189362174908248631225 := by
  unfold tailWord_5953855
  simp only [CollatzResearch.WordTrace]
  refine ⟨217154931845207647324543019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144769954563471764883028679 217154931845207647324543019)
  ·
    refine ⟨325732397767811470986814529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217154931845207647324543019 325732397767811470986814529)
    ·
      refine ⟨244299298325858603240110897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325732397767811470986814529 244299298325858603240110897)
      ·
        refine ⟨183224473744393952430083173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244299298325858603240110897 183224473744393952430083173)
        ·
          refine ⟨34354588827073866080640595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183224473744393952430083173 34354588827073866080640595)
          ·
            refine ⟨51531883240610799120960893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34354588827073866080640595 51531883240610799120960893)
            ·
              refine ⟨19324456215229049670360335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51531883240610799120960893 19324456215229049670360335)
              ·
                refine ⟨28986684322843574505540503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19324456215229049670360335 28986684322843574505540503)
                ·
                  refine ⟨43480026484265361758310755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28986684322843574505540503 43480026484265361758310755)
                  ·
                    refine ⟨65220039726398042637466133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43480026484265361758310755 65220039726398042637466133)
                    ·
                      refine ⟨3057189362174908248631225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65220039726398042637466133 3057189362174908248631225)
                      ·
                        rfl

theorem cell23_5953855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_5953855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953855 prefixEnd_5953855 := by exact prefixLift 5953855
  have htrace : WordTrace (prefixWord ++ tailWord_5953855) baseStart_5953855 baseEnd_5953855 := by
    simpa [prefixWord, tailWord_5953855, baseEnd_5953855] using wordTrace_append hprefix tailTrace_5953855
  have hstable : (prefixWord ++ tailWord_5953855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953855).length < 2 ^ (prefixWord ++ tailWord_5953855).sum := by decide
  have hdescent : baseEnd_5953855 < baseStart_5953855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953859 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 3, 2, 2]
def baseStart_5953859 : Nat := 118140960795 + 5953859 * 2 ^ 59
def prefixEnd_5953859 : Nat := 4983230072969 + 3 ^ 40 * 5953859 * 2
def baseEnd_5953859 : Nat := 3057191416097526232981207

theorem tailTrace_5953859 : CollatzResearch.WordTrace tailWord_5953859 prefixEnd_5953859 3057191416097526232981207 := by
  unfold tailWord_5953859
  simp only [CollatzResearch.WordTrace]
  refine ⟨217155077737193156007688631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144770051824795437338459087 217155077737193156007688631)
  ·
    refine ⟨325732616605789734011532947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217155077737193156007688631 325732616605789734011532947)
    ·
      refine ⟨488598924908684601017299421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325732616605789734011532947 488598924908684601017299421)
      ·
        refine ⟨183224596840756725381487283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488598924908684601017299421 183224596840756725381487283)
        ·
          refine ⟨274836895261135088072230925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183224596840756725381487283 274836895261135088072230925)
          ·
            refine ⟨103063835722925658027086597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274836895261135088072230925 103063835722925658027086597)
            ·
              refine ⟨19324469198048560880078737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103063835722925658027086597 19324469198048560880078737)
              ·
                refine ⟨14493351898536420660059053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19324469198048560880078737 14493351898536420660059053)
                ·
                  refine ⟨5435006961951157747522145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14493351898536420660059053 5435006961951157747522145)
                  ·
                    refine ⟨4076255221463368310641609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5435006961951157747522145 4076255221463368310641609)
                    ·
                      refine ⟨3057191416097526232981207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076255221463368310641609 3057191416097526232981207)
                      ·
                        rfl

theorem cell23_5953859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_5953859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953859 prefixEnd_5953859 := by exact prefixLift 5953859
  have htrace : WordTrace (prefixWord ++ tailWord_5953859) baseStart_5953859 baseEnd_5953859 := by
    simpa [prefixWord, tailWord_5953859, baseEnd_5953859] using wordTrace_append hprefix tailTrace_5953859
  have hstable : (prefixWord ++ tailWord_5953859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953859).length < 2 ^ (prefixWord ++ tailWord_5953859).sum := by decide
  have hdescent : baseEnd_5953859 < baseStart_5953859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953910 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5953910 : Nat := 118140960795 + 5953910 * 2 ^ 59
def prefixEnd_5953910 : Nat := 4983230072969 + 3 ^ 40 * 5953910 * 2
def baseEnd_5953910 : Nat := 3057217603610905533443473

theorem tailTrace_5953910 : CollatzResearch.WordTrace tailWord_5953910 prefixEnd_5953910 3057217603610905533443473 := by
  unfold tailWord_5953910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572308616250524482362199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144771291906672261145196789 13572308616250524482362199)
  ·
    refine ⟨20358462924375786723543299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13572308616250524482362199 20358462924375786723543299)
    ·
      refine ⟨30537694386563680085314949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20358462924375786723543299 30537694386563680085314949)
      ·
        refine ⟨5725817697480690015996553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30537694386563680085314949 5725817697480690015996553)
        ·
          refine ⟨4294363273110517511997415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725817697480690015996553 4294363273110517511997415)
          ·
            refine ⟨6441544909665776267996123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294363273110517511997415 6441544909665776267996123)
            ·
              refine ⟨9662317364498664401994185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441544909665776267996123 9662317364498664401994185)
              ·
                refine ⟨7246738023373998301495639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9662317364498664401994185 7246738023373998301495639)
                ·
                  refine ⟨10870107035060997452243459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7246738023373998301495639 10870107035060997452243459)
                  ·
                    refine ⟨16305160552591496178365189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10870107035060997452243459 16305160552591496178365189)
                    ·
                      refine ⟨3057217603610905533443473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16305160552591496178365189 3057217603610905533443473)
                      ·
                        rfl

theorem cell23_5953910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5953910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953910 prefixEnd_5953910 := by exact prefixLift 5953910
  have htrace : WordTrace (prefixWord ++ tailWord_5953910) baseStart_5953910 baseEnd_5953910 := by
    simpa [prefixWord, tailWord_5953910, baseEnd_5953910] using wordTrace_append hprefix tailTrace_5953910
  have hstable : (prefixWord ++ tailWord_5953910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953910).length < 2 ^ (prefixWord ++ tailWord_5953910).sum := by decide
  have hdescent : baseEnd_5953910 < baseStart_5953910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953925 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_5953925 : Nat := 118140960795 + 5953925 * 2 ^ 59
def prefixEnd_5953925 : Nat := 4983230072969 + 3 ^ 40 * 5953925 * 2
def baseEnd_5953925 : Nat := 1019075101940240991585301

theorem tailTrace_5953925 : CollatzResearch.WordTrace tailWord_5953925 prefixEnd_5953925 1019075101940240991585301 := by
  unfold tailWord_5953925
  simp only [CollatzResearch.WordTrace]
  refine ⟨217157484954954049279591229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144771656636636032853060819 217157484954954049279591229)
  ·
    refine ⟨81434056858107768479846711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217157484954954049279591229 81434056858107768479846711)
    ·
      refine ⟨122151085287161652719770067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81434056858107768479846711 122151085287161652719770067)
      ·
        refine ⟨183226627930742479079655101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122151085287161652719770067 183226627930742479079655101)
        ·
          refine ⟨68709985474028429654870663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183226627930742479079655101 68709985474028429654870663)
          ·
            refine ⟨103064978211042644482305995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68709985474028429654870663 103064978211042644482305995)
            ·
              refine ⟨154597467316563966723458993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103064978211042644482305995 154597467316563966723458993)
              ·
                refine ⟨115948100487422975042594245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154597467316563966723458993 115948100487422975042594245)
                ·
                  refine ⟨21740268841391807820486421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115948100487422975042594245 21740268841391807820486421)
                  ·
                    refine ⟨1019075101940240991585301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21740268841391807820486421 1019075101940240991585301)
                    ·
                      rfl

theorem cell23_5953925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_5953925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953925 prefixEnd_5953925 := by exact prefixLift 5953925
  have htrace : WordTrace (prefixWord ++ tailWord_5953925) baseStart_5953925 baseEnd_5953925 := by
    simpa [prefixWord, tailWord_5953925, baseEnd_5953925] using wordTrace_append hprefix tailTrace_5953925
  have hstable : (prefixWord ++ tailWord_5953925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953925).length < 2 ^ (prefixWord ++ tailWord_5953925).sum := by decide
  have hdescent : baseEnd_5953925 < baseStart_5953925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5953952 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_5953952 : Nat := 118140960795 + 5953952 * 2 ^ 59
def prefixEnd_5953952 : Nat := 4983230072969 + 3 ^ 40 * 5953952 * 2
def baseEnd_5953952 : Nat := 3057239169798394369118279

theorem tailTrace_5953952 : CollatzResearch.WordTrace tailWord_5953952 prefixEnd_5953952 3057239169798394369118279 := by
  unfold tailWord_5953952
  simp only [CollatzResearch.WordTrace]
  refine ⟨108579234862928116445412055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144772313150570821927216073 108579234862928116445412055)
  ·
    refine ⟨162868852294392174668118083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108579234862928116445412055 162868852294392174668118083)
    ·
      refine ⟨244303278441588262002177125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162868852294392174668118083 244303278441588262002177125)
      ·
        refine ⟨45806864707797799125408211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244303278441588262002177125 45806864707797799125408211)
        ·
          refine ⟨68710297061696698688112317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45806864707797799125408211 68710297061696698688112317)
          ·
            refine ⟨25766361398136262008042119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68710297061696698688112317 25766361398136262008042119)
            ·
              refine ⟨38649542097204393012063179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25766361398136262008042119 38649542097204393012063179)
              ·
                refine ⟨57974313145806589518094769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38649542097204393012063179 57974313145806589518094769)
                ·
                  refine ⟨43480734859354942138571077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57974313145806589518094769 43480734859354942138571077)
                  ·
                    refine ⟨8152637786129051650982077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43480734859354942138571077 8152637786129051650982077)
                    ·
                      refine ⟨3057239169798394369118279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8152637786129051650982077 3057239169798394369118279)
                      ·
                        rfl

theorem cell23_5953952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_5953952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5953952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5953952 prefixEnd_5953952 := by exact prefixLift 5953952
  have htrace : WordTrace (prefixWord ++ tailWord_5953952) baseStart_5953952 baseEnd_5953952 := by
    simpa [prefixWord, tailWord_5953952, baseEnd_5953952] using wordTrace_append hprefix tailTrace_5953952
  have hstable : (prefixWord ++ tailWord_5953952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5953952).length < 2 ^ (prefixWord ++ tailWord_5953952).sum := by decide
  have hdescent : baseEnd_5953952 < baseStart_5953952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5953952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954006 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_5954006 : Nat := 118140960795 + 5954006 * 2 ^ 59
def prefixEnd_5954006 : Nat := 4983230072969 + 3 ^ 40 * 5954006 * 2
def baseEnd_5954006 : Nat := 339696321972637461982559

theorem tailTrace_5954006 : CollatzResearch.WordTrace tailWord_5954006 prefixEnd_5954006 339696321972637461982559 := by
  unfold tailWord_5954006
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572527454228787507080617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144773626178440400075526581 13572527454228787507080617)
  ·
    refine ⟨10179395590671590630310463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13572527454228787507080617 10179395590671590630310463)
    ·
      refine ⟨15269093386007385945465695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10179395590671590630310463 15269093386007385945465695)
      ·
        refine ⟨22903640079011078918198543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15269093386007385945465695 22903640079011078918198543)
        ·
          refine ⟨34355460118516618377297815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22903640079011078918198543 34355460118516618377297815)
          ·
            refine ⟨51533190177774927565946723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34355460118516618377297815 51533190177774927565946723)
            ·
              refine ⟨77299785266662391348920085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51533190177774927565946723 77299785266662391348920085)
              ·
                refine ⟨3623427434374799594480629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77299785266662391348920085 3623427434374799594480629)
                ·
                  refine ⟨339696321972637461982559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3623427434374799594480629 339696321972637461982559)
                  ·
                    rfl

theorem cell23_5954006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_5954006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954006 prefixEnd_5954006 := by exact prefixLift 5954006
  have htrace : WordTrace (prefixWord ++ tailWord_5954006) baseStart_5954006 baseEnd_5954006 := by
    simpa [prefixWord, tailWord_5954006, baseEnd_5954006] using wordTrace_append hprefix tailTrace_5954006
  have hstable : (prefixWord ++ tailWord_5954006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954006).length < 2 ^ (prefixWord ++ tailWord_5954006).sum := by decide
  have hdescent : baseEnd_5954006 < baseStart_5954006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954059 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 3]
def baseStart_5954059 : Nat := 118140960795 + 5954059 * 2 ^ 59
def prefixEnd_5954059 : Nat := 4983230072969 + 3 ^ 40 * 5954059 * 2
def baseEnd_5954059 : Nat := 3057294112228425450480287

theorem tailTrace_5954059 : CollatzResearch.WordTrace tailWord_5954059 prefixEnd_5954059 3057294112228425450480287 := by
  unfold tailWord_5954059
  simp only [CollatzResearch.WordTrace]
  refine ⟨217162372336468590164969231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144774914890979060109979487 217162372336468590164969231)
  ·
    refine ⟨325743558504702885247453847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217162372336468590164969231 325743558504702885247453847)
    ·
      refine ⟨488615337757054327871180771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325743558504702885247453847 488615337757054327871180771)
      ·
        refine ⟨732923006635581491806771157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488615337757054327871180771 732923006635581491806771157)
        ·
          refine ⟨17177882968021441214221199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 732923006635581491806771157 17177882968021441214221199)
          ·
            refine ⟨25766824452032161821331799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17177882968021441214221199 25766824452032161821331799)
            ·
              refine ⟨38650236678048242731997699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25766824452032161821331799 38650236678048242731997699)
              ·
                refine ⟨57975355017072364097996549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38650236678048242731997699 57975355017072364097996549)
                ·
                  refine ⟨10870379065701068268374353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57975355017072364097996549 10870379065701068268374353)
                  ·
                    refine ⟨8152784299275801201280765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10870379065701068268374353 8152784299275801201280765)
                    ·
                      refine ⟨3057294112228425450480287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8152784299275801201280765 3057294112228425450480287)
                      ·
                        rfl

theorem cell23_5954059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 3].length) (baseStart_5954059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954059 prefixEnd_5954059 := by exact prefixLift 5954059
  have htrace : WordTrace (prefixWord ++ tailWord_5954059) baseStart_5954059 baseEnd_5954059 := by
    simpa [prefixWord, tailWord_5954059, baseEnd_5954059] using wordTrace_append hprefix tailTrace_5954059
  have hstable : (prefixWord ++ tailWord_5954059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954059).length < 2 ^ (prefixWord ++ tailWord_5954059).sum := by decide
  have hdescent : baseEnd_5954059 < baseStart_5954059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954129 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_5954129 : Nat := 118140960795 + 5954129 * 2 ^ 59
def prefixEnd_5954129 : Nat := 4983230072969 + 3 ^ 40 * 5954129 * 2
def baseEnd_5954129 : Nat := 3057330055874240176604965

theorem tailTrace_5954129 : CollatzResearch.WordTrace tailWord_5954129 prefixEnd_5954129 3057330055874240176604965 := by
  unfold tailWord_5954129
  simp only [CollatzResearch.WordTrace]
  refine ⟨217164925446214992120017441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144776616964143328080011627 217164925446214992120017441)
  ·
    refine ⟨162873694084661244090013081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217164925446214992120017441 162873694084661244090013081)
    ·
      refine ⟨122155270563495933067509811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162873694084661244090013081 122155270563495933067509811)
      ·
        refine ⟨183232905845243899601264717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122155270563495933067509811 183232905845243899601264717)
        ·
          refine ⟨68712339691966462350474269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183232905845243899601264717 68712339691966462350474269)
          ·
            refine ⟨25767127384487423381427851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68712339691966462350474269 25767127384487423381427851)
            ·
              refine ⟨38650691076731135072141777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25767127384487423381427851 38650691076731135072141777)
              ·
                refine ⟨28988018307548351304106333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38650691076731135072141777 28988018307548351304106333)
                ·
                  refine ⟨10870506865330631739039875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28988018307548351304106333 10870506865330631739039875)
                  ·
                    refine ⟨16305760297995947608559813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10870506865330631739039875 16305760297995947608559813)
                    ·
                      refine ⟨3057330055874240176604965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16305760297995947608559813 3057330055874240176604965)
                      ·
                        rfl

theorem cell23_5954129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_5954129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954129 prefixEnd_5954129 := by exact prefixLift 5954129
  have htrace : WordTrace (prefixWord ++ tailWord_5954129) baseStart_5954129 baseEnd_5954129 := by
    simpa [prefixWord, tailWord_5954129, baseEnd_5954129] using wordTrace_append hprefix tailTrace_5954129
  have hstable : (prefixWord ++ tailWord_5954129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954129).length < 2 ^ (prefixWord ++ tailWord_5954129).sum := by decide
  have hdescent : baseEnd_5954129 < baseStart_5954129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954159 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_5954159 : Nat := 118140960795 + 5954159 * 2 ^ 59
def prefixEnd_5954159 : Nat := 4983230072969 + 3 ^ 40 * 5954159 * 2
def baseEnd_5954159 : Nat := 3057345460293875059229827

theorem tailTrace_5954159 : CollatzResearch.WordTrace tailWord_5954159 prefixEnd_5954159 3057345460293875059229827 := by
  unfold tailWord_5954159
  simp only [CollatzResearch.WordTrace]
  refine ⟨217166019636106307243609531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144777346424070871495739687 217166019636106307243609531)
  ·
    refine ⟨325749029454159460865414297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217166019636106307243609531 325749029454159460865414297)
    ·
      refine ⟨244311772090619595649060723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325749029454159460865414297 244311772090619595649060723)
      ·
        refine ⟨366467658135929393473591085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244311772090619595649060723 366467658135929393473591085)
        ·
          refine ⟨137425371800973522552596657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366467658135929393473591085 137425371800973522552596657)
          ·
            refine ⟨103069028850730141914447493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137425371800973522552596657 103069028850730141914447493)
            ·
              refine ⟨19325442909511901608958905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103069028850730141914447493 19325442909511901608958905)
              ·
                refine ⟨14494082182133926206719179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19325442909511901608958905 14494082182133926206719179)
                ·
                  refine ⟨21741123273200889310078769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14494082182133926206719179 21741123273200889310078769)
                  ·
                    refine ⟨16305842454900666982559077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21741123273200889310078769 16305842454900666982559077)
                    ·
                      refine ⟨3057345460293875059229827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16305842454900666982559077 3057345460293875059229827)
                      ·
                        rfl

theorem cell23_5954159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_5954159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954159 prefixEnd_5954159 := by exact prefixLift 5954159
  have htrace : WordTrace (prefixWord ++ tailWord_5954159) baseStart_5954159 baseEnd_5954159 := by
    simpa [prefixWord, tailWord_5954159, baseEnd_5954159] using wordTrace_append hprefix tailTrace_5954159
  have hstable : (prefixWord ++ tailWord_5954159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954159).length < 2 ^ (prefixWord ++ tailWord_5954159).sum := by decide
  have hdescent : baseEnd_5954159 < baseStart_5954159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954160 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 1, 5]
def baseStart_5954160 : Nat := 118140960795 + 5954160 * 2 ^ 59
def prefixEnd_5954160 : Nat := 4983230072969 + 3 ^ 40 * 5954160 * 2
def baseEnd_5954160 : Nat := 1019115324591509851772441

theorem tailTrace_5954160 : CollatzResearch.WordTrace tailWord_5954160 prefixEnd_5954160 1019115324591509851772441 := by
  unfold tailWord_5954160
  simp only [CollatzResearch.WordTrace]
  refine ⟨108583028054551342207197967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144777370739401789609597289 108583028054551342207197967)
  ·
    refine ⟨162874542081827013310796951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108583028054551342207197967 162874542081827013310796951)
    ·
      refine ⟨244311813122740519966195427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162874542081827013310796951 244311813122740519966195427)
      ·
        refine ⟨366467719684110779949293141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244311813122740519966195427 366467719684110779949293141)
        ·
          refine ⟨4294543590048173202530779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 366467719684110779949293141 4294543590048173202530779)
          ·
            refine ⟨6441815385072259803796169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294543590048173202530779 6441815385072259803796169)
            ·
              refine ⟨4831361538804194852847127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6441815385072259803796169 4831361538804194852847127)
              ·
                refine ⟨7247042308206292279270691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831361538804194852847127 7247042308206292279270691)
                ·
                  refine ⟨10870563462309438418906037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247042308206292279270691 10870563462309438418906037)
                  ·
                    refine ⟨1019115324591509851772441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10870563462309438418906037 1019115324591509851772441)
                    ·
                      rfl

theorem cell23_5954160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 5].length) (baseStart_5954160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954160 prefixEnd_5954160 := by exact prefixLift 5954160
  have htrace : WordTrace (prefixWord ++ tailWord_5954160) baseStart_5954160 baseEnd_5954160 := by
    simpa [prefixWord, tailWord_5954160, baseEnd_5954160] using wordTrace_append hprefix tailTrace_5954160
  have hstable : (prefixWord ++ tailWord_5954160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954160).length < 2 ^ (prefixWord ++ tailWord_5954160).sum := by decide
  have hdescent : baseEnd_5954160 < baseStart_5954160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954179 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 3]
def baseStart_5954179 : Nat := 118140960795 + 5954179 * 2 ^ 59
def prefixEnd_5954179 : Nat := 4983230072969 + 3 ^ 40 * 5954179 * 2
def baseEnd_5954179 : Nat := 3057355729906964980979735

theorem tailTrace_5954179 : CollatzResearch.WordTrace tailWord_5954179 prefixEnd_5954179 3057355729906964980979735 := by
  unfold tailWord_5954179
  simp only [CollatzResearch.WordTrace]
  refine ⟨217166749096033850659337591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144777832730689233772891727 217166749096033850659337591)
  ·
    refine ⟨325750123644050775989006387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217166749096033850659337591 325750123644050775989006387)
    ·
      refine ⟨488625185466076163983509581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325750123644050775989006387 488625185466076163983509581)
      ·
        refine ⟨183234444549778561493816093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488625185466076163983509581 183234444549778561493816093)
        ·
          refine ⟨68712916706166960560181035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183234444549778561493816093 68712916706166960560181035)
          ·
            refine ⟨103069375059250440840271553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68712916706166960560181035 103069375059250440840271553)
            ·
              refine ⟨77302031294437830630203665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103069375059250440840271553 77302031294437830630203665)
              ·
                refine ⟨57976523470828372972652749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77302031294437830630203665 57976523470828372972652749)
                ·
                  refine ⟨21741196301560639864744781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57976523470828372972652749 21741196301560639864744781)
                  ·
                    refine ⟨8152948613085239949279293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21741196301560639864744781 8152948613085239949279293)
                    ·
                      refine ⟨3057355729906964980979735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8152948613085239949279293 3057355729906964980979735)
                      ·
                        rfl

theorem cell23_5954179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_5954179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954179 prefixEnd_5954179 := by exact prefixLift 5954179
  have htrace : WordTrace (prefixWord ++ tailWord_5954179) baseStart_5954179 baseEnd_5954179 := by
    simpa [prefixWord, tailWord_5954179, baseEnd_5954179] using wordTrace_append hprefix tailTrace_5954179
  have hstable : (prefixWord ++ tailWord_5954179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954179).length < 2 ^ (prefixWord ++ tailWord_5954179).sum := by decide
  have hdescent : baseEnd_5954179 < baseStart_5954179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954180 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_5954180 : Nat := 118140960795 + 5954180 * 2 ^ 59
def prefixEnd_5954180 : Nat := 4983230072969 + 3 ^ 40 * 5954180 * 2
def baseEnd_5954180 : Nat := 3057356243387619477067231

theorem tailTrace_5954180 : CollatzResearch.WordTrace tailWord_5954180 prefixEnd_5954180 3057356243387619477067231 := by
  unfold tailWord_5954180
  simp only [CollatzResearch.WordTrace]
  refine ⟨108583392784515113915061997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144777857046020151886749329 108583392784515113915061997)
  ·
    refine ⟨40718772294193167718148249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108583392784515113915061997 40718772294193167718148249)
    ·
      refine ⟨30539079220644875788611187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40718772294193167718148249 30539079220644875788611187)
      ·
        refine ⟨45808618830967313682916781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30539079220644875788611187 45808618830967313682916781)
        ·
          refine ⟨17178232061612742631093793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45808618830967313682916781 17178232061612742631093793)
          ·
            refine ⟨12883674046209556973320345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17178232061612742631093793 12883674046209556973320345)
            ·
              refine ⟨9662755534657167729990259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12883674046209556973320345 9662755534657167729990259)
              ·
                refine ⟨14494133301985751594985389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9662755534657167729990259 14494133301985751594985389)
                ·
                  refine ⟨5435299988244656848119521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14494133301985751594985389 5435299988244656848119521)
                  ·
                    refine ⟨4076474991183492636089641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5435299988244656848119521 4076474991183492636089641)
                    ·
                      refine ⟨3057356243387619477067231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076474991183492636089641 3057356243387619477067231)
                      ·
                        rfl

theorem cell23_5954180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_5954180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954180 prefixEnd_5954180 := by exact prefixLift 5954180
  have htrace : WordTrace (prefixWord ++ tailWord_5954180) baseStart_5954180 baseEnd_5954180 := by
    simpa [prefixWord, tailWord_5954180, baseEnd_5954180] using wordTrace_append hprefix tailTrace_5954180
  have hstable : (prefixWord ++ tailWord_5954180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954180).length < 2 ^ (prefixWord ++ tailWord_5954180).sum := by decide
  have hdescent : baseEnd_5954180 < baseStart_5954180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954223 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 1, 3, 2]
def baseStart_5954223 : Nat := 118140960795 + 5954223 * 2 ^ 59
def prefixEnd_5954223 : Nat := 4983230072969 + 3 ^ 40 * 5954223 * 2
def baseEnd_5954223 : Nat := 3057378323055762808829533

theorem tailTrace_5954223 : CollatzResearch.WordTrace tailWord_5954223 prefixEnd_5954223 3057378323055762808829533 := by
  unfold tailWord_5954223
  simp only [CollatzResearch.WordTrace]
  refine ⟨217168353907874446173939323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144778902605249630782626215 217168353907874446173939323)
  ·
    refine ⟨325752530861811669260908985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217168353907874446173939323 325752530861811669260908985)
    ·
      refine ⟨244314398146358751945681739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325752530861811669260908985 244314398146358751945681739)
      ·
        refine ⟨366471597219538127918522609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244314398146358751945681739 366471597219538127918522609)
        ·
          refine ⟨274853697914653595938891957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366471597219538127918522609 274853697914653595938891957)
          ·
            refine ⟨25767534179498774619271121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274853697914653595938891957 25767534179498774619271121)
            ·
              refine ⟨19325650634624080964453341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25767534179498774619271121 19325650634624080964453341)
              ·
                refine ⟨7247118987984030361670003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19325650634624080964453341 7247118987984030361670003)
                ·
                  refine ⟨10870678481976045542505005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247118987984030361670003 10870678481976045542505005)
                  ·
                    refine ⟨4076504430741017078439377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10870678481976045542505005 4076504430741017078439377)
                    ·
                      refine ⟨3057378323055762808829533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076504430741017078439377 3057378323055762808829533)
                      ·
                        rfl

theorem cell23_5954223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 3, 2].length) (baseStart_5954223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954223 prefixEnd_5954223 := by exact prefixLift 5954223
  have htrace : WordTrace (prefixWord ++ tailWord_5954223) baseStart_5954223 baseEnd_5954223 := by
    simpa [prefixWord, tailWord_5954223, baseEnd_5954223] using wordTrace_append hprefix tailTrace_5954223
  have hstable : (prefixWord ++ tailWord_5954223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954223).length < 2 ^ (prefixWord ++ tailWord_5954223).sum := by decide
  have hdescent : baseEnd_5954223 < baseStart_5954223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954296 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 7, 2]
def baseStart_5954296 : Nat := 118140960795 + 5954296 * 2 ^ 59
def prefixEnd_5954296 : Nat := 4983230072969 + 3 ^ 40 * 5954296 * 2
def baseEnd_5954296 : Nat := 3057415807143541023216697

theorem tailTrace_5954296 : CollatzResearch.WordTrace tailWord_5954296 prefixEnd_5954296 3057415807143541023216697 := by
  unfold tailWord_5954296
  simp only [CollatzResearch.WordTrace]
  refine ⟨108585508218304989820673371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144780677624406653094231161 108585508218304989820673371)
  ·
    refine ⟨162878262327457484731010057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108585508218304989820673371 162878262327457484731010057)
    ·
      refine ⟨122158696745593113548257543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162878262327457484731010057 122158696745593113548257543)
      ·
        refine ⟨183238045118389670322386315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122158696745593113548257543 183238045118389670322386315)
        ·
          refine ⟨274857067677584505483579473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183238045118389670322386315 274857067677584505483579473)
          ·
            refine ⟨206142800758188379112684605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274857067677584505483579473 206142800758188379112684605)
            ·
              refine ⟨77303550284320642167256727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206142800758188379112684605 77303550284320642167256727)
              ·
                refine ⟨115955325426480963250885091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77303550284320642167256727 115955325426480963250885091)
                ·
                  refine ⟨173932988139721444876327637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115955325426480963250885091 173932988139721444876327637)
                  ·
                    refine ⟨4076554409524721364288929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 173932988139721444876327637 4076554409524721364288929)
                    ·
                      refine ⟨3057415807143541023216697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076554409524721364288929 3057415807143541023216697)
                      ·
                        rfl

theorem cell23_5954296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_5954296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954296 prefixEnd_5954296 := by exact prefixLift 5954296
  have htrace : WordTrace (prefixWord ++ tailWord_5954296) baseStart_5954296 baseEnd_5954296 := by
    simpa [prefixWord, tailWord_5954296, baseEnd_5954296] using wordTrace_append hprefix tailTrace_5954296
  have hstable : (prefixWord ++ tailWord_5954296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954296).length < 2 ^ (prefixWord ++ tailWord_5954296).sum := by decide
  have hdescent : baseEnd_5954296 < baseStart_5954296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954329 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_5954329 : Nat := 118140960795 + 5954329 * 2 ^ 59
def prefixEnd_5954329 : Nat := 4983230072969 + 3 ^ 40 * 5954329 * 2
def baseEnd_5954329 : Nat := 3057432752005139394104045

theorem tailTrace_5954329 : CollatzResearch.WordTrace tailWord_5954329 prefixEnd_5954329 3057432752005139394104045 := by
  unfold tailWord_5954329
  simp only [CollatzResearch.WordTrace]
  refine ⟨217172220045490426277298041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144781480030326950851532027 217172220045490426277298041)
  ·
    refine ⟨162879165034117819707973531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217172220045490426277298041 162879165034117819707973531)
    ·
      refine ⟨244318747551176729561960297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162879165034117819707973531 244318747551176729561960297)
      ·
        refine ⟨183239060663382547171470223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244318747551176729561960297 183239060663382547171470223)
        ·
          refine ⟨274858590995073820757205335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183239060663382547171470223 274858590995073820757205335)
          ·
            refine ⟨412287886492610731135808003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274858590995073820757205335 412287886492610731135808003)
            ·
              refine ⟨618431829738916096703712005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412287886492610731135808003 618431829738916096703712005)
              ·
                refine ⟨115955968076046768131946001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618431829738916096703712005 115955968076046768131946001)
                ·
                  refine ⟨86966976057035076098959501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115955968076046768131946001 86966976057035076098959501)
                  ·
                    refine ⟨32612616021388153537109813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86966976057035076098959501 32612616021388153537109813)
                    ·
                      refine ⟨3057432752005139394104045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32612616021388153537109813 3057432752005139394104045)
                      ·
                        rfl

theorem cell23_5954329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_5954329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954329 prefixEnd_5954329 := by exact prefixLift 5954329
  have htrace : WordTrace (prefixWord ++ tailWord_5954329) baseStart_5954329 baseEnd_5954329 := by
    simpa [prefixWord, tailWord_5954329, baseEnd_5954329] using wordTrace_append hprefix tailTrace_5954329
  have hstable : (prefixWord ++ tailWord_5954329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954329).length < 2 ^ (prefixWord ++ tailWord_5954329).sum := by decide
  have hdescent : baseEnd_5954329 < baseStart_5954329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954353 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 3, 4]
def baseStart_5954353 : Nat := 118140960795 + 5954353 * 2 ^ 59
def prefixEnd_5954353 : Nat := 4983230072969 + 3 ^ 40 * 5954353 * 2
def baseEnd_5954353 : Nat := 1019148358513615766734645

theorem tailTrace_5954353 : CollatzResearch.WordTrace tailWord_5954353 prefixEnd_5954353 1019148358513615766734645 := by
  unfold tailWord_5954353
  simp only [CollatzResearch.WordTrace]
  refine ⟨217173095397403478376171713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144782063598268985584114475 217173095397403478376171713)
  ·
    refine ⟨162879821548052608782128785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217173095397403478376171713 162879821548052608782128785)
    ·
      refine ⟨122159866161039456586596589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162879821548052608782128785 122159866161039456586596589)
      ·
        refine ⟨45809949810389796219973721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122159866161039456586596589 45809949810389796219973721)
        ·
          refine ⟨34357462357792347164980291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45809949810389796219973721 34357462357792347164980291)
          ·
            refine ⟨51536193536688520747470437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34357462357792347164980291 51536193536688520747470437)
            ·
              refine ⟨9663036288129097640150707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51536193536688520747470437 9663036288129097640150707)
              ·
                refine ⟨14494554432193646460226061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663036288129097640150707 14494554432193646460226061)
                ·
                  refine ⟨5435457912072617422584773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14494554432193646460226061 5435457912072617422584773)
                  ·
                    refine ⟨1019148358513615766734645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5435457912072617422584773 1019148358513615766734645)
                    ·
                      rfl

theorem cell23_5954353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_5954353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954353 prefixEnd_5954353 := by exact prefixLift 5954353
  have htrace : WordTrace (prefixWord ++ tailWord_5954353) baseStart_5954353 baseEnd_5954353 := by
    simpa [prefixWord, tailWord_5954353, baseEnd_5954353] using wordTrace_append hprefix tailTrace_5954353
  have hstable : (prefixWord ++ tailWord_5954353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954353).length < 2 ^ (prefixWord ++ tailWord_5954353).sum := by decide
  have hdescent : baseEnd_5954353 < baseStart_5954353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954376 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_5954376 : Nat := 118140960795 + 5954376 * 2 ^ 59
def prefixEnd_5954376 : Nat := 4983230072969 + 3 ^ 40 * 5954376 * 2
def baseEnd_5954376 : Nat := 3057456885595900710216329

theorem tailTrace_5954376 : CollatzResearch.WordTrace tailWord_5954376 prefixEnd_5954376 3057456885595900710216329 := by
  unfold tailWord_5954376
  simp only [CollatzResearch.WordTrace]
  refine ⟨108586967138160076652129491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144782622850880102202839321 108586967138160076652129491)
  ·
    refine ⟨162880450707240114978194237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108586967138160076652129491 162880450707240114978194237)
    ·
      refine ⟨61080169015215043116822839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162880450707240114978194237 61080169015215043116822839)
      ·
        refine ⟨91620253522822564675234259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61080169015215043116822839 91620253522822564675234259)
        ·
          refine ⟨137430380284233847012851389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91620253522822564675234259 137430380284233847012851389)
          ·
            refine ⟨51536392606587692629819271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137430380284233847012851389 51536392606587692629819271)
            ·
              refine ⟨77304588909881538944728907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51536392606587692629819271 77304588909881538944728907)
              ·
                refine ⟨115956883364822308417093361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77304588909881538944728907 115956883364822308417093361)
                ·
                  refine ⟨86967662523616731312820021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115956883364822308417093361 86967662523616731312820021)
                  ·
                    refine ⟨8153218361589068560576877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86967662523616731312820021 8153218361589068560576877)
                    ·
                      refine ⟨3057456885595900710216329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8153218361589068560576877 3057456885595900710216329)
                      ·
                        rfl

theorem cell23_5954376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_5954376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954376 prefixEnd_5954376 := by exact prefixLift 5954376
  have htrace : WordTrace (prefixWord ++ tailWord_5954376) baseStart_5954376 baseEnd_5954376 := by
    simpa [prefixWord, tailWord_5954376, baseEnd_5954376] using wordTrace_append hprefix tailTrace_5954376
  have hstable : (prefixWord ++ tailWord_5954376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954376).length < 2 ^ (prefixWord ++ tailWord_5954376).sum := by decide
  have hdescent : baseEnd_5954376 < baseStart_5954376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954379 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 9]
def baseStart_5954379 : Nat := 118140960795 + 5954379 * 2 ^ 59
def prefixEnd_5954379 : Nat := 4983230072969 + 3 ^ 40 * 5954379 * 2
def baseEnd_5954379 : Nat := 1019152808679288066159605

theorem tailTrace_5954379 : CollatzResearch.WordTrace tailWord_5954379 prefixEnd_5954379 1019152808679288066159605 := by
  unfold tailWord_5954379
  simp only [CollatzResearch.WordTrace]
  refine ⟨217174043695309284816618191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144782695796872856544412127 217174043695309284816618191)
  ·
    refine ⟨325761065542963927224927287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217174043695309284816618191 325761065542963927224927287)
    ·
      refine ⟨488641598314445890837390931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325761065542963927224927287 488641598314445890837390931)
      ·
        refine ⟨732962397471668836256086397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488641598314445890837390931 732962397471668836256086397)
        ·
          refine ⟨274860899051875813596032399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732962397471668836256086397 274860899051875813596032399)
          ·
            refine ⟨412291348577813720394048599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274860899051875813596032399 412291348577813720394048599)
            ·
              refine ⟨618437022866720580591072899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412291348577813720394048599 618437022866720580591072899)
              ·
                refine ⟨927655534300080870886609349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618437022866720580591072899 927655534300080870886609349)
                ·
                  refine ⟨173935412681265163291239253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 927655534300080870886609349 173935412681265163291239253)
                  ·
                    refine ⟨1019152808679288066159605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 173935412681265163291239253 1019152808679288066159605)
                    ·
                      rfl

theorem cell23_5954379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_5954379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954379 prefixEnd_5954379 := by exact prefixLift 5954379
  have htrace : WordTrace (prefixWord ++ tailWord_5954379) baseStart_5954379 baseEnd_5954379 := by
    simpa [prefixWord, tailWord_5954379, baseEnd_5954379] using wordTrace_append hprefix tailTrace_5954379
  have hstable : (prefixWord ++ tailWord_5954379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954379).length < 2 ^ (prefixWord ++ tailWord_5954379).sum := by decide
  have hdescent : baseEnd_5954379 < baseStart_5954379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954426 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_5954426 : Nat := 118140960795 + 5954426 * 2 ^ 59
def prefixEnd_5954426 : Nat := 4983230072969 + 3 ^ 40 * 5954426 * 2
def baseEnd_5954426 : Nat := 1019160853209541838197033

theorem tailTrace_5954426 : CollatzResearch.WordTrace tailWord_5954426 prefixEnd_5954426 1019160853209541838197033 := by
  unfold tailWord_5954426
  simp only [CollatzResearch.WordTrace]
  refine ⟨54293939481534752960894783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144783838617426007895719421 54293939481534752960894783)
  ·
    refine ⟨81440909222302129441342175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54293939481534752960894783 81440909222302129441342175)
    ·
      refine ⟨122161363833453194162013263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81440909222302129441342175 122161363833453194162013263)
      ·
        refine ⟨183242045750179791243019895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122161363833453194162013263 183242045750179791243019895)
        ·
          refine ⟨274863068625269686864529843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183242045750179791243019895 274863068625269686864529843)
          ·
            refine ⟨412294602937904530296794765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274863068625269686864529843 412294602937904530296794765)
            ·
              refine ⟨154610476101714198861298037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412294602937904530296794765 154610476101714198861298037)
              ·
                refine ⟨14494732134535706143246691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154610476101714198861298037 14494732134535706143246691)
                ·
                  refine ⟨21742098201803559214870037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14494732134535706143246691 21742098201803559214870037)
                  ·
                    refine ⟨1019160853209541838197033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21742098201803559214870037 1019160853209541838197033)
                    ·
                      rfl

theorem cell23_5954426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_5954426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954426 prefixEnd_5954426 := by exact prefixLift 5954426
  have htrace : WordTrace (prefixWord ++ tailWord_5954426) baseStart_5954426 baseEnd_5954426 := by
    simpa [prefixWord, tailWord_5954426, baseEnd_5954426] using wordTrace_append hprefix tailTrace_5954426
  have hstable : (prefixWord ++ tailWord_5954426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954426).length < 2 ^ (prefixWord ++ tailWord_5954426).sum := by decide
  have hdescent : baseEnd_5954426 < baseStart_5954426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954453 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_5954453 : Nat := 118140960795 + 5954453 * 2 ^ 59
def prefixEnd_5954453 : Nat := 4983230072969 + 3 ^ 40 * 5954453 * 2
def baseEnd_5954453 : Nat := 3057496423606296908953475

theorem tailTrace_5954453 : CollatzResearch.WordTrace tailWord_5954453 prefixEnd_5954453 3057496423606296908953475 := by
  unfold tailWord_5954453
  simp only [CollatzResearch.WordTrace]
  refine ⟨217176742697041195454812013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144784495131360796969874675 217176742697041195454812013)
  ·
    refine ⟨81441278511390448295554505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217176742697041195454812013 81441278511390448295554505)
    ·
      refine ⟨61080958883542836221665879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81441278511390448295554505 61080958883542836221665879)
      ·
        refine ⟨91621438325314254332498819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61080958883542836221665879 91621438325314254332498819)
        ·
          refine ⟨137432157487971381498748229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91621438325314254332498819 137432157487971381498748229)
          ·
            refine ⟨25768529528994634031015293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137432157487971381498748229 25768529528994634031015293)
            ·
              refine ⟨9663198573372987761630735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25768529528994634031015293 9663198573372987761630735)
              ·
                refine ⟨14494797860059481642446103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663198573372987761630735 14494797860059481642446103)
                ·
                  refine ⟨21742196790089222463669155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14494797860059481642446103 21742196790089222463669155)
                  ·
                    refine ⟨32613295185133833695503733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21742196790089222463669155 32613295185133833695503733)
                    ·
                      refine ⟨3057496423606296908953475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32613295185133833695503733 3057496423606296908953475)
                      ·
                        rfl

theorem cell23_5954453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_5954453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954453 prefixEnd_5954453 := by exact prefixLift 5954453
  have htrace : WordTrace (prefixWord ++ tailWord_5954453) baseStart_5954453 baseEnd_5954453 := by
    simpa [prefixWord, tailWord_5954453, baseEnd_5954453] using wordTrace_append hprefix tailTrace_5954453
  have hstable : (prefixWord ++ tailWord_5954453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954453).length < 2 ^ (prefixWord ++ tailWord_5954453).sum := by decide
  have hdescent : baseEnd_5954453 < baseStart_5954453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954477 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_5954477 : Nat := 118140960795 + 5954477 * 2 ^ 59
def prefixEnd_5954477 : Nat := 4983230072969 + 3 ^ 40 * 5954477 * 2
def baseEnd_5954477 : Nat := 1019169582380668271684455

theorem tailTrace_5954477 : CollatzResearch.WordTrace tailWord_5954477 prefixEnd_5954477 1019169582380668271684455 := by
  unfold tailWord_5954477
  simp only [CollatzResearch.WordTrace]
  refine ⟨217177618048954247553685685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144785078699302831702457123 217177618048954247553685685)
  ·
    refine ⟨20360401692089460708158033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217177618048954247553685685 20360401692089460708158033)
    ·
      refine ⟨15270301269067095531118525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20360401692089460708158033 15270301269067095531118525)
      ·
        refine ⟨5726362975900160824169447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15270301269067095531118525 5726362975900160824169447)
        ·
          refine ⟨8589544463850241236254171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726362975900160824169447 8589544463850241236254171)
          ·
            refine ⟨12884316695775361854381257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8589544463850241236254171 12884316695775361854381257)
            ·
              refine ⟨9663237521831521390785943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12884316695775361854381257 9663237521831521390785943)
              ·
                refine ⟨14494856282747282086178915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663237521831521390785943 14494856282747282086178915)
                ·
                  refine ⟨21742284424120923129268373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14494856282747282086178915 21742284424120923129268373)
                  ·
                    refine ⟨1019169582380668271684455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21742284424120923129268373 1019169582380668271684455)
                    ·
                      rfl

theorem cell23_5954477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_5954477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954477 prefixEnd_5954477 := by exact prefixLift 5954477
  have htrace : WordTrace (prefixWord ++ tailWord_5954477) baseStart_5954477 baseEnd_5954477 := by
    simpa [prefixWord, tailWord_5954477, baseEnd_5954477] using wordTrace_append hprefix tailTrace_5954477
  have hstable : (prefixWord ++ tailWord_5954477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954477).length < 2 ^ (prefixWord ++ tailWord_5954477).sum := by decide
  have hdescent : baseEnd_5954477 < baseStart_5954477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954484 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5954484 : Nat := 118140960795 + 5954484 * 2 ^ 59
def prefixEnd_5954484 : Nat := 4983230072969 + 3 ^ 40 * 5954484 * 2
def baseEnd_5954484 : Nat := 3057512341506586287665833

theorem tailTrace_5954484 : CollatzResearch.WordTrace tailWord_5954484 prefixEnd_5954484 3057512341506586287665833 := by
  unfold tailWord_5954484
  simp only [CollatzResearch.WordTrace]
  refine ⟨108588936679964443874595253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144785248906619258499460337 108588936679964443874595253)
  ·
    refine ⟨10180212813746666613243305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108588936679964443874595253 10180212813746666613243305)
    ·
      refine ⟨7635159610309999959932479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10180212813746666613243305 7635159610309999959932479)
      ·
        refine ⟨11452739415464999939898719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7635159610309999959932479 11452739415464999939898719)
        ·
          refine ⟨17179109123197499909848079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11452739415464999939898719 17179109123197499909848079)
          ·
            refine ⟨25768663684796249864772119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17179109123197499909848079 25768663684796249864772119)
            ·
              refine ⟨38652995527194374797158179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25768663684796249864772119 38652995527194374797158179)
              ·
                refine ⟨57979493290791562195737269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38652995527194374797158179 57979493290791562195737269)
                ·
                  refine ⟨5435577496011708955850369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57979493290791562195737269 5435577496011708955850369)
                  ·
                    refine ⟨4076683122008781716887777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5435577496011708955850369 4076683122008781716887777)
                    ·
                      refine ⟨3057512341506586287665833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076683122008781716887777 3057512341506586287665833)
                      ·
                        rfl

theorem cell23_5954484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5954484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954484 prefixEnd_5954484 := by exact prefixLift 5954484
  have htrace : WordTrace (prefixWord ++ tailWord_5954484) baseStart_5954484 baseEnd_5954484 := by
    simpa [prefixWord, tailWord_5954484, baseEnd_5954484] using wordTrace_append hprefix tailTrace_5954484
  have hstable : (prefixWord ++ tailWord_5954484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954484).length < 2 ^ (prefixWord ++ tailWord_5954484).sum := by decide
  have hdescent : baseEnd_5954484 < baseStart_5954484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954504 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_5954504 : Nat := 118140960795 + 5954504 * 2 ^ 59
def prefixEnd_5954504 : Nat := 4983230072969 + 3 ^ 40 * 5954504 * 2
def baseEnd_5954504 : Nat := 3057522611119676209415741

theorem tailTrace_5954504 : CollatzResearch.WordTrace tailWord_5954504 prefixEnd_5954504 3057522611119676209415741 := by
  unfold tailWord_5954504
  simp only [CollatzResearch.WordTrace]
  refine ⟨108589301409928215582459283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144785735213237620776612377 108589301409928215582459283)
  ·
    refine ⟨162883952114892323373688925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108589301409928215582459283 162883952114892323373688925)
    ·
      refine ⟨61081482043084621265133347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162883952114892323373688925 61081482043084621265133347)
      ·
        refine ⟨91622223064626931897700021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61081482043084621265133347 91622223064626931897700021)
        ·
          refine ⟨8589583412308774865409377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91622223064626931897700021 8589583412308774865409377)
          ·
            refine ⟨6442187559231581149057033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8589583412308774865409377 6442187559231581149057033)
            ·
              refine ⟨4831640669423685861792775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6442187559231581149057033 4831640669423685861792775)
              ·
                refine ⟨7247461004135528792689163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831640669423685861792775 7247461004135528792689163)
                ·
                  refine ⟨10871191506203293189033745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247461004135528792689163 10871191506203293189033745)
                  ·
                    refine ⟨8153393629652469891775309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10871191506203293189033745 8153393629652469891775309)
                    ·
                      refine ⟨3057522611119676209415741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8153393629652469891775309 3057522611119676209415741)
                      ·
                        rfl

theorem cell23_5954504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_5954504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954504 prefixEnd_5954504 := by exact prefixLift 5954504
  have htrace : WordTrace (prefixWord ++ tailWord_5954504) baseStart_5954504 baseEnd_5954504 := by
    simpa [prefixWord, tailWord_5954504, baseEnd_5954504] using wordTrace_append hprefix tailTrace_5954504
  have hstable : (prefixWord ++ tailWord_5954504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954504).length < 2 ^ (prefixWord ++ tailWord_5954504).sum := by decide
  have hdescent : baseEnd_5954504 < baseStart_5954504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954517 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5954517 : Nat := 118140960795 + 5954517 * 2 ^ 59
def prefixEnd_5954517 : Nat := 4983230072969 + 3 ^ 40 * 5954517 * 2
def baseEnd_5954517 : Nat := 3057529286368184658553181

theorem tailTrace_5954517 : CollatzResearch.WordTrace tailWord_5954517 prefixEnd_5954517 3057529286368184658553181 := by
  unfold tailWord_5954517
  simp only [CollatzResearch.WordTrace]
  refine ⟨217179076968809334385141805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144786051312539556256761203 217179076968809334385141805)
  ·
    refine ⟨81442153863303500394428177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217179076968809334385141805 81442153863303500394428177)
    ·
      refine ⟨61081615397477625295821133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81442153863303500394428177 61081615397477625295821133)
      ·
        refine ⟨22905605774054109485932925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61081615397477625295821133 22905605774054109485932925)
        ·
          refine ⟨8589602165270291057224847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22905605774054109485932925 8589602165270291057224847)
          ·
            refine ⟨12884403247905436585837271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8589602165270291057224847 12884403247905436585837271)
            ·
              refine ⟨19326604871858154878755907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12884403247905436585837271 19326604871858154878755907)
              ·
                refine ⟨28989907307787232318133861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19326604871858154878755907 28989907307787232318133861)
                ·
                  refine ⟨5435607620210106059650099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28989907307787232318133861 5435607620210106059650099)
                  ·
                    refine ⟨8153411430315159089475149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435607620210106059650099 8153411430315159089475149)
                    ·
                      refine ⟨3057529286368184658553181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8153411430315159089475149 3057529286368184658553181)
                      ·
                        rfl

theorem cell23_5954517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5954517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954517 prefixEnd_5954517 := by exact prefixLift 5954517
  have htrace : WordTrace (prefixWord ++ tailWord_5954517) baseStart_5954517 baseEnd_5954517 := by
    simpa [prefixWord, tailWord_5954517, baseEnd_5954517] using wordTrace_append hprefix tailTrace_5954517
  have hstable : (prefixWord ++ tailWord_5954517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954517).length < 2 ^ (prefixWord ++ tailWord_5954517).sum := by decide
  have hdescent : baseEnd_5954517 < baseStart_5954517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954591 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 2, 2, 2]
def baseStart_5954591 : Nat := 118140960795 + 5954591 * 2 ^ 59
def prefixEnd_5954591 : Nat := 4983230072969 + 3 ^ 40 * 5954591 * 2
def baseEnd_5954591 : Nat := 3057567283936617369027841

theorem tailTrace_5954591 : CollatzResearch.WordTrace tailWord_5954591 prefixEnd_5954591 3057567283936617369027841 := by
  unfold tailWord_5954591
  simp only [CollatzResearch.WordTrace]
  refine ⟨217181775970541245023335627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144787850647027496682223751 217181775970541245023335627)
  ·
    refine ⟨325772663955811867535003441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217181775970541245023335627 325772663955811867535003441)
    ·
      refine ⟨244329497966858900651252581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325772663955811867535003441 244329497966858900651252581)
      ·
        refine ⟨45811780868786043872109859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244329497966858900651252581 45811780868786043872109859)
        ·
          refine ⟨68717671303179065808164789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45811780868786043872109859 68717671303179065808164789)
          ·
            refine ⟨6442281684673037419515449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68717671303179065808164789 6442281684673037419515449)
            ·
              refine ⟨4831711263504778064636587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6442281684673037419515449 4831711263504778064636587)
              ·
                refine ⟨7247566895257167096954881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831711263504778064636587 7247566895257167096954881)
                ·
                  refine ⟨5435675171442875322716161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7247566895257167096954881 5435675171442875322716161)
                  ·
                    refine ⟨4076756378582156492037121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5435675171442875322716161 4076756378582156492037121)
                    ·
                      refine ⟨3057567283936617369027841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076756378582156492037121 3057567283936617369027841)
                      ·
                        rfl

theorem cell23_5954591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_5954591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954591 prefixEnd_5954591 := by exact prefixLift 5954591
  have htrace : WordTrace (prefixWord ++ tailWord_5954591) baseStart_5954591 baseEnd_5954591 := by
    simpa [prefixWord, tailWord_5954591, baseEnd_5954591] using wordTrace_append hprefix tailTrace_5954591
  have hstable : (prefixWord ++ tailWord_5954591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954591).length < 2 ^ (prefixWord ++ tailWord_5954591).sum := by decide
  have hdescent : baseEnd_5954591 < baseStart_5954591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954610 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_5954610 : Nat := 118140960795 + 5954610 * 2 ^ 59
def prefixEnd_5954610 : Nat := 4983230072969 + 3 ^ 40 * 5954610 * 2
def baseEnd_5954610 : Nat := 1019192346689684264896751

theorem tailTrace_5954610 : CollatzResearch.WordTrace tailWord_5954610 prefixEnd_5954610 1019192346689684264896751 := by
  unfold tailWord_5954610
  simp only [CollatzResearch.WordTrace]
  refine ⟨54295617239368102817069321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144788312638314940845518189 54295617239368102817069321)
  ·
    refine ⟨40721712929526077112801991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54295617239368102817069321 40721712929526077112801991)
    ·
      refine ⟨61082569394289115669202987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40721712929526077112801991 61082569394289115669202987)
      ·
        refine ⟨91623854091433673503804481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61082569394289115669202987 91623854091433673503804481)
        ·
          refine ⟨68717890568575255127853361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91623854091433673503804481 68717890568575255127853361)
          ·
            refine ⟨51538417926431441345890021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68717890568575255127853361 51538417926431441345890021)
            ·
              refine ⟨9663453361205895252354379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51538417926431441345890021 9663453361205895252354379)
              ·
                refine ⟨14495180041808842878531569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663453361205895252354379 14495180041808842878531569)
                ·
                  refine ⟨10871385031356632158898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14495180041808842878531569 10871385031356632158898677)
                  ·
                    refine ⟨1019192346689684264896751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10871385031356632158898677 1019192346689684264896751)
                    ·
                      rfl

theorem cell23_5954610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_5954610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954610 prefixEnd_5954610 := by exact prefixLift 5954610
  have htrace : WordTrace (prefixWord ++ tailWord_5954610) baseStart_5954610 baseEnd_5954610 := by
    simpa [prefixWord, tailWord_5954610, baseEnd_5954610] using wordTrace_append hprefix tailTrace_5954610
  have hstable : (prefixWord ++ tailWord_5954610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954610).length < 2 ^ (prefixWord ++ tailWord_5954610).sum := by decide
  have hdescent : baseEnd_5954610 < baseStart_5954610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954674 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_5954674 : Nat := 118140960795 + 5954674 * 2 ^ 59
def prefixEnd_5954674 : Nat := 4983230072969 + 3 ^ 40 * 5954674 * 2
def baseEnd_5954674 : Nat := 1019203300943646848096653

theorem tailTrace_5954674 : CollatzResearch.WordTrace tailWord_5954674 prefixEnd_5954674 1019203300943646848096653 := by
  unfold tailWord_5954674
  simp only [CollatzResearch.WordTrace]
  refine ⟨54296200807310137549651769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144789868819493700132404717 54296200807310137549651769)
  ·
    refine ⟨40722150605482603162238827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54296200807310137549651769 40722150605482603162238827)
    ·
      refine ⟨61083225908223904743358241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40722150605482603162238827 61083225908223904743358241)
      ·
        refine ⟨45812419431167928557518681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61083225908223904743358241 45812419431167928557518681)
        ·
          refine ⟨34359314573375946418139011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45812419431167928557518681 34359314573375946418139011)
          ·
            refine ⟨51538971860063919627208517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34359314573375946418139011 51538971860063919627208517)
            ·
              refine ⟨9663557223761984930101597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51538971860063919627208517 9663557223761984930101597)
              ·
                refine ⟨3623833958910744348788099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9663557223761984930101597 3623833958910744348788099)
                ·
                  refine ⟨5435750938366116523182149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623833958910744348788099 5435750938366116523182149)
                  ·
                    refine ⟨1019203300943646848096653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5435750938366116523182149 1019203300943646848096653)
                    ·
                      rfl

theorem cell23_5954674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_5954674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954674 prefixEnd_5954674 := by exact prefixLift 5954674
  have htrace : WordTrace (prefixWord ++ tailWord_5954674) baseStart_5954674 baseEnd_5954674 := by
    simpa [prefixWord, tailWord_5954674, baseEnd_5954674] using wordTrace_append hprefix tailTrace_5954674
  have hstable : (prefixWord ++ tailWord_5954674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954674).length < 2 ^ (prefixWord ++ tailWord_5954674).sum := by decide
  have hdescent : baseEnd_5954674 < baseStart_5954674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954697 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 3]
def baseStart_5954697 : Nat := 118140960795 + 5954697 * 2 ^ 59
def prefixEnd_5954697 : Nat := 4983230072969 + 3 ^ 40 * 5954697 * 2
def baseEnd_5954697 : Nat := 3057621712885993954302353

theorem tailTrace_5954697 : CollatzResearch.WordTrace tailWord_5954697 prefixEnd_5954697 3057621712885993954302353 := by
  unfold tailWord_5954697
  simp only [CollatzResearch.WordTrace]
  refine ⟨217185642108157225126694345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144790428072104816751129563 217185642108157225126694345)
  ·
    refine ⟨162889231581117918845020759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217185642108157225126694345 162889231581117918845020759)
    ·
      refine ⟨244333847371676878267531139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162889231581117918845020759 244333847371676878267531139)
      ·
        refine ⟨366500771057515317401296709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244333847371676878267531139 366500771057515317401296709)
        ·
          refine ⟨68718894573284122012743133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366500771057515317401296709 68718894573284122012743133)
          ·
            refine ⟨25769585464981545754778675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68718894573284122012743133 25769585464981545754778675)
            ·
              refine ⟨38654378197472318632168013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25769585464981545754778675 38654378197472318632168013)
              ·
                refine ⟨14495391824052119487063005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38654378197472318632168013 14495391824052119487063005)
                ·
                  refine ⟨5435771934019544807648627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14495391824052119487063005 5435771934019544807648627)
                  ·
                    refine ⟨8153657901029317211472941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435771934019544807648627 8153657901029317211472941)
                    ·
                      refine ⟨3057621712885993954302353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8153657901029317211472941 3057621712885993954302353)
                      ·
                        rfl

theorem cell23_5954697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_5954697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954697 prefixEnd_5954697 := by exact prefixLift 5954697
  have htrace : WordTrace (prefixWord ++ tailWord_5954697) baseStart_5954697 baseEnd_5954697 := by
    simpa [prefixWord, tailWord_5954697, baseEnd_5954697] using wordTrace_append hprefix tailTrace_5954697
  have hstable : (prefixWord ++ tailWord_5954697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954697).length < 2 ^ (prefixWord ++ tailWord_5954697).sum := by decide
  have hdescent : baseEnd_5954697 < baseStart_5954697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954714 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5954714 : Nat := 118140960795 + 5954714 * 2 ^ 59
def prefixEnd_5954714 : Nat := 4983230072969 + 3 ^ 40 * 5954714 * 2
def baseEnd_5954714 : Nat := 3057630442057120387789775

theorem tailTrace_5954714 : CollatzResearch.WordTrace tailWord_5954714 prefixEnd_5954714 3057630442057120387789775 := by
  unfold tailWord_5954714
  simp only [CollatzResearch.WordTrace]
  refine ⟨54296565537273909257515799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144790841432730424686708797 54296565537273909257515799)
  ·
    refine ⟨81444848305910863886273699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54296565537273909257515799 81444848305910863886273699)
    ·
      refine ⟨122167272458866295829410549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81444848305910863886273699 122167272458866295829410549)
      ·
        refine ⟨11453181793018715234007239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122167272458866295829410549 11453181793018715234007239)
        ·
          refine ⟨17179772689528072851010859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453181793018715234007239 17179772689528072851010859)
          ·
            refine ⟨25769659034292109276516289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17179772689528072851010859 25769659034292109276516289)
            ·
              refine ⟨19327244275719081957387217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25769659034292109276516289 19327244275719081957387217)
              ·
                refine ⟨14495433206789311468040413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19327244275719081957387217 14495433206789311468040413)
                ·
                  refine ⟨5435787452545991800515155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14495433206789311468040413 5435787452545991800515155)
                  ·
                    refine ⟨8153681178818987700772733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435787452545991800515155 8153681178818987700772733)
                    ·
                      refine ⟨3057630442057120387789775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8153681178818987700772733 3057630442057120387789775)
                      ·
                        rfl

theorem cell23_5954714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5954714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954714 prefixEnd_5954714 := by exact prefixLift 5954714
  have htrace : WordTrace (prefixWord ++ tailWord_5954714) baseStart_5954714 baseEnd_5954714 := by
    simpa [prefixWord, tailWord_5954714, baseEnd_5954714] using wordTrace_append hprefix tailTrace_5954714
  have hstable : (prefixWord ++ tailWord_5954714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954714).length < 2 ^ (prefixWord ++ tailWord_5954714).sum := by decide
  have hdescent : baseEnd_5954714 < baseStart_5954714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954717 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_5954717 : Nat := 118140960795 + 5954717 * 2 ^ 59
def prefixEnd_5954717 : Nat := 4983230072969 + 3 ^ 40 * 5954717 * 2
def baseEnd_5954717 : Nat := 1019210660833027958684087

theorem tailTrace_5954717 : CollatzResearch.WordTrace tailWord_5954717 prefixEnd_5954717 1019210660833027958684087 := by
  unfold tailWord_5954717
  simp only [CollatzResearch.WordTrace]
  refine ⟨217186371568084768542422405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144790914378723179028281603 217186371568084768542422405)
  ·
    refine ⟨40722444669015894101704201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217186371568084768542422405 40722444669015894101704201)
    ·
      refine ⟨30541833501761920576278151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40722444669015894101704201 30541833501761920576278151)
      ·
        refine ⟨45812750252642880864417227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30541833501761920576278151 45812750252642880864417227)
        ·
          refine ⟨68719125378964321296625841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45812750252642880864417227 68719125378964321296625841)
          ·
            refine ⟨51539344034223240972469381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68719125378964321296625841 51539344034223240972469381)
            ·
              refine ⟨9663627006416857682338009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51539344034223240972469381 9663627006416857682338009)
              ·
                refine ⟨7247720254812643261753507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9663627006416857682338009 7247720254812643261753507)
                ·
                  refine ⟨10871580382218964892630261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247720254812643261753507 10871580382218964892630261)
                  ·
                    refine ⟨1019210660833027958684087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10871580382218964892630261 1019210660833027958684087)
                    ·
                      rfl

theorem cell23_5954717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_5954717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954717 prefixEnd_5954717 := by exact prefixLift 5954717
  have htrace : WordTrace (prefixWord ++ tailWord_5954717) baseStart_5954717 baseEnd_5954717 := by
    simpa [prefixWord, tailWord_5954717, baseEnd_5954717] using wordTrace_append hprefix tailTrace_5954717
  have hstable : (prefixWord ++ tailWord_5954717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954717).length < 2 ^ (prefixWord ++ tailWord_5954717).sum := by decide
  have hdescent : baseEnd_5954717 < baseStart_5954717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954748 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5954748 : Nat := 118140960795 + 5954748 * 2 ^ 59
def prefixEnd_5954748 : Nat := 4983230072969 + 3 ^ 40 * 5954748 * 2
def baseEnd_5954748 : Nat := 3057647900399373254764619

theorem tailTrace_5954748 : CollatzResearch.WordTrace tailWord_5954748 prefixEnd_5954748 3057647900399373254764619 := by
  unfold tailWord_5954748
  simp only [CollatzResearch.WordTrace]
  refine ⟨108593751115486230418400449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144791668153981640557867265 108593751115486230418400449)
  ·
    refine ⟨81445313336614672813800337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108593751115486230418400449 81445313336614672813800337)
    ·
      refine ⟨61083985002461004610350253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81445313336614672813800337 61083985002461004610350253)
      ·
        refine ⟨22906494375922876728881345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61083985002461004610350253 22906494375922876728881345)
        ·
          refine ⟨17179870781942157546661009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22906494375922876728881345 17179870781942157546661009)
          ·
            refine ⟨12884903086456618159995757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17179870781942157546661009 12884903086456618159995757)
            ·
              refine ⟨4831838657421231809998409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12884903086456618159995757 4831838657421231809998409)
              ·
                refine ⟨3623878993065923857498807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4831838657421231809998409 3623878993065923857498807)
                ·
                  refine ⟨5435818489598885786248211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623878993065923857498807 5435818489598885786248211)
                  ·
                    refine ⟨8153727734398328679372317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435818489598885786248211 8153727734398328679372317)
                    ·
                      refine ⟨3057647900399373254764619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8153727734398328679372317 3057647900399373254764619)
                      ·
                        rfl

theorem cell23_5954748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5954748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954748 prefixEnd_5954748 := by exact prefixLift 5954748
  have htrace : WordTrace (prefixWord ++ tailWord_5954748) baseStart_5954748 baseEnd_5954748 := by
    simpa [prefixWord, tailWord_5954748, baseEnd_5954748] using wordTrace_append hprefix tailTrace_5954748
  have hstable : (prefixWord ++ tailWord_5954748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954748).length < 2 ^ (prefixWord ++ tailWord_5954748).sum := by decide
  have hdescent : baseEnd_5954748 < baseStart_5954748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954791 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5954791 : Nat := 118140960795 + 5954791 * 2 ^ 59
def prefixEnd_5954791 : Nat := 4983230072969 + 3 ^ 40 * 5954791 * 2
def baseEnd_5954791 : Nat := 3057669980067516586526921

theorem tailTrace_5954791 : CollatzResearch.WordTrace tailWord_5954791 prefixEnd_5954791 3057669980067516586526921 := by
  unfold tailWord_5954791
  simp only [CollatzResearch.WordTrace]
  refine ⟨217189070569816679180616227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144792713713211119453744151 217189070569816679180616227)
  ·
    refine ⟨325783605854725018770924341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217189070569816679180616227 325783605854725018770924341)
    ·
      refine ⟨30542213048880470509774157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325783605854725018770924341 30542213048880470509774157)
      ·
        refine ⟨11453329893330176441165309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30542213048880470509774157 11453329893330176441165309)
        ·
          refine ⟨4294998709998816165436991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11453329893330176441165309 4294998709998816165436991)
          ·
            refine ⟨6442498064998224248155487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294998709998816165436991 6442498064998224248155487)
            ·
              refine ⟨9663747097497336372233231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442498064998224248155487 9663747097497336372233231)
              ·
                refine ⟨14495620646246004558349847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663747097497336372233231 14495620646246004558349847)
                ·
                  refine ⟨21743430969369006837524771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14495620646246004558349847 21743430969369006837524771)
                  ·
                    refine ⟨32615146454053510256287157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21743430969369006837524771 32615146454053510256287157)
                    ·
                      refine ⟨3057669980067516586526921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32615146454053510256287157 3057669980067516586526921)
                      ·
                        rfl

theorem cell23_5954791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5954791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954791 prefixEnd_5954791 := by exact prefixLift 5954791
  have htrace : WordTrace (prefixWord ++ tailWord_5954791) baseStart_5954791 baseEnd_5954791 := by
    simpa [prefixWord, tailWord_5954791, baseEnd_5954791] using wordTrace_append hprefix tailTrace_5954791
  have hstable : (prefixWord ++ tailWord_5954791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954791).length < 2 ^ (prefixWord ++ tailWord_5954791).sum := by decide
  have hdescent : baseEnd_5954791 < baseStart_5954791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954810 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_5954810 : Nat := 118140960795 + 5954810 * 2 ^ 59
def prefixEnd_5954810 : Nat := 4983230072969 + 3 ^ 40 * 5954810 * 2
def baseEnd_5954810 : Nat := 3057679736199952012189333

theorem tailTrace_5954810 : CollatzResearch.WordTrace tailWord_5954810 prefixEnd_5954810 3057679736199952012189333 := by
  unfold tailWord_5954810
  simp only [CollatzResearch.WordTrace]
  refine ⟨54297440889186961356389471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144793175704498563617038589 54297440889186961356389471)
  ·
    refine ⟨81446161333780442034584207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54297440889186961356389471 81446161333780442034584207)
    ·
      refine ⟨122169242000670663051876311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81446161333780442034584207 122169242000670663051876311)
      ·
        refine ⟨183253863001005994577814467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122169242000670663051876311 183253863001005994577814467)
        ·
          refine ⟨274880794501508991866721701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183253863001005994577814467 274880794501508991866721701)
          ·
            refine ⟨51540148969032935975010319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274880794501508991866721701 51540148969032935975010319)
            ·
              refine ⟨77310223453549403962515479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51540148969032935975010319 77310223453549403962515479)
              ·
                refine ⟨115965335180324105943773219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77310223453549403962515479 115965335180324105943773219)
                ·
                  refine ⟨173948002770486158915659829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115965335180324105943773219 173948002770486158915659829)
                  ·
                    refine ⟨16307625259733077398343109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173948002770486158915659829 16307625259733077398343109)
                    ·
                      refine ⟨3057679736199952012189333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16307625259733077398343109 3057679736199952012189333)
                      ·
                        rfl

theorem cell23_5954810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_5954810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954810 prefixEnd_5954810 := by exact prefixLift 5954810
  have htrace : WordTrace (prefixWord ++ tailWord_5954810) baseStart_5954810 baseEnd_5954810 := by
    simpa [prefixWord, tailWord_5954810, baseEnd_5954810] using wordTrace_append hprefix tailTrace_5954810
  have hstable : (prefixWord ++ tailWord_5954810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954810).length < 2 ^ (prefixWord ++ tailWord_5954810).sum := by decide
  have hdescent : baseEnd_5954810 < baseStart_5954810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954844 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5954844 : Nat := 118140960795 + 5954844 * 2 ^ 59
def prefixEnd_5954844 : Nat := 4983230072969 + 3 ^ 40 * 5954844 * 2
def baseEnd_5954844 : Nat := 3057697194542204879164177

theorem tailTrace_5954844 : CollatzResearch.WordTrace tailWord_5954844 prefixEnd_5954844 3057697194542204879164177 := by
  unfold tailWord_5954844
  simp only [CollatzResearch.WordTrace]
  refine ⟨108595501819312334616147793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144794002425749779488197057 108595501819312334616147793)
  ·
    refine ⟨81446626364484250962110845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108595501819312334616147793 81446626364484250962110845)
    ·
      refine ⟨30542484886681594110791567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81446626364484250962110845 30542484886681594110791567)
      ·
        refine ⟨45813727330022391166187351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30542484886681594110791567 45813727330022391166187351)
        ·
          refine ⟨68720590995033586749281027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45813727330022391166187351 68720590995033586749281027)
          ·
            refine ⟨103080886492550380123921541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68720590995033586749281027 103080886492550380123921541)
            ·
              refine ⟨19327666217353196273235289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103080886492550380123921541 19327666217353196273235289)
              ·
                refine ⟨14495749663014897204926467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19327666217353196273235289 14495749663014897204926467)
                ·
                  refine ⟨21743624494522345807389701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14495749663014897204926467 21743624494522345807389701)
                  ·
                    refine ⟨4076929592722939838885569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21743624494522345807389701 4076929592722939838885569)
                    ·
                      refine ⟨3057697194542204879164177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4076929592722939838885569 3057697194542204879164177)
                      ·
                        rfl

theorem cell23_5954844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5954844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954844 prefixEnd_5954844 := by exact prefixLift 5954844
  have htrace : WordTrace (prefixWord ++ tailWord_5954844) baseStart_5954844 baseEnd_5954844 := by
    simpa [prefixWord, tailWord_5954844, baseEnd_5954844] using wordTrace_append hprefix tailTrace_5954844
  have hstable : (prefixWord ++ tailWord_5954844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954844).length < 2 ^ (prefixWord ++ tailWord_5954844).sum := by decide
  have hdescent : baseEnd_5954844 < baseStart_5954844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954867 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 7]
def baseStart_5954867 : Nat := 118140960795 + 5954867 * 2 ^ 59
def prefixEnd_5954867 : Nat := 4983230072969 + 3 ^ 40 * 5954867 * 2
def baseEnd_5954867 : Nat := 339745444955250921019619

theorem tailTrace_5954867 : CollatzResearch.WordTrace tailWord_5954867 prefixEnd_5954867 339745444955250921019619 := by
  unfold tailWord_5954867
  simp only [CollatzResearch.WordTrace]
  refine ⟨217191842517541344160382855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144794561678360896106921903 217191842517541344160382855)
  ·
    refine ⟨325787763776312016240574283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217191842517541344160382855 325787763776312016240574283)
    ·
      refine ⟨488681645664468024360861425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325787763776312016240574283 488681645664468024360861425)
      ·
        refine ⟨366511234248351018270646069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488681645664468024360861425 366511234248351018270646069)
        ·
          refine ⟨34360428210782907962873069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366511234248351018270646069 34360428210782907962873069)
          ·
            refine ⟨12885160579043590486077401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34360428210782907962873069 12885160579043590486077401)
            ·
              refine ⟨9663870434282692864558051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12885160579043590486077401 9663870434282692864558051)
              ·
                refine ⟨14495805651424039296837077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663870434282692864558051 14495805651424039296837077)
                ·
                  refine ⟨339745444955250921019619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14495805651424039296837077 339745444955250921019619)
                  ·
                    rfl

theorem cell23_5954867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 7].length) (baseStart_5954867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954867 prefixEnd_5954867 := by exact prefixLift 5954867
  have htrace : WordTrace (prefixWord ++ tailWord_5954867) baseStart_5954867 baseEnd_5954867 := by
    simpa [prefixWord, tailWord_5954867, baseEnd_5954867] using wordTrace_append hprefix tailTrace_5954867
  have hstable : (prefixWord ++ tailWord_5954867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954867).length < 2 ^ (prefixWord ++ tailWord_5954867).sum := by decide
  have hdescent : baseEnd_5954867 < baseStart_5954867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954880 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_5954880 : Nat := 118140960795 + 5954880 * 2 ^ 59
def prefixEnd_5954880 : Nat := 4983230072969 + 3 ^ 40 * 5954880 * 2
def baseEnd_5954880 : Nat := 1019238559948588912771337

theorem tailTrace_5954880 : CollatzResearch.WordTrace tailWord_5954880 prefixEnd_5954880 1019238559948588912771337 := by
  unfold tailWord_5954880
  simp only [CollatzResearch.WordTrace]
  refine ⟨108596158333247123690303047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144794877777662831587070729 108596158333247123690303047)
  ·
    refine ⟨162894237499870685535454571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108596158333247123690303047 162894237499870685535454571)
    ·
      refine ⟨244341356249806028303181857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162894237499870685535454571 244341356249806028303181857)
      ·
        refine ⟨183256017187354521227386393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244341356249806028303181857 183256017187354521227386393)
        ·
          refine ⟨137442012890515890920539795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183256017187354521227386393 137442012890515890920539795)
          ·
            refine ⟨206163019335773836380809693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137442012890515890920539795 206163019335773836380809693)
            ·
              refine ⟨77311132250915188642803635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206163019335773836380809693 77311132250915188642803635)
              ·
                refine ⟨115966698376372782964205453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77311132250915188642803635 115966698376372782964205453)
                ·
                  refine ⟨43487511891139793611577045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115966698376372782964205453 43487511891139793611577045)
                  ·
                    refine ⟨1019238559948588912771337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43487511891139793611577045 1019238559948588912771337)
                    ·
                      rfl

theorem cell23_5954880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_5954880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954880 prefixEnd_5954880 := by exact prefixLift 5954880
  have htrace : WordTrace (prefixWord ++ tailWord_5954880) baseStart_5954880 baseEnd_5954880 := by
    simpa [prefixWord, tailWord_5954880, baseEnd_5954880] using wordTrace_append hprefix tailTrace_5954880
  have hstable : (prefixWord ++ tailWord_5954880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954880).length < 2 ^ (prefixWord ++ tailWord_5954880).sum := by decide
  have hdescent : baseEnd_5954880 < baseStart_5954880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954884 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 7]
def baseStart_5954884 : Nat := 118140960795 + 5954884 * 2 ^ 59
def prefixEnd_5954884 : Nat := 4983230072969 + 3 ^ 40 * 5954884 * 2
def baseEnd_5954884 : Nat := 339746414863153858073777

theorem tailTrace_5954884 : CollatzResearch.WordTrace tailWord_5954884 prefixEnd_5954884 339746414863153858073777 := by
  unfold tailWord_5954884
  simp only [CollatzResearch.WordTrace]
  refine ⟨108596231279239878031875853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144794975038986504042501137 108596231279239878031875853)
  ·
    refine ⟨40723586729714954261953445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108596231279239878031875853 40723586729714954261953445)
    ·
      refine ⟨7635672511821553924116271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40723586729714954261953445 7635672511821553924116271)
      ·
        refine ⟨11453508767732330886174407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7635672511821553924116271 11453508767732330886174407)
        ·
          refine ⟨17180263151598496329261611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453508767732330886174407 17180263151598496329261611)
          ·
            refine ⟨25770394727397744493892417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17180263151598496329261611 25770394727397744493892417)
            ·
              refine ⟨19327796045548308370419313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25770394727397744493892417 19327796045548308370419313)
              ·
                refine ⟨14495847034161231277814485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19327796045548308370419313 14495847034161231277814485)
                ·
                  refine ⟨339746414863153858073777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14495847034161231277814485 339746414863153858073777)
                  ·
                    rfl

theorem cell23_5954884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_5954884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954884 prefixEnd_5954884 := by exact prefixLift 5954884
  have htrace : WordTrace (prefixWord ++ tailWord_5954884) baseStart_5954884 baseEnd_5954884 := by
    simpa [prefixWord, tailWord_5954884, baseEnd_5954884] using wordTrace_append hprefix tailTrace_5954884
  have hstable : (prefixWord ++ tailWord_5954884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954884).length < 2 ^ (prefixWord ++ tailWord_5954884).sum := by decide
  have hdescent : baseEnd_5954884 < baseStart_5954884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954897 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_5954897 : Nat := 118140960795 + 5954897 * 2 ^ 59
def prefixEnd_5954897 : Nat := 4983230072969 + 3 ^ 40 * 5954897 * 2
def baseEnd_5954897 : Nat := 1019241469672297723933811

theorem tailTrace_5954897 : CollatzResearch.WordTrace tailWord_5954897 prefixEnd_5954897 1019241469672297723933811 := by
  unfold tailWord_5954897
  simp only [CollatzResearch.WordTrace]
  refine ⟨217192936707432659283974945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144795291138288439522649963 217192936707432659283974945)
  ·
    refine ⟨162894702530574494462981209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217192936707432659283974945 162894702530574494462981209)
    ·
      refine ⟨122171026897930870847235907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162894702530574494462981209 122171026897930870847235907)
      ·
        refine ⟨183256540346896306270853861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122171026897930870847235907 183256540346896306270853861)
        ·
          refine ⟨34360601315043057425785099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183256540346896306270853861 34360601315043057425785099)
          ·
            refine ⟨51540901972564586138677649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34360601315043057425785099 51540901972564586138677649)
            ·
              refine ⟨38655676479423439604008237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51540901972564586138677649 38655676479423439604008237)
              ·
                refine ⟨14495878679783789851503089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38655676479423439604008237 14495878679783789851503089)
                ·
                  refine ⟨10871909009837842388627317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14495878679783789851503089 10871909009837842388627317)
                  ·
                    refine ⟨1019241469672297723933811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10871909009837842388627317 1019241469672297723933811)
                    ·
                      rfl

theorem cell23_5954897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_5954897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954897 prefixEnd_5954897 := by exact prefixLift 5954897
  have htrace : WordTrace (prefixWord ++ tailWord_5954897) baseStart_5954897 baseEnd_5954897 := by
    simpa [prefixWord, tailWord_5954897, baseEnd_5954897] using wordTrace_append hprefix tailTrace_5954897
  have hstable : (prefixWord ++ tailWord_5954897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954897).length < 2 ^ (prefixWord ++ tailWord_5954897).sum := by decide
  have hdescent : baseEnd_5954897 < baseStart_5954897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954901 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 5]
def baseStart_5954901 : Nat := 118140960795 + 5954901 * 2 ^ 59
def prefixEnd_5954901 : Nat := 4983230072969 + 3 ^ 40 * 5954901 * 2
def baseEnd_5954901 : Nat := 339747384771056795127935

theorem tailTrace_5954901 : CollatzResearch.WordTrace tailWord_5954901 prefixEnd_5954901 339747384771056795127935 := by
  unfold tailWord_5954901
  simp only [CollatzResearch.WordTrace]
  refine ⟨217193082599418167967120557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144795388399612111978080371 217193082599418167967120557)
  ·
    refine ⟨81447405974781812987670209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217193082599418167967120557 81447405974781812987670209)
    ·
      refine ⟨61085554481086359740752657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81447405974781812987670209 61085554481086359740752657)
      ·
        refine ⟨45814165860814769805564493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61085554481086359740752657 45814165860814769805564493)
        ·
          refine ⟨17180312197805538677086685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45814165860814769805564493 17180312197805538677086685)
          ·
            refine ⟨6442617074177077003907507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17180312197805538677086685 6442617074177077003907507)
            ·
              refine ⟨9663925611265615505861261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442617074177077003907507 9663925611265615505861261)
              ·
                refine ⟨3623972104224605814697973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9663925611265615505861261 3623972104224605814697973)
                ·
                  refine ⟨339747384771056795127935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3623972104224605814697973 339747384771056795127935)
                  ·
                    rfl

theorem cell23_5954901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_5954901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954901 prefixEnd_5954901 := by exact prefixLift 5954901
  have htrace : WordTrace (prefixWord ++ tailWord_5954901) baseStart_5954901 baseEnd_5954901 := by
    simpa [prefixWord, tailWord_5954901, baseEnd_5954901] using wordTrace_append hprefix tailTrace_5954901
  have hstable : (prefixWord ++ tailWord_5954901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954901).length < 2 ^ (prefixWord ++ tailWord_5954901).sum := by decide
  have hdescent : baseEnd_5954901 < baseStart_5954901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954914 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_5954914 : Nat := 118140960795 + 5954914 * 2 ^ 59
def prefixEnd_5954914 : Nat := 4983230072969 + 3 ^ 40 * 5954914 * 2
def baseEnd_5954914 : Nat := 1019244379396006535096285

theorem tailTrace_5954914 : CollatzResearch.WordTrace tailWord_5954914 prefixEnd_5954914 1019244379396006535096285 := by
  unfold tailWord_5954914
  simp only [CollatzResearch.WordTrace]
  refine ⟨54298389187092767796835949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144795704498914047458229197 54298389187092767796835949)
  ·
    refine ⟨20361895945159787923813481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54298389187092767796835949 20361895945159787923813481)
    ·
      refine ⟨15271421958869840942860111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20361895945159787923813481 15271421958869840942860111)
      ·
        refine ⟨22907132938304761414290167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15271421958869840942860111 22907132938304761414290167)
        ·
          refine ⟨34360699407457142121435251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22907132938304761414290167 34360699407457142121435251)
          ·
            refine ⟨51541049111185713182152877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34360699407457142121435251 51541049111185713182152877)
            ·
              refine ⟨19327893416694642443307329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51541049111185713182152877 19327893416694642443307329)
              ·
                refine ⟨14495920062520981832480497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19327893416694642443307329 14495920062520981832480497)
                ·
                  refine ⟨10871940046890736374360373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14495920062520981832480497 10871940046890736374360373)
                  ·
                    refine ⟨1019244379396006535096285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10871940046890736374360373 1019244379396006535096285)
                    ·
                      rfl

theorem cell23_5954914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_5954914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954914 prefixEnd_5954914 := by exact prefixLift 5954914
  have htrace : WordTrace (prefixWord ++ tailWord_5954914) baseStart_5954914 baseEnd_5954914 := by
    simpa [prefixWord, tailWord_5954914, baseEnd_5954914] using wordTrace_append hprefix tailTrace_5954914
  have hstable : (prefixWord ++ tailWord_5954914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954914).length < 2 ^ (prefixWord ++ tailWord_5954914).sum := by decide
  have hdescent : baseEnd_5954914 < baseStart_5954914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954937 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_5954937 : Nat := 118140960795 + 5954937 * 2 ^ 59
def prefixEnd_5954937 : Nat := 4983230072969 + 3 ^ 40 * 5954937 * 2
def baseEnd_5954937 : Nat := 3057744948243073015301249

theorem tailTrace_5954937 : CollatzResearch.WordTrace tailWord_5954937 prefixEnd_5954937 3057744948243073015301249 := by
  unfold tailWord_5954937
  simp only [CollatzResearch.WordTrace]
  refine ⟨217194395627287746115431065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144796263751525164076954043 217194395627287746115431065)
  ·
    refine ⟨162895796720465809586573299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217194395627287746115431065 162895796720465809586573299)
    ·
      refine ⟨244343695080698714379859949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162895796720465809586573299 244343695080698714379859949)
      ·
        refine ⟨91628885655262017892447481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244343695080698714379859949 91628885655262017892447481)
        ·
          refine ⟨68721664241446513419335611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91628885655262017892447481 68721664241446513419335611)
          ·
            refine ⟨103082496362169770129003417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68721664241446513419335611 103082496362169770129003417)
            ·
              refine ⟨77311872271627327596752563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103082496362169770129003417 77311872271627327596752563)
              ·
                refine ⟨115967808407440991395128845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77311872271627327596752563 115967808407440991395128845)
                ·
                  refine ⟨43487928152790371773173317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115967808407440991395128845 43487928152790371773173317)
                  ·
                    refine ⟨8153986528648194707469997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43487928152790371773173317 8153986528648194707469997)
                    ·
                      refine ⟨3057744948243073015301249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8153986528648194707469997 3057744948243073015301249)
                      ·
                        rfl

theorem cell23_5954937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_5954937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954937 prefixEnd_5954937 := by exact prefixLift 5954937
  have htrace : WordTrace (prefixWord ++ tailWord_5954937) baseStart_5954937 baseEnd_5954937 := by
    simpa [prefixWord, tailWord_5954937, baseEnd_5954937] using wordTrace_append hprefix tailTrace_5954937
  have hstable : (prefixWord ++ tailWord_5954937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954937).length < 2 ^ (prefixWord ++ tailWord_5954937).sum := by decide
  have hdescent : baseEnd_5954937 < baseStart_5954937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5954978 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_5954978 : Nat := 118140960795 + 5954978 * 2 ^ 59
def prefixEnd_5954978 : Nat := 4983230072969 + 3 ^ 40 * 5954978 * 2
def baseEnd_5954978 : Nat := 1019255333649969118296187

theorem tailTrace_5954978 : CollatzResearch.WordTrace tailWord_5954978 prefixEnd_5954978 1019255333649969118296187 := by
  unfold tailWord_5954978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54298972755034802529418397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144797260680092806745115725 54298972755034802529418397)
  ·
    refine ⟨20362114783138050948531899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54298972755034802529418397 20362114783138050948531899)
    ·
      refine ⟨30543172174707076422797849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20362114783138050948531899 30543172174707076422797849)
      ·
        refine ⟨22907379131030307317098387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30543172174707076422797849 22907379131030307317098387)
        ·
          refine ⟨34361068696545460975647581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22907379131030307317098387 34361068696545460975647581)
          ·
            refine ⟨12885400761204547865867843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34361068696545460975647581 12885400761204547865867843)
            ·
              refine ⟨19328101141806821798801765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12885400761204547865867843 19328101141806821798801765)
              ·
                refine ⟨3624018964088779087275331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19328101141806821798801765 3624018964088779087275331)
                ·
                  refine ⟨5436028446133168630912997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624018964088779087275331 5436028446133168630912997)
                  ·
                    refine ⟨1019255333649969118296187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436028446133168630912997 1019255333649969118296187)
                    ·
                      rfl

theorem cell23_5954978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_5954978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5954978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5954978 prefixEnd_5954978 := by exact prefixLift 5954978
  have htrace : WordTrace (prefixWord ++ tailWord_5954978) baseStart_5954978 baseEnd_5954978 := by
    simpa [prefixWord, tailWord_5954978, baseEnd_5954978] using wordTrace_append hprefix tailTrace_5954978
  have hstable : (prefixWord ++ tailWord_5954978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5954978).length < 2 ^ (prefixWord ++ tailWord_5954978).sum := by decide
  have hdescent : baseEnd_5954978 < baseStart_5954978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5954978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955011 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 2, 3, 2]
def baseStart_5955011 : Nat := 118140960795 + 5955011 * 2 ^ 59
def prefixEnd_5955011 : Nat := 4983230072969 + 3 ^ 40 * 5955011 * 2
def baseEnd_5955011 : Nat := 3057782945811505725775909

theorem tailTrace_5955011 : CollatzResearch.WordTrace tailWord_5955011 prefixEnd_5955011 3057782945811505725775909 := by
  unfold tailWord_5955011
  simp only [CollatzResearch.WordTrace]
  refine ⟨217197094629019656753624887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144798063086013104502416591 217197094629019656753624887)
  ·
    refine ⟨325795641943529485130437331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217197094629019656753624887 325795641943529485130437331)
    ·
      refine ⟨488693462915294227695655997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325795641943529485130437331 488693462915294227695655997)
      ·
        refine ⟨183260048593235335385870999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488693462915294227695655997 183260048593235335385870999)
        ·
          refine ⟨274890072889853003078806499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183260048593235335385870999 274890072889853003078806499)
          ·
            refine ⟨412335109334779504618209749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274890072889853003078806499 412335109334779504618209749)
            ·
              refine ⟨9664104125033894639489291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 412335109334779504618209749 9664104125033894639489291)
              ·
                refine ⟨14496156187550841959233937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664104125033894639489291 14496156187550841959233937)
                ·
                  refine ⟨10872117140663131469425453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14496156187550841959233937 10872117140663131469425453)
                  ·
                    refine ⟨4077043927748674301034545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10872117140663131469425453 4077043927748674301034545)
                    ·
                      refine ⟨3057782945811505725775909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4077043927748674301034545 3057782945811505725775909)
                      ·
                        rfl

theorem cell23_5955011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_5955011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955011 prefixEnd_5955011 := by exact prefixLift 5955011
  have htrace : WordTrace (prefixWord ++ tailWord_5955011) baseStart_5955011 baseEnd_5955011 := by
    simpa [prefixWord, tailWord_5955011, baseEnd_5955011] using wordTrace_append hprefix tailTrace_5955011
  have hstable : (prefixWord ++ tailWord_5955011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955011).length < 2 ^ (prefixWord ++ tailWord_5955011).sum := by decide
  have hdescent : baseEnd_5955011 < baseStart_5955011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955018 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_5955018 : Nat := 118140960795 + 5955018 * 2 ^ 59
def prefixEnd_5955018 : Nat := 4983230072969 + 3 ^ 40 * 5955018 * 2
def baseEnd_5955018 : Nat := 3057786540176087198388377

theorem tailTrace_5955018 : CollatzResearch.WordTrace tailWord_5955018 prefixEnd_5955018 3057786540176087198388377 := by
  unfold tailWord_5955018
  simp only [CollatzResearch.WordTrace]
  refine ⟨54299337484998574237282427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144798233293329531299419805 54299337484998574237282427)
  ·
    refine ⟨81449006227497861355923641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54299337484998574237282427 81449006227497861355923641)
    ·
      refine ⟨61086754670623396016942731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81449006227497861355923641 61086754670623396016942731)
      ·
        refine ⟨91630132005935094025414097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61086754670623396016942731 91630132005935094025414097)
        ·
          refine ⟨68722599004451320519060573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91630132005935094025414097 68722599004451320519060573)
          ·
            refine ⟨25770974626669245194647715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68722599004451320519060573 25770974626669245194647715)
            ·
              refine ⟨38656461940003867791971573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25770974626669245194647715 38656461940003867791971573)
              ·
                refine ⟨3624043306875362605497335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38656461940003867791971573 3624043306875362605497335)
                ·
                  refine ⟨5436064960313043908246003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624043306875362605497335 5436064960313043908246003)
                  ·
                    refine ⟨8154097440469565862369005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5436064960313043908246003 8154097440469565862369005)
                    ·
                      refine ⟨3057786540176087198388377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154097440469565862369005 3057786540176087198388377)
                      ·
                        rfl

theorem cell23_5955018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_5955018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955018 prefixEnd_5955018 := by exact prefixLift 5955018
  have htrace : WordTrace (prefixWord ++ tailWord_5955018) baseStart_5955018 baseEnd_5955018 := by
    simpa [prefixWord, tailWord_5955018, baseEnd_5955018] using wordTrace_append hprefix tailTrace_5955018
  have hstable : (prefixWord ++ tailWord_5955018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955018).length < 2 ^ (prefixWord ++ tailWord_5955018).sum := by decide
  have hdescent : baseEnd_5955018 < baseStart_5955018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955024 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4]
def baseStart_5955024 : Nat := 118140960795 + 5955024 * 2 ^ 59
def prefixEnd_5955024 : Nat := 4983230072969 + 3 ^ 40 * 5955024 * 2
def baseEnd_5955024 : Nat := 3057789621060014174913349

theorem tailTrace_5955024 : CollatzResearch.WordTrace tailWord_5955024 prefixEnd_5955024 3057789621060014174913349 := by
  unfold tailWord_5955024
  simp only [CollatzResearch.WordTrace]
  refine ⟨108598784388986279986924063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144798379185315039982565417 108598784388986279986924063)
  ·
    refine ⟨162898176583479419980386095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108598784388986279986924063 162898176583479419980386095)
    ·
      refine ⟨244347264875219129970579143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162898176583479419980386095 244347264875219129970579143)
      ·
        refine ⟨366520897312828694955868715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244347264875219129970579143 366520897312828694955868715)
        ·
          refine ⟨549781345969243042433803073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366520897312828694955868715 549781345969243042433803073)
          ·
            refine ⟨412336009476932281825352305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549781345969243042433803073 412336009476932281825352305)
            ·
              refine ⟨309252007107699211369014229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412336009476932281825352305 309252007107699211369014229)
              ·
                refine ⟨7248093916586700266461271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 309252007107699211369014229 7248093916586700266461271)
                ·
                  refine ⟨10872140874880050399691907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248093916586700266461271 10872140874880050399691907)
                  ·
                    refine ⟨16308211312320075599537861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10872140874880050399691907 16308211312320075599537861)
                    ·
                      refine ⟨3057789621060014174913349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16308211312320075599537861 3057789621060014174913349)
                      ·
                        rfl

theorem cell23_5955024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_5955024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955024 prefixEnd_5955024 := by exact prefixLift 5955024
  have htrace : WordTrace (prefixWord ++ tailWord_5955024) baseStart_5955024 baseEnd_5955024 := by
    simpa [prefixWord, tailWord_5955024, baseEnd_5955024] using wordTrace_append hprefix tailTrace_5955024
  have hstable : (prefixWord ++ tailWord_5955024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955024).length < 2 ^ (prefixWord ++ tailWord_5955024).sum := by decide
  have hdescent : baseEnd_5955024 < baseStart_5955024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955044 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_5955044 : Nat := 118140960795 + 5955044 * 2 ^ 59
def prefixEnd_5955044 : Nat := 4983230072969 + 3 ^ 40 * 5955044 * 2
def baseEnd_5955044 : Nat := 3057799890673104096663257

theorem tailTrace_5955044 : CollatzResearch.WordTrace tailWord_5955044 prefixEnd_5955044 3057799890673104096663257 := by
  unfold tailWord_5955044
  simp only [CollatzResearch.WordTrace]
  refine ⟨108599149118950051694788093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144798865491933402259717457 108599149118950051694788093)
  ·
    refine ⟨40724680919606269385545535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108599149118950051694788093 40724680919606269385545535)
    ·
      refine ⟨61087021379409404078318303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40724680919606269385545535 61087021379409404078318303)
      ·
        refine ⟨91630532069114106117477455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61087021379409404078318303 91630532069114106117477455)
        ·
          refine ⟨137445798103671159176216183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91630532069114106117477455 137445798103671159176216183)
          ·
            refine ⟨206168697155506738764324275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137445798103671159176216183 206168697155506738764324275)
            ·
              refine ⟨309253045733260108146486413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206168697155506738764324275 309253045733260108146486413)
              ·
                refine ⟨115969892149972540554932405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309253045733260108146486413 115969892149972540554932405)
                ·
                  refine ⟨10872177389059925677024913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115969892149972540554932405 10872177389059925677024913)
                  ·
                    refine ⟨8154133041794944257768685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10872177389059925677024913 8154133041794944257768685)
                    ·
                      refine ⟨3057799890673104096663257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154133041794944257768685 3057799890673104096663257)
                      ·
                        rfl

theorem cell23_5955044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_5955044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955044 prefixEnd_5955044 := by exact prefixLift 5955044
  have htrace : WordTrace (prefixWord ++ tailWord_5955044) baseStart_5955044 baseEnd_5955044 := by
    simpa [prefixWord, tailWord_5955044, baseEnd_5955044] using wordTrace_append hprefix tailTrace_5955044
  have hstable : (prefixWord ++ tailWord_5955044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955044).length < 2 ^ (prefixWord ++ tailWord_5955044).sum := by decide
  have hdescent : baseEnd_5955044 < baseStart_5955044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955054 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_5955054 : Nat := 118140960795 + 5955054 * 2 ^ 59
def prefixEnd_5955054 : Nat := 4983230072969 + 3 ^ 40 * 5955054 * 2
def baseEnd_5955054 : Nat := 3057805025479649057538211

theorem tailTrace_5955054 : CollatzResearch.WordTrace tailWord_5955054 prefixEnd_5955054 3057805025479649057538211 := by
  unfold tailWord_5955054
  simp only [CollatzResearch.WordTrace]
  refine ⟨27149832870982984387180027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144799108645242583398293477 27149832870982984387180027)
  ·
    refine ⟨40724749306474476580770041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27149832870982984387180027 40724749306474476580770041)
    ·
      refine ⟨30543561979855857435577531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40724749306474476580770041 30543561979855857435577531)
      ·
        refine ⟨45815342969783786153366297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30543561979855857435577531 45815342969783786153366297)
        ·
          refine ⟨34361507227337839615024723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45815342969783786153366297 34361507227337839615024723)
          ·
            refine ⟨51542260841006759422537085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34361507227337839615024723 51542260841006759422537085)
            ·
              refine ⟨19328347815377534783451407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51542260841006759422537085 19328347815377534783451407)
              ·
                refine ⟨28992521723066302175177111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19328347815377534783451407 28992521723066302175177111)
                ·
                  refine ⟨43488782584599453262765667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28992521723066302175177111 43488782584599453262765667)
                  ·
                    refine ⟨65233173876899179894148501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43488782584599453262765667 65233173876899179894148501)
                    ·
                      refine ⟨3057805025479649057538211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65233173876899179894148501 3057805025479649057538211)
                      ·
                        rfl

theorem cell23_5955054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_5955054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955054 prefixEnd_5955054 := by exact prefixLift 5955054
  have htrace : WordTrace (prefixWord ++ tailWord_5955054) baseStart_5955054 baseEnd_5955054 := by
    simpa [prefixWord, tailWord_5955054, baseEnd_5955054] using wordTrace_append hprefix tailTrace_5955054
  have hstable : (prefixWord ++ tailWord_5955054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955054).length < 2 ^ (prefixWord ++ tailWord_5955054).sum := by decide
  have hdescent : baseEnd_5955054 < baseStart_5955054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955058 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_5955058 : Nat := 118140960795 + 5955058 * 2 ^ 59
def prefixEnd_5955058 : Nat := 4983230072969 + 3 ^ 40 * 5955058 * 2
def baseEnd_5955058 : Nat := 3057807079402267041888193

theorem tailTrace_5955058 : CollatzResearch.WordTrace tailWord_5955058 prefixEnd_5955058 3057807079402267041888193 := by
  unfold tailWord_5955058
  simp only [CollatzResearch.WordTrace]
  refine ⟨54299702214962345945146457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144799205906566255853723885 54299702214962345945146457)
  ·
    refine ⟨40724776661221759458859843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54299702214962345945146457 40724776661221759458859843)
    ·
      refine ⟨61087164991832639188289765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40724776661221759458859843 61087164991832639188289765)
      ·
        refine ⟨11453843435968619847804331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61087164991832639188289765 11453843435968619847804331)
        ·
          refine ⟨17180765153952929771706497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453843435968619847804331 17180765153952929771706497)
          ·
            refine ⟨12885573865464697328779873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17180765153952929771706497 12885573865464697328779873)
            ·
              refine ⟨9664180399098522996584905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12885573865464697328779873 9664180399098522996584905)
              ·
                refine ⟨7248135299323892247438679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9664180399098522996584905 7248135299323892247438679)
                ·
                  refine ⟨10872202948985838371158019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248135299323892247438679 10872202948985838371158019)
                  ·
                    refine ⟨16308304423478757556737029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10872202948985838371158019 16308304423478757556737029)
                    ·
                      refine ⟨3057807079402267041888193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16308304423478757556737029 3057807079402267041888193)
                      ·
                        rfl

theorem cell23_5955058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_5955058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955058 prefixEnd_5955058 := by exact prefixLift 5955058
  have htrace : WordTrace (prefixWord ++ tailWord_5955058) baseStart_5955058 baseEnd_5955058 := by
    simpa [prefixWord, tailWord_5955058, baseEnd_5955058] using wordTrace_append hprefix tailTrace_5955058
  have hstable : (prefixWord ++ tailWord_5955058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955058).length < 2 ^ (prefixWord ++ tailWord_5955058).sum := by decide
  have hdescent : baseEnd_5955058 < baseStart_5955058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955064 : List Nat := [2, 1, 2, 1, 1, 5, 4, 7]
def baseStart_5955064 : Nat := 118140960795 + 5955064 * 2 ^ 59
def prefixEnd_5955064 : Nat := 4983230072969 + 3 ^ 40 * 5955064 * 2
def baseEnd_5955064 : Nat := 113252228158747926607895

theorem tailTrace_5955064 : CollatzResearch.WordTrace tailWord_5955064 prefixEnd_5955064 113252228158747926607895 := by
  unfold tailWord_5955064
  simp only [CollatzResearch.WordTrace]
  refine ⟨108599513848913823402652123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144799351798551764536869497 108599513848913823402652123)
  ·
    refine ⟨162899270773370735103978185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108599513848913823402652123 162899270773370735103978185)
    ·
      refine ⟨122174453080028051327983639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162899270773370735103978185 122174453080028051327983639)
      ·
        refine ⟨183261679620042076991975459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122174453080028051327983639 183261679620042076991975459)
        ·
          refine ⟨274892519430063115487963189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183261679620042076991975459 274892519430063115487963189)
          ·
            refine ⟨25771173696568417076996549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274892519430063115487963189 25771173696568417076996549)
            ·
              refine ⟨4832095068106578201936853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25771173696568417076996549 4832095068106578201936853)
              ·
                refine ⟨113252228158747926607895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4832095068106578201936853 113252228158747926607895)
                ·
                  rfl

theorem cell23_5955064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 7].length) (baseStart_5955064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955064 prefixEnd_5955064 := by exact prefixLift 5955064
  have htrace : WordTrace (prefixWord ++ tailWord_5955064) baseStart_5955064 baseEnd_5955064 := by
    simpa [prefixWord, tailWord_5955064, baseEnd_5955064] using wordTrace_append hprefix tailTrace_5955064
  have hstable : (prefixWord ++ tailWord_5955064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955064).length < 2 ^ (prefixWord ++ tailWord_5955064).sum := by decide
  have hdescent : baseEnd_5955064 < baseStart_5955064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955077 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_5955077 : Nat := 118140960795 + 5955077 * 2 ^ 59
def prefixEnd_5955077 : Nat := 4983230072969 + 3 ^ 40 * 5955077 * 2
def baseEnd_5955077 : Nat := 1019272278511567489183535

theorem tailTrace_5955077 : CollatzResearch.WordTrace tailWord_5955077 prefixEnd_5955077 1019272278511567489183535 := by
  unfold tailWord_5955077
  simp only [CollatzResearch.WordTrace]
  refine ⟨217199501846780550025527485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144799667897853700017018323 217199501846780550025527485)
  ·
    refine ⟨81449813192542706259572807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217199501846780550025527485 81449813192542706259572807)
    ·
      refine ⟨122174719788814059389359211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81449813192542706259572807 122174719788814059389359211)
      ·
        refine ⟨183262079683221089084038817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122174719788814059389359211 183262079683221089084038817)
        ·
          refine ⟨137446559762415816813029113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183262079683221089084038817 137446559762415816813029113)
          ·
            refine ⟨103084919821811862609771835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137446559762415816813029113 103084919821811862609771835)
            ·
              refine ⟨154627379732717793914657753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103084919821811862609771835 154627379732717793914657753)
              ·
                refine ⟨115970534799538345435993315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154627379732717793914657753 115970534799538345435993315)
                ·
                  refine ⟨173955802199307518153989973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115970534799538345435993315 173955802199307518153989973)
                  ·
                    refine ⟨1019272278511567489183535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 173955802199307518153989973 1019272278511567489183535)
                    ·
                      rfl

theorem cell23_5955077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_5955077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955077 prefixEnd_5955077 := by exact prefixLift 5955077
  have htrace : WordTrace (prefixWord ++ tailWord_5955077) baseStart_5955077 baseEnd_5955077 := by
    simpa [prefixWord, tailWord_5955077, baseEnd_5955077] using wordTrace_append hprefix tailTrace_5955077
  have hstable : (prefixWord ++ tailWord_5955077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955077).length < 2 ^ (prefixWord ++ tailWord_5955077).sum := by decide
  have hdescent : baseEnd_5955077 < baseStart_5955077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955087 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_5955087 : Nat := 118140960795 + 5955087 * 2 ^ 59
def prefixEnd_5955087 : Nat := 4983230072969 + 3 ^ 40 * 5955087 * 2
def baseEnd_5955087 : Nat := 3057821970341247428425559

theorem tailTrace_5955087 : CollatzResearch.WordTrace tailWord_5955087 prefixEnd_5955087 3057821970341247428425559 := by
  unfold tailWord_5955087
  simp only [CollatzResearch.WordTrace]
  refine ⟨217199866576744321733391515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144799911051162881155594343 217199866576744321733391515)
  ·
    refine ⟨325799799865116482600087273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217199866576744321733391515 325799799865116482600087273)
    ·
      refine ⟨244349849898837361950065455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325799799865116482600087273 244349849898837361950065455)
      ·
        refine ⟨366524774848256042925098183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244349849898837361950065455 366524774848256042925098183)
        ·
          refine ⟨549787162272384064387647275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366524774848256042925098183 549787162272384064387647275)
          ·
            refine ⟨824680743408576096581470913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549787162272384064387647275 824680743408576096581470913)
            ·
              refine ⟨618510557556432072436103185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824680743408576096581470913 618510557556432072436103185)
              ·
                refine ⟨463882918167324054327077389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618510557556432072436103185 463882918167324054327077389)
                ·
                  refine ⟨173956094312746520372654021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463882918167324054327077389 173956094312746520372654021)
                  ·
                    refine ⟨32616767683639972569872629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173956094312746520372654021 32616767683639972569872629)
                    ·
                      refine ⟨3057821970341247428425559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32616767683639972569872629 3057821970341247428425559)
                      ·
                        rfl

theorem cell23_5955087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_5955087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955087 prefixEnd_5955087 := by exact prefixLift 5955087
  have htrace : WordTrace (prefixWord ++ tailWord_5955087) baseStart_5955087 baseEnd_5955087 := by
    simpa [prefixWord, tailWord_5955087, baseEnd_5955087] using wordTrace_append hprefix tailTrace_5955087
  have hstable : (prefixWord ++ tailWord_5955087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955087).length < 2 ^ (prefixWord ++ tailWord_5955087).sum := by decide
  have hdescent : baseEnd_5955087 < baseStart_5955087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955091 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 3]
def baseStart_5955091 : Nat := 118140960795 + 5955091 * 2 ^ 59
def prefixEnd_5955091 : Nat := 4983230072969 + 3 ^ 40 * 5955091 * 2
def baseEnd_5955091 : Nat := 3057824024263865412775541

theorem tailTrace_5955091 : CollatzResearch.WordTrace tailWord_5955091 prefixEnd_5955091 3057824024263865412775541 := by
  unfold tailWord_5955091
  simp only [CollatzResearch.WordTrace]
  refine ⟨217200012468729830416537127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144800008312486553611024751 217200012468729830416537127)
  ·
    refine ⟨325800018703094745624805691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217200012468729830416537127 325800018703094745624805691)
    ·
      refine ⟨488700028054642118437208537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325800018703094745624805691 488700028054642118437208537)
      ·
        refine ⟨366525021040981588827906403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488700028054642118437208537 366525021040981588827906403)
        ·
          refine ⟨549787531561472383241859605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366525021040981588827906403 549787531561472383241859605)
          ·
            refine ⟨25771290541944017964462169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 549787531561472383241859605 25771290541944017964462169)
            ·
              refine ⟨19328467906458013473346627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25771290541944017964462169 19328467906458013473346627)
              ·
                refine ⟨28992701859687020210019941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19328467906458013473346627 28992701859687020210019941)
                ·
                  refine ⟨5436131598691316289378739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28992701859687020210019941 5436131598691316289378739)
                  ·
                    refine ⟨8154197398036974434068109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5436131598691316289378739 8154197398036974434068109)
                    ·
                      refine ⟨3057824024263865412775541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154197398036974434068109 3057824024263865412775541)
                      ·
                        rfl

theorem cell23_5955091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_5955091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955091 prefixEnd_5955091 := by exact prefixLift 5955091
  have htrace : WordTrace (prefixWord ++ tailWord_5955091) baseStart_5955091 baseEnd_5955091 := by
    simpa [prefixWord, tailWord_5955091, baseEnd_5955091] using wordTrace_append hprefix tailTrace_5955091
  have hstable : (prefixWord ++ tailWord_5955091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955091).length < 2 ^ (prefixWord ++ tailWord_5955091).sum := by decide
  have hdescent : baseEnd_5955091 < baseStart_5955091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955112 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5955112 : Nat := 118140960795 + 5955112 * 2 ^ 59
def prefixEnd_5955112 : Nat := 4983230072969 + 3 ^ 40 * 5955112 * 2
def baseEnd_5955112 : Nat := 3057834807357609830612945

theorem tailTrace_5955112 : CollatzResearch.WordTrace tailWord_5955112 prefixEnd_5955112 3057834807357609830612945 := by
  unfold tailWord_5955112
  simp only [CollatzResearch.WordTrace]
  refine ⟨108600389200826875501525795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144800518934435834002034393 108600389200826875501525795)
  ·
    refine ⟨162900583801240313252288693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108600389200826875501525795 162900583801240313252288693)
    ·
      refine ⟨15271929731366279367402065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162900583801240313252288693 15271929731366279367402065)
      ·
        refine ⟨11453947298524709525551549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15271929731366279367402065 11453947298524709525551549)
        ·
          refine ⟨4295230236946766072081831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11453947298524709525551549 4295230236946766072081831)
          ·
            refine ⟨6442845355420149108122747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295230236946766072081831 6442845355420149108122747)
            ·
              refine ⟨9664268033130223662184121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442845355420149108122747 9664268033130223662184121)
              ·
                refine ⟨7248201024847667746638091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9664268033130223662184121 7248201024847667746638091)
                ·
                  refine ⟨10872301537271501619957137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248201024847667746638091 10872301537271501619957137)
                  ·
                    refine ⟨8154226152953626214967853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10872301537271501619957137 8154226152953626214967853)
                    ·
                      refine ⟨3057834807357609830612945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154226152953626214967853 3057834807357609830612945)
                      ·
                        rfl

theorem cell23_5955112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5955112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955112 prefixEnd_5955112 := by exact prefixLift 5955112
  have htrace : WordTrace (prefixWord ++ tailWord_5955112) baseStart_5955112 baseEnd_5955112 := by
    simpa [prefixWord, tailWord_5955112, baseEnd_5955112] using wordTrace_append hprefix tailTrace_5955112
  have hstable : (prefixWord ++ tailWord_5955112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955112).length < 2 ^ (prefixWord ++ tailWord_5955112).sum := by decide
  have hdescent : baseEnd_5955112 < baseStart_5955112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955135 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 1, 3, 2]
def baseStart_5955135 : Nat := 118140960795 + 5955135 * 2 ^ 59
def prefixEnd_5955135 : Nat := 4983230072969 + 3 ^ 40 * 5955135 * 2
def baseEnd_5955135 : Nat := 3057846617412663240625339

theorem tailTrace_5955135 : CollatzResearch.WordTrace tailWord_5955135 prefixEnd_5955135 3057846617412663240625339 := by
  unfold tailWord_5955135
  simp only [CollatzResearch.WordTrace]
  refine ⟨217201617280570425931138859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144801078187046950620759239 217201617280570425931138859)
  ·
    refine ⟨325802425920855638896708289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217201617280570425931138859 325802425920855638896708289)
    ·
      refine ⟨244351819440641729172531217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325802425920855638896708289 244351819440641729172531217)
      ·
        refine ⟨183263864580481296879398413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244351819440641729172531217 183263864580481296879398413)
        ·
          refine ⟨68723949217680486329774405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183263864580481296879398413 68723949217680486329774405)
          ·
            refine ⟨12885740478315091186832701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68723949217680486329774405 12885740478315091186832701)
            ·
              refine ⟨4832152679368159195062263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12885740478315091186832701 4832152679368159195062263)
              ·
                refine ⟨7248229019052238792593395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832152679368159195062263 7248229019052238792593395)
                ·
                  refine ⟨10872343528578358188890093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248229019052238792593395 10872343528578358188890093)
                  ·
                    refine ⟨4077128823216884320833785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10872343528578358188890093 4077128823216884320833785)
                    ·
                      refine ⟨3057846617412663240625339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4077128823216884320833785 3057846617412663240625339)
                      ·
                        rfl

theorem cell23_5955135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_5955135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955135 prefixEnd_5955135 := by exact prefixLift 5955135
  have htrace : WordTrace (prefixWord ++ tailWord_5955135) baseStart_5955135 baseEnd_5955135 := by
    simpa [prefixWord, tailWord_5955135, baseEnd_5955135] using wordTrace_append hprefix tailTrace_5955135
  have hstable : (prefixWord ++ tailWord_5955135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955135).length < 2 ^ (prefixWord ++ tailWord_5955135).sum := by decide
  have hdescent : baseEnd_5955135 < baseStart_5955135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955194 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_5955194 : Nat := 118140960795 + 5955194 * 2 ^ 59
def prefixEnd_5955194 : Nat := 4983230072969 + 3 ^ 40 * 5955194 * 2
def baseEnd_5955194 : Nat := 3057876912771278509787567

theorem tailTrace_5955194 : CollatzResearch.WordTrace tailWord_5955194 prefixEnd_5955194 3057876912771278509787567 := by
  unfold tailWord_5955194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54300942296839169751884159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144802512791571119338357757 54300942296839169751884159)
  ·
    refine ⟨81451413445258754627826239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54300942296839169751884159 81451413445258754627826239)
    ·
      refine ⟨122177120167888131941739359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81451413445258754627826239 122177120167888131941739359)
      ·
        refine ⟨183265680251832197912609039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122177120167888131941739359 183265680251832197912609039)
        ·
          refine ⟨274898520377748296868913559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183265680251832197912609039 274898520377748296868913559)
          ·
            refine ⟨412347780566622445303370339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274898520377748296868913559 412347780566622445303370339)
            ·
              refine ⟨618521670849933667955055509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412347780566622445303370339 618521670849933667955055509)
              ·
                refine ⟨28993203321090640685393227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 618521670849933667955055509 28993203321090640685393227)
                ·
                  refine ⟨43489804981635961028089841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28993203321090640685393227 43489804981635961028089841)
                  ·
                    refine ⟨32617353736226970771067381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43489804981635961028089841 32617353736226970771067381)
                    ·
                      refine ⟨3057876912771278509787567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32617353736226970771067381 3057876912771278509787567)
                      ·
                        rfl

theorem cell23_5955194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_5955194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955194 prefixEnd_5955194 := by exact prefixLift 5955194
  have htrace : WordTrace (prefixWord ++ tailWord_5955194) baseStart_5955194 baseEnd_5955194 := by
    simpa [prefixWord, tailWord_5955194, baseEnd_5955194] using wordTrace_append hprefix tailTrace_5955194
  have hstable : (prefixWord ++ tailWord_5955194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955194).length < 2 ^ (prefixWord ++ tailWord_5955194).sum := by decide
  have hdescent : baseEnd_5955194 < baseStart_5955194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955258 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_5955258 : Nat := 118140960795 + 5955258 * 2 ^ 59
def prefixEnd_5955258 : Nat := 4983230072969 + 3 ^ 40 * 5955258 * 2
def baseEnd_5955258 : Nat := 3057909775533166259387273

theorem tailTrace_5955258 : CollatzResearch.WordTrace tailWord_5955258 prefixEnd_5955258 3057909775533166259387273 := by
  unfold tailWord_5955258
  simp only [CollatzResearch.WordTrace]
  refine ⟨54301525864781204484466607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144804068972749878625244285 54301525864781204484466607)
  ·
    refine ⟨81452288797171806726699911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54301525864781204484466607 81452288797171806726699911)
    ·
      refine ⟨122178433195757710090049867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81452288797171806726699911 122178433195757710090049867)
      ·
        refine ⟨183267649793636565135074801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122178433195757710090049867 183267649793636565135074801)
        ·
          refine ⟨137450737345227423851306101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183267649793636565135074801 137450737345227423851306101)
          ·
            refine ⟨12886006626115070986059947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137450737345227423851306101 12886006626115070986059947)
            ·
              refine ⟨19329009939172606479089921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12886006626115070986059947 19329009939172606479089921)
              ·
                refine ⟨14496757454379454859317441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19329009939172606479089921 14496757454379454859317441)
                ·
                  refine ⟨10872568090784591144488081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14496757454379454859317441 10872568090784591144488081)
                  ·
                    refine ⟨8154426068088443358366061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10872568090784591144488081 8154426068088443358366061)
                    ·
                      refine ⟨3057909775533166259387273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154426068088443358366061 3057909775533166259387273)
                      ·
                        rfl

theorem cell23_5955258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_5955258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955258 prefixEnd_5955258 := by exact prefixLift 5955258
  have htrace : WordTrace (prefixWord ++ tailWord_5955258) baseStart_5955258 baseEnd_5955258 := by
    simpa [prefixWord, tailWord_5955258, baseEnd_5955258] using wordTrace_append hprefix tailTrace_5955258
  have hstable : (prefixWord ++ tailWord_5955258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955258).length < 2 ^ (prefixWord ++ tailWord_5955258).sum := by decide
  have hdescent : baseEnd_5955258 < baseStart_5955258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955261 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 6]
def baseStart_5955261 : Nat := 118140960795 + 5955261 * 2 ^ 59
def prefixEnd_5955261 : Nat := 4983230072969 + 3 ^ 40 * 5955261 * 2
def baseEnd_5955261 : Nat := 339767923997236638627751

theorem tailTrace_5955261 : CollatzResearch.WordTrace tailWord_5955261 prefixEnd_5955261 339767923997236638627751 := by
  unfold tailWord_5955261
  simp only [CollatzResearch.WordTrace]
  refine ⟨217206212878113949450225637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144804141918742632966817091 217206212878113949450225637)
  ·
    refine ⟨40726164914646365521917307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217206212878113949450225637 40726164914646365521917307)
    ·
      refine ⟨61089247371969548282875961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40726164914646365521917307 61089247371969548282875961)
      ·
        refine ⟨45816935528977161212156971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61089247371969548282875961 45816935528977161212156971)
        ·
          refine ⟨68725403293465741818235457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45816935528977161212156971 68725403293465741818235457)
          ·
            refine ⟨51544052470099306363676593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68725403293465741818235457 51544052470099306363676593)
            ·
              refine ⟨38658039352574479772757445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51544052470099306363676593 38658039352574479772757445)
              ·
                refine ⟨7248382378607714957392021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38658039352574479772757445 7248382378607714957392021)
                ·
                  refine ⟨339767923997236638627751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7248382378607714957392021 339767923997236638627751)
                  ·
                    rfl

theorem cell23_5955261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_5955261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955261 prefixEnd_5955261 := by exact prefixLift 5955261
  have htrace : WordTrace (prefixWord ++ tailWord_5955261) baseStart_5955261 baseEnd_5955261 := by
    simpa [prefixWord, tailWord_5955261, baseEnd_5955261] using wordTrace_append hprefix tailTrace_5955261
  have hstable : (prefixWord ++ tailWord_5955261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955261).length < 2 ^ (prefixWord ++ tailWord_5955261).sum := by decide
  have hdescent : baseEnd_5955261 < baseStart_5955261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955288 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_5955288 : Nat := 118140960795 + 5955288 * 2 ^ 59
def prefixEnd_5955288 : Nat := 4983230072969 + 3 ^ 40 * 5955288 * 2
def baseEnd_5955288 : Nat := 3057925179952801142012135

theorem tailTrace_5955288 : CollatzResearch.WordTrace tailWord_5955288 prefixEnd_5955288 3057925179952801142012135 := by
  unfold tailWord_5955288
  simp only [CollatzResearch.WordTrace]
  refine ⟨108603598824508066530729259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144804798432677422040972345 108603598824508066530729259)
  ·
    refine ⟨162905398236762099796093889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108603598824508066530729259 162905398236762099796093889)
    ·
      refine ⟨122179048677571574847070417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162905398236762099796093889 122179048677571574847070417)
      ·
        refine ⟨91634286508178681135302813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122179048677571574847070417 91634286508178681135302813)
        ·
          refine ⟨34362857440567005425738555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91634286508178681135302813 34362857440567005425738555)
          ·
            refine ⟨51544286160850508138607833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34362857440567005425738555 51544286160850508138607833)
            ·
              refine ⟨38658214620637881103955875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51544286160850508138607833 38658214620637881103955875)
              ·
                refine ⟨57987321930956821655933813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38658214620637881103955875 57987321930956821655933813)
                ·
                  refine ⟨5436311431027202030243795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57987321930956821655933813 5436311431027202030243795)
                  ·
                    refine ⟨8154467146540803045365693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5436311431027202030243795 8154467146540803045365693)
                    ·
                      refine ⟨3057925179952801142012135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154467146540803045365693 3057925179952801142012135)
                      ·
                        rfl

theorem cell23_5955288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_5955288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955288 prefixEnd_5955288 := by exact prefixLift 5955288
  have htrace : WordTrace (prefixWord ++ tailWord_5955288) baseStart_5955288 baseEnd_5955288 := by
    simpa [prefixWord, tailWord_5955288, baseEnd_5955288] using wordTrace_append hprefix tailTrace_5955288
  have hstable : (prefixWord ++ tailWord_5955288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955288).length < 2 ^ (prefixWord ++ tailWord_5955288).sum := by decide
  have hdescent : baseEnd_5955288 < baseStart_5955288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955292 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5955292 : Nat := 118140960795 + 5955292 * 2 ^ 59
def prefixEnd_5955292 : Nat := 4983230072969 + 3 ^ 40 * 5955292 * 2
def baseEnd_5955292 : Nat := 3057927233875419126362117

theorem tailTrace_5955292 : CollatzResearch.WordTrace tailWord_5955292 prefixEnd_5955292 3057927233875419126362117 := by
  unfold tailWord_5955292
  simp only [CollatzResearch.WordTrace]
  refine ⟨108603671770500820872302065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144804895694001094496402753 108603671770500820872302065)
  ·
    refine ⟨81452753827875615654226549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108603671770500820872302065 81452753827875615654226549)
    ·
      refine ⟨7636195671363338967583739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81452753827875615654226549 7636195671363338967583739)
      ·
        refine ⟨11454293507045008451375609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636195671363338967583739 11454293507045008451375609)
        ·
          refine ⟨8590720130283756338531707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11454293507045008451375609 8590720130283756338531707)
          ·
            refine ⟨12886080195425634507797561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8590720130283756338531707 12886080195425634507797561)
            ·
              refine ⟨9664560146569225880848171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12886080195425634507797561 9664560146569225880848171)
              ·
                refine ⟨14496840219853838821272257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664560146569225880848171 14496840219853838821272257)
                ·
                  refine ⟨10872630164890379115954193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14496840219853838821272257 10872630164890379115954193)
                  ·
                    refine ⟨8154472623667784336965645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10872630164890379115954193 8154472623667784336965645)
                    ·
                      refine ⟨3057927233875419126362117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154472623667784336965645 3057927233875419126362117)
                      ·
                        rfl

theorem cell23_5955292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5955292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955292 prefixEnd_5955292 := by exact prefixLift 5955292
  have htrace : WordTrace (prefixWord ++ tailWord_5955292) baseStart_5955292 baseEnd_5955292 := by
    simpa [prefixWord, tailWord_5955292, baseEnd_5955292] using wordTrace_append hprefix tailTrace_5955292
  have hstable : (prefixWord ++ tailWord_5955292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955292).length < 2 ^ (prefixWord ++ tailWord_5955292).sum := by decide
  have hdescent : baseEnd_5955292 < baseStart_5955292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955305 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 1, 1, 3]
def baseStart_5955305 : Nat := 118140960795 + 5955305 * 2 ^ 59
def prefixEnd_5955305 : Nat := 4983230072969 + 3 ^ 40 * 5955305 * 2
def baseEnd_5955305 : Nat := 3057933909123927575499557

theorem tailTrace_5955305 : CollatzResearch.WordTrace tailWord_5955305 prefixEnd_5955305 3057933909123927575499557 := by
  unfold tailWord_5955305
  simp only [CollatzResearch.WordTrace]
  refine ⟨217207817689954544964827369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144805211793303029976551579 217207817689954544964827369)
  ·
    refine ⟨162905863267465908723620527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217207817689954544964827369 162905863267465908723620527)
    ·
      refine ⟨244358794901198863085430791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162905863267465908723620527 244358794901198863085430791)
      ·
        refine ⟨366538192351798294628146187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244358794901198863085430791 366538192351798294628146187)
        ·
          refine ⟨549807288527697441942219281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366538192351798294628146187 549807288527697441942219281)
          ·
            refine ⟨412355466395773081456664461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549807288527697441942219281 412355466395773081456664461)
            ·
              refine ⟨154633299898414905546249173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412355466395773081456664461 154633299898414905546249173)
              ·
                refine ⟨3624217966369099348740215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154633299898414905546249173 3624217966369099348740215)
                ·
                  refine ⟨5436326949553649023110323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624217966369099348740215 5436326949553649023110323)
                  ·
                    refine ⟨8154490424330473534665485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5436326949553649023110323 8154490424330473534665485)
                    ·
                      refine ⟨3057933909123927575499557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154490424330473534665485 3057933909123927575499557)
                      ·
                        rfl

theorem cell23_5955305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 1, 3].length) (baseStart_5955305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955305 prefixEnd_5955305 := by exact prefixLift 5955305
  have htrace : WordTrace (prefixWord ++ tailWord_5955305) baseStart_5955305 baseEnd_5955305 := by
    simpa [prefixWord, tailWord_5955305, baseEnd_5955305] using wordTrace_append hprefix tailTrace_5955305
  have hstable : (prefixWord ++ tailWord_5955305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955305).length < 2 ^ (prefixWord ++ tailWord_5955305).sum := by decide
  have hdescent : baseEnd_5955305 < baseStart_5955305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955316 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5955316 : Nat := 118140960795 + 5955316 * 2 ^ 59
def prefixEnd_5955316 : Nat := 4983230072969 + 3 ^ 40 * 5955316 * 2
def baseEnd_5955316 : Nat := 1019313185803709010820669

theorem tailTrace_5955316 : CollatzResearch.WordTrace tailWord_5955316 prefixEnd_5955316 1019313185803709010820669 := by
  unfold tailWord_5955316
  simp only [CollatzResearch.WordTrace]
  refine ⟨108604109446457346921738901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144805479261943129228985201 108604109446457346921738901)
  ·
    refine ⟨5090817630302688136956511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108604109446457346921738901 5090817630302688136956511)
    ·
      refine ⟨7636226445454032205434767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5090817630302688136956511 7636226445454032205434767)
      ·
        refine ⟨11454339668181048308152151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636226445454032205434767 11454339668181048308152151)
        ·
          refine ⟨17181509502271572462228227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11454339668181048308152151 17181509502271572462228227)
          ·
            refine ⟨25772264253407358693342341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17181509502271572462228227 25772264253407358693342341)
            ·
              refine ⟨4832299547513879755001689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25772264253407358693342341 4832299547513879755001689)
              ·
                refine ⟨3624224660635409816251267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832299547513879755001689 3624224660635409816251267)
                ·
                  refine ⟨5436336990953114724376901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624224660635409816251267 5436336990953114724376901)
                  ·
                    refine ⟨1019313185803709010820669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436336990953114724376901 1019313185803709010820669)
                    ·
                      rfl

theorem cell23_5955316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5955316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955316 prefixEnd_5955316 := by exact prefixLift 5955316
  have htrace : WordTrace (prefixWord ++ tailWord_5955316) baseStart_5955316 baseEnd_5955316 := by
    simpa [prefixWord, tailWord_5955316, baseEnd_5955316] using wordTrace_append hprefix tailTrace_5955316
  have hstable : (prefixWord ++ tailWord_5955316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955316).length < 2 ^ (prefixWord ++ tailWord_5955316).sum := by decide
  have hdescent : baseEnd_5955316 < baseStart_5955316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955331 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5]
def baseStart_5955331 : Nat := 118140960795 + 5955331 * 2 ^ 59
def prefixEnd_5955331 : Nat := 4983230072969 + 3 ^ 40 * 5955331 * 2
def baseEnd_5955331 : Nat := 3057947259620944473774437

theorem tailTrace_5955331 : CollatzResearch.WordTrace tailWord_5955331 prefixEnd_5955331 3057947259620944473774437 := by
  unfold tailWord_5955331
  simp only [CollatzResearch.WordTrace]
  refine ⟨217208765987860351405273847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144805843991906900936849231 217208765987860351405273847)
  ·
    refine ⟨325813148981790527107910771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217208765987860351405273847 325813148981790527107910771)
    ·
      refine ⟨488719723472685790661866157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325813148981790527107910771 488719723472685790661866157)
      ·
        refine ⟨183269896302257171498199809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488719723472685790661866157 183269896302257171498199809)
        ·
          refine ⟨137452422226692878623649857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183269896302257171498199809 137452422226692878623649857)
          ·
            refine ⟨103089316670019658967737393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137452422226692878623649857 103089316670019658967737393)
            ·
              refine ⟨77316987502514744225803045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103089316670019658967737393 77316987502514744225803045)
              ·
                refine ⟨14496935156721514542338071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77316987502514744225803045 14496935156721514542338071)
                ·
                  refine ⟨21745402735082271813507107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14496935156721514542338071 21745402735082271813507107)
                  ·
                    refine ⟨32618104102623407720260661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21745402735082271813507107 32618104102623407720260661)
                    ·
                      refine ⟨3057947259620944473774437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32618104102623407720260661 3057947259620944473774437)
                      ·
                        rfl

theorem cell23_5955331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_5955331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955331 prefixEnd_5955331 := by exact prefixLift 5955331
  have htrace : WordTrace (prefixWord ++ tailWord_5955331) baseStart_5955331 baseEnd_5955331 := by
    simpa [prefixWord, tailWord_5955331, baseEnd_5955331] using wordTrace_append hprefix tailTrace_5955331
  have hstable : (prefixWord ++ tailWord_5955331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955331).length < 2 ^ (prefixWord ++ tailWord_5955331).sum := by decide
  have hdescent : baseEnd_5955331 < baseStart_5955331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955338 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_5955338 : Nat := 118140960795 + 5955338 * 2 ^ 59
def prefixEnd_5955338 : Nat := 4983230072969 + 3 ^ 40 * 5955338 * 2
def baseEnd_5955338 : Nat := 1019316951328508648795635

theorem tailTrace_5955338 : CollatzResearch.WordTrace tailWord_5955338 prefixEnd_5955338 1019316951328508648795635 := by
  unfold tailWord_5955338
  simp only [CollatzResearch.WordTrace]
  refine ⟨54302255324708747900194667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144806014199223327733852445 54302255324708747900194667)
  ·
    refine ⟨81453382987063121850292001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54302255324708747900194667 81453382987063121850292001)
    ·
      refine ⟨61090037240297341387719001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81453382987063121850292001 61090037240297341387719001)
      ·
        refine ⟨45817527930223006040789251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61090037240297341387719001 45817527930223006040789251)
        ·
          refine ⟨68726291895334509061183877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45817527930223006040789251 68726291895334509061183877)
          ·
            refine ⟨12886179730375220448971977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68726291895334509061183877 12886179730375220448971977)
            ·
              refine ⟨9664634797781415336728983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12886179730375220448971977 9664634797781415336728983)
              ·
                refine ⟨14496952196672123005093475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664634797781415336728983 14496952196672123005093475)
                ·
                  refine ⟨21745428295008184507640213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14496952196672123005093475 21745428295008184507640213)
                  ·
                    refine ⟨1019316951328508648795635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21745428295008184507640213 1019316951328508648795635)
                    ·
                      rfl

theorem cell23_5955338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_5955338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955338 prefixEnd_5955338 := by exact prefixLift 5955338
  have htrace : WordTrace (prefixWord ++ tailWord_5955338) baseStart_5955338 baseEnd_5955338 := by
    simpa [prefixWord, tailWord_5955338, baseEnd_5955338] using wordTrace_append hprefix tailTrace_5955338
  have hstable : (prefixWord ++ tailWord_5955338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955338).length < 2 ^ (prefixWord ++ tailWord_5955338).sum := by decide
  have hdescent : baseEnd_5955338 < baseStart_5955338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955365 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_5955365 : Nat := 118140960795 + 5955365 * 2 ^ 59
def prefixEnd_5955365 : Nat := 4983230072969 + 3 ^ 40 * 5955365 * 2
def baseEnd_5955365 : Nat := 3057964717963197340749281

theorem tailTrace_5955365 : CollatzResearch.WordTrace tailWord_5955365 prefixEnd_5955365 3057964717963197340749281 := by
  unfold tailWord_5955365
  simp only [CollatzResearch.WordTrace]
  refine ⟨217210006069737175212011549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144806670713158116808007699 217210006069737175212011549)
  ·
    refine ⟨81453752276151440704504331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217210006069737175212011549 81453752276151440704504331)
    ·
      refine ⟨122180628414227161056756497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81453752276151440704504331 122180628414227161056756497)
      ·
        refine ⟨91635471310670370792567373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122180628414227161056756497 91635471310670370792567373)
        ·
          refine ⟨34363301741501389047212765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91635471310670370792567373 34363301741501389047212765)
          ·
            refine ⟨12886238153063020892704787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34363301741501389047212765 12886238153063020892704787)
            ·
              refine ⟨19329357229594531339057181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12886238153063020892704787 19329357229594531339057181)
              ·
                refine ⟨7248508961097949252146443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19329357229594531339057181 7248508961097949252146443)
                ·
                  refine ⟨10872763441646923878219665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248508961097949252146443 10872763441646923878219665)
                  ·
                    refine ⟨8154572581235192908664749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10872763441646923878219665 8154572581235192908664749)
                    ·
                      refine ⟨3057964717963197340749281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154572581235192908664749 3057964717963197340749281)
                      ·
                        rfl

theorem cell23_5955365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_5955365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955365 prefixEnd_5955365 := by exact prefixLift 5955365
  have htrace : WordTrace (prefixWord ++ tailWord_5955365) baseStart_5955365 baseEnd_5955365 := by
    simpa [prefixWord, tailWord_5955365, baseEnd_5955365] using wordTrace_append hprefix tailTrace_5955365
  have hstable : (prefixWord ++ tailWord_5955365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955365).length < 2 ^ (prefixWord ++ tailWord_5955365).sum := by decide
  have hdescent : baseEnd_5955365 < baseStart_5955365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955395 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 3]
def baseStart_5955395 : Nat := 118140960795 + 5955395 * 2 ^ 59
def prefixEnd_5955395 : Nat := 4983230072969 + 3 ^ 40 * 5955395 * 2
def baseEnd_5955395 : Nat := 3057980122382832223374143

theorem tailTrace_5955395 : CollatzResearch.WordTrace tailWord_5955395 prefixEnd_5955395 3057980122382832223374143 := by
  unfold tailWord_5955395
  simp only [CollatzResearch.WordTrace]
  refine ⟨217211100259628490335603639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144807400173085660223735759 217211100259628490335603639)
  ·
    refine ⟨325816650389442735503405459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217211100259628490335603639 325816650389442735503405459)
    ·
      refine ⟨488724975584164103255108189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325816650389442735503405459 488724975584164103255108189)
      ·
        refine ⟨183271865844061538720665571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488724975584164103255108189 183271865844061538720665571)
        ·
          refine ⟨274907798766092308080998357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183271865844061538720665571 274907798766092308080998357)
          ·
            refine ⟨6443151533580288470648399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 274907798766092308080998357 6443151533580288470648399)
            ·
              refine ⟨9664727300370432705972599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443151533580288470648399 9664727300370432705972599)
              ·
                refine ⟨14497090950555649058958899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664727300370432705972599 14497090950555649058958899)
                ·
                  refine ⟨21745636425833473588438349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14497090950555649058958899 21745636425833473588438349)
                  ·
                    refine ⟨8154613659687552595664381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21745636425833473588438349 8154613659687552595664381)
                    ·
                      refine ⟨3057980122382832223374143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154613659687552595664381 3057980122382832223374143)
                      ·
                        rfl

theorem cell23_5955395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_5955395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955395 prefixEnd_5955395 := by exact prefixLift 5955395
  have htrace : WordTrace (prefixWord ++ tailWord_5955395) baseStart_5955395 baseEnd_5955395 := by
    simpa [prefixWord, tailWord_5955395, baseEnd_5955395] using wordTrace_append hprefix tailTrace_5955395
  have hstable : (prefixWord ++ tailWord_5955395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955395).length < 2 ^ (prefixWord ++ tailWord_5955395).sum := by decide
  have hdescent : baseEnd_5955395 < baseStart_5955395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955468 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_5955468 : Nat := 118140960795 + 5955468 * 2 ^ 59
def prefixEnd_5955468 : Nat := 4983230072969 + 3 ^ 40 * 5955468 * 2
def baseEnd_5955468 : Nat := 3058017606470610437761307

theorem tailTrace_5955468 : CollatzResearch.WordTrace tailWord_5955468 prefixEnd_5955468 3058017606470610437761307 := by
  unfold tailWord_5955468
  simp only [CollatzResearch.WordTrace]
  refine ⟨108606881394182011901505529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144809175192242682535340705 108606881394182011901505529)
  ·
    refine ⟨81455161045636508926129147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108606881394182011901505529 81455161045636508926129147)
    ·
      refine ⟨122182741568454763389193721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81455161045636508926129147 122182741568454763389193721)
      ·
        refine ⟨91637056176341072541895291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122182741568454763389193721 91637056176341072541895291)
        ·
          refine ⟨137455584264511608812842937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91637056176341072541895291 137455584264511608812842937)
          ·
            refine ⟨103091688198383706609632203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137455584264511608812842937 103091688198383706609632203)
            ·
              refine ⟨154637532297575559914448305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103091688198383706609632203 154637532297575559914448305)
              ·
                refine ⟨115978149223181669935836229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154637532297575559914448305 115978149223181669935836229)
                ·
                  refine ⟨21745902979346563112969293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115978149223181669935836229 21745902979346563112969293)
                  ·
                    refine ⟨8154713617254961167363485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21745902979346563112969293 8154713617254961167363485)
                    ·
                      refine ⟨3058017606470610437761307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154713617254961167363485 3058017606470610437761307)
                      ·
                        rfl

theorem cell23_5955468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_5955468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955468 prefixEnd_5955468 := by exact prefixLift 5955468
  have htrace : WordTrace (prefixWord ++ tailWord_5955468) baseStart_5955468 baseEnd_5955468 := by
    simpa [prefixWord, tailWord_5955468, baseEnd_5955468] using wordTrace_append hprefix tailTrace_5955468
  have hstable : (prefixWord ++ tailWord_5955468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955468).length < 2 ^ (prefixWord ++ tailWord_5955468).sum := by decide
  have hdescent : baseEnd_5955468 < baseStart_5955468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955471 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 7, 7]
def baseStart_5955471 : Nat := 118140960795 + 5955471 * 2 ^ 59
def prefixEnd_5955471 : Nat := 4983230072969 + 3 ^ 40 * 5955471 * 2
def baseEnd_5955471 : Nat := 1019339715637524642007931

theorem tailTrace_5955471 : CollatzResearch.WordTrace tailWord_5955471 prefixEnd_5955471 1019339715637524642007931 := by
  unfold tailWord_5955471
  simp only [CollatzResearch.WordTrace]
  refine ⟨217213872207353155315370267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144809248138235436876913511 217213872207353155315370267)
  ·
    refine ⟨325820808311029732973055401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217213872207353155315370267 325820808311029732973055401)
    ·
      refine ⟨244365606233272299729791551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325820808311029732973055401 244365606233272299729791551)
      ·
        refine ⟨366548409349908449594687327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244365606233272299729791551 366548409349908449594687327)
        ·
          refine ⟨549822614024862674392030991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366548409349908449594687327 549822614024862674392030991)
          ·
            refine ⟨824733921037294011588046487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549822614024862674392030991 824733921037294011588046487)
            ·
              refine ⟨1237100881555941017382069731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824733921037294011588046487 1237100881555941017382069731)
              ·
                refine ⟨1855651322333911526073104597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237100881555941017382069731 1855651322333911526073104597)
                ·
                  refine ⟨43491827867201051392338389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1855651322333911526073104597 43491827867201051392338389)
                  ·
                    refine ⟨1019339715637524642007931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43491827867201051392338389 1019339715637524642007931)
                    ·
                      rfl

theorem cell23_5955471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_5955471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955471 prefixEnd_5955471 := by exact prefixLift 5955471
  have htrace : WordTrace (prefixWord ++ tailWord_5955471) baseStart_5955471 baseEnd_5955471 := by
    simpa [prefixWord, tailWord_5955471, baseEnd_5955471] using wordTrace_append hprefix tailTrace_5955471
  have hstable : (prefixWord ++ tailWord_5955471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955471).length < 2 ^ (prefixWord ++ tailWord_5955471).sum := by decide
  have hdescent : baseEnd_5955471 < baseStart_5955471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955492 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 5]
def baseStart_5955492 : Nat := 118140960795 + 5955492 * 2 ^ 59
def prefixEnd_5955492 : Nat := 4983230072969 + 3 ^ 40 * 5955492 * 2
def baseEnd_5955492 : Nat := 339781103334035371540133

theorem tailTrace_5955492 : CollatzResearch.WordTrace tailWord_5955492 prefixEnd_5955492 339781103334035371540133 := by
  unfold tailWord_5955492
  simp only [CollatzResearch.WordTrace]
  refine ⟨108607319070138537950942365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144809758760184717267923153 108607319070138537950942365)
  ·
    refine ⟨40727744651301951731603387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108607319070138537950942365 40727744651301951731603387)
    ·
      refine ⟨61091616976952927597405081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40727744651301951731603387 61091616976952927597405081)
      ·
        refine ⟨45818712732714695698053811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61091616976952927597405081 45818712732714695698053811)
        ·
          refine ⟨68728069099072043547080717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45818712732714695698053811 68728069099072043547080717)
          ·
            refine ⟨25773025912152016330155269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68728069099072043547080717 25773025912152016330155269)
            ·
              refine ⟨4832442358528503061904113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25773025912152016330155269 4832442358528503061904113)
              ·
                refine ⟨3624331768896377296428085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832442358528503061904113 3624331768896377296428085)
                ·
                  refine ⟨339781103334035371540133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3624331768896377296428085 339781103334035371540133)
                  ·
                    rfl

theorem cell23_5955492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_5955492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955492 prefixEnd_5955492 := by exact prefixLift 5955492
  have htrace : WordTrace (prefixWord ++ tailWord_5955492) baseStart_5955492 baseEnd_5955492 := by
    simpa [prefixWord, tailWord_5955492, baseEnd_5955492] using wordTrace_append hprefix tailTrace_5955492
  have hstable : (prefixWord ++ tailWord_5955492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955492).length < 2 ^ (prefixWord ++ tailWord_5955492).sum := by decide
  have hdescent : baseEnd_5955492 < baseStart_5955492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955595 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 1, 5]
def baseStart_5955595 : Nat := 118140960795 + 5955595 * 2 ^ 59
def prefixEnd_5955595 : Nat := 4983230072969 + 3 ^ 40 * 5955595 * 2
def baseEnd_5955595 : Nat := 1019360939504577146957741

theorem tailTrace_5955595 : CollatzResearch.WordTrace tailWord_5955595 prefixEnd_5955595 1019360939504577146957741 := by
  unfold tailWord_5955595
  simp only [CollatzResearch.WordTrace]
  refine ⟨217218394858903924492884239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144812263239269282995256159 217218394858903924492884239)
  ·
    refine ⟨325827592288355886739326359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217218394858903924492884239 325827592288355886739326359)
    ·
      refine ⟨488741388432533830108989539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325827592288355886739326359 488741388432533830108989539)
      ·
        refine ⟨733112082648800745163484309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488741388432533830108989539 733112082648800745163484309)
        ·
          refine ⟨34364628874162534929538327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 733112082648800745163484309 34364628874162534929538327)
          ·
            refine ⟨51546943311243802394307491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34364628874162534929538327 51546943311243802394307491)
            ·
              refine ⟨77320414966865703591461237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51546943311243802394307491 77320414966865703591461237)
              ·
                refine ⟨7248788903143659711699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77320414966865703591461237 7248788903143659711699491)
                ·
                  refine ⟨10873183354715489567549237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248788903143659711699491 10873183354715489567549237)
                  ·
                    refine ⟨1019360939504577146957741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10873183354715489567549237 1019360939504577146957741)
                    ·
                      rfl

theorem cell23_5955595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 5].length) (baseStart_5955595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955595 prefixEnd_5955595 := by exact prefixLift 5955595
  have htrace : WordTrace (prefixWord ++ tailWord_5955595) baseStart_5955595 baseEnd_5955595 := by
    simpa [prefixWord, tailWord_5955595, baseEnd_5955595] using wordTrace_append hprefix tailTrace_5955595
  have hstable : (prefixWord ++ tailWord_5955595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955595).length < 2 ^ (prefixWord ++ tailWord_5955595).sum := by decide
  have hdescent : baseEnd_5955595 < baseStart_5955595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955615 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_5955615 : Nat := 118140960795 + 5955615 * 2 ^ 59
def prefixEnd_5955615 : Nat := 4983230072969 + 3 ^ 40 * 5955615 * 2
def baseEnd_5955615 : Nat := 3058093088126821362623131

theorem tailTrace_5955615 : CollatzResearch.WordTrace tailWord_5955615 prefixEnd_5955615 3058093088126821362623131 := by
  unfold tailWord_5955615
  simp only [CollatzResearch.WordTrace]
  refine ⟨217219124318831467908612299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144812749545887645272408199 217219124318831467908612299)
  ·
    refine ⟨325828686478247201862918449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217219124318831467908612299 325828686478247201862918449)
    ·
      refine ⟨244371514858685401397188837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325828686478247201862918449 244371514858685401397188837)
      ·
        refine ⟨45819659036003512761972907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244371514858685401397188837 45819659036003512761972907)
        ·
          refine ⟨68729488554005269142959361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45819659036003512761972907 68729488554005269142959361)
          ·
            refine ⟨51547116415503951857219521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68729488554005269142959361 51547116415503951857219521)
            ·
              refine ⟨38660337311627963892914641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51547116415503951857219521 38660337311627963892914641)
              ·
                refine ⟨28995252983720972919685981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38660337311627963892914641 28995252983720972919685981)
                ·
                  refine ⟨10873219868895364844882243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28995252983720972919685981 10873219868895364844882243)
                  ·
                    refine ⟨16309829803343047267323365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10873219868895364844882243 16309829803343047267323365)
                    ·
                      refine ⟨3058093088126821362623131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16309829803343047267323365 3058093088126821362623131)
                      ·
                        rfl

theorem cell23_5955615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_5955615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955615 prefixEnd_5955615 := by exact prefixLift 5955615
  have htrace : WordTrace (prefixWord ++ tailWord_5955615) baseStart_5955615 baseEnd_5955615 := by
    simpa [prefixWord, tailWord_5955615, baseEnd_5955615] using wordTrace_append hprefix tailTrace_5955615
  have hstable : (prefixWord ++ tailWord_5955615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955615).length < 2 ^ (prefixWord ++ tailWord_5955615).sum := by decide
  have hdescent : baseEnd_5955615 < baseStart_5955615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955632 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4]
def baseStart_5955632 : Nat := 118140960795 + 5955632 * 2 ^ 59
def prefixEnd_5955632 : Nat := 4983230072969 + 3 ^ 40 * 5955632 * 2
def baseEnd_5955632 : Nat := 3058101817297947796110553

theorem tailTrace_5955632 : CollatzResearch.WordTrace tailWord_5955632 prefixEnd_5955632 3058101817297947796110553 := by
  unfold tailWord_5955632
  simp only [CollatzResearch.WordTrace]
  refine ⟨108609872179884939905990575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144813162906513253207987433 108609872179884939905990575)
  ·
    refine ⟨162914808269827409858985863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108609872179884939905990575 162914808269827409858985863)
    ·
      refine ⟨244372212404741114788478795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162914808269827409858985863 244372212404741114788478795)
      ·
        refine ⟨366558318607111672182718193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244372212404741114788478795 366558318607111672182718193)
        ·
          refine ⟨274918738955333754137038645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366558318607111672182718193 274918738955333754137038645)
          ·
            refine ⟨25773631777062539450347373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274918738955333754137038645 25773631777062539450347373)
            ·
              refine ⟨9665111916398452293880265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25773631777062539450347373 9665111916398452293880265)
              ·
                refine ⟨7248833937298839220410199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9665111916398452293880265 7248833937298839220410199)
                ·
                  refine ⟨10873250905948258830615299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248833937298839220410199 10873250905948258830615299)
                  ·
                    refine ⟨16309876358922388245922949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10873250905948258830615299 16309876358922388245922949)
                    ·
                      refine ⟨3058101817297947796110553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16309876358922388245922949 3058101817297947796110553)
                      ·
                        rfl

theorem cell23_5955632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_5955632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955632 prefixEnd_5955632 := by exact prefixLift 5955632
  have htrace : WordTrace (prefixWord ++ tailWord_5955632) baseStart_5955632 baseEnd_5955632 := by
    simpa [prefixWord, tailWord_5955632, baseEnd_5955632] using wordTrace_append hprefix tailTrace_5955632
  have hstable : (prefixWord ++ tailWord_5955632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955632).length < 2 ^ (prefixWord ++ tailWord_5955632).sum := by decide
  have hdescent : baseEnd_5955632 < baseStart_5955632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955646 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_5955646 : Nat := 118140960795 + 5955646 * 2 ^ 59
def prefixEnd_5955646 : Nat := 4983230072969 + 3 ^ 40 * 5955646 * 2
def baseEnd_5955646 : Nat := 1019369668675703580445163

theorem tailTrace_5955646 : CollatzResearch.WordTrace tailWord_5955646 prefixEnd_5955646 1019369668675703580445163 := by
  unfold tailWord_5955646
  simp only [CollatzResearch.WordTrace]
  refine ⟨27152531872714895025373849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144813503321146106801993861 27152531872714895025373849)
  ·
    refine ⟨20364398904536171269030387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27152531872714895025373849 20364398904536171269030387)
    ·
      refine ⟨30546598356804256903545581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20364398904536171269030387 30546598356804256903545581)
      ·
        refine ⟨11454974383801596338829593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30546598356804256903545581 11454974383801596338829593)
        ·
          refine ⟨8591230787851197254122195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11454974383801596338829593 8591230787851197254122195)
          ·
            refine ⟨12886846181776795881183293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591230787851197254122195 12886846181776795881183293)
            ·
              refine ⟨4832567318166298455443735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12886846181776795881183293 4832567318166298455443735)
              ·
                refine ⟨7248850977249447683165603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832567318166298455443735 7248850977249447683165603)
                ·
                  refine ⟨10873276465874171524748405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7248850977249447683165603 10873276465874171524748405)
                  ·
                    refine ⟨1019369668675703580445163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10873276465874171524748405 1019369668675703580445163)
                    ·
                      rfl

theorem cell23_5955646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_5955646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955646 prefixEnd_5955646 := by exact prefixLift 5955646
  have htrace : WordTrace (prefixWord ++ tailWord_5955646) baseStart_5955646 baseEnd_5955646 := by
    simpa [prefixWord, tailWord_5955646, baseEnd_5955646] using wordTrace_append hprefix tailTrace_5955646
  have hstable : (prefixWord ++ tailWord_5955646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955646).length < 2 ^ (prefixWord ++ tailWord_5955646).sum := by decide
  have hdescent : baseEnd_5955646 < baseStart_5955646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955665 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_5955665 : Nat := 118140960795 + 5955665 * 2 ^ 59
def prefixEnd_5955665 : Nat := 4983230072969 + 3 ^ 40 * 5955665 * 2
def baseEnd_5955665 : Nat := 3058118762159546166997901

theorem tailTrace_5955665 : CollatzResearch.WordTrace tailWord_5955665 prefixEnd_5955665 3058118762159546166997901 := by
  unfold tailWord_5955665
  simp only [CollatzResearch.WordTrace]
  refine ⟨217220947968650326447932449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144813965312433550965288299 217220947968650326447932449)
  ·
    refine ⟨162915710976487744835949337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217220947968650326447932449 162915710976487744835949337)
    ·
      refine ⟨122186783232365808626962003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162915710976487744835949337 122186783232365808626962003)
      ·
        refine ⟨183280174848548712940443005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122186783232365808626962003 183280174848548712940443005)
        ·
          refine ⟨68730065568205767352666127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183280174848548712940443005 68730065568205767352666127)
          ·
            refine ⟨103095098352308651028999191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68730065568205767352666127 103095098352308651028999191)
            ·
              refine ⟨154642647528462976543498787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103095098352308651028999191 154642647528462976543498787)
              ·
                refine ⟨231963971292694464815248181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154642647528462976543498787 231963971292694464815248181)
                ·
                  refine ⟨21746622308690106076429517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231963971292694464815248181 21746622308690106076429517)
                  ·
                    refine ⟨8154983365758789778661069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21746622308690106076429517 8154983365758789778661069)
                    ·
                      refine ⟨3058118762159546166997901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8154983365758789778661069 3058118762159546166997901)
                      ·
                        rfl

theorem cell23_5955665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_5955665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955665 prefixEnd_5955665 := by exact prefixLift 5955665
  have htrace : WordTrace (prefixWord ++ tailWord_5955665) baseStart_5955665 baseEnd_5955665 := by
    simpa [prefixWord, tailWord_5955665, baseEnd_5955665] using wordTrace_append hprefix tailTrace_5955665
  have hstable : (prefixWord ++ tailWord_5955665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955665).length < 2 ^ (prefixWord ++ tailWord_5955665).sum := by decide
  have hdescent : baseEnd_5955665 < baseStart_5955665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955715 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 2, 6]
def baseStart_5955715 : Nat := 118140960795 + 5955715 * 2 ^ 59
def prefixEnd_5955715 : Nat := 4983230072969 + 3 ^ 40 * 5955715 * 2
def baseEnd_5955715 : Nat := 1019381478730756990457557

theorem tailTrace_5955715 : CollatzResearch.WordTrace tailWord_5955715 prefixEnd_5955715 1019381478730756990457557 := by
  unfold tailWord_5955715
  simp only [CollatzResearch.WordTrace]
  refine ⟨217222771618469184987252599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144815181078979456658168399 217222771618469184987252599)
  ·
    refine ⟨325834157427703777480878899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217222771618469184987252599 325834157427703777480878899)
    ·
      refine ⟨488751236141555666221318349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325834157427703777480878899 488751236141555666221318349)
      ·
        refine ⟨183281713553083374832994381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488751236141555666221318349 183281713553083374832994381)
        ·
          refine ⟨68730642582406265562372893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183281713553083374832994381 68730642582406265562372893)
          ·
            refine ⟨25773990968402349585889835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68730642582406265562372893 25773990968402349585889835)
            ·
              refine ⟨38660986452603524378834753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25773990968402349585889835 38660986452603524378834753)
              ·
                refine ⟨28995739839452643284126065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38660986452603524378834753 28995739839452643284126065)
                ·
                  refine ⟨21746804879589482463094549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28995739839452643284126065 21746804879589482463094549)
                  ·
                    refine ⟨1019381478730756990457557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21746804879589482463094549 1019381478730756990457557)
                    ·
                      rfl

theorem cell23_5955715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 6].length) (baseStart_5955715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955715 prefixEnd_5955715 := by exact prefixLift 5955715
  have htrace : WordTrace (prefixWord ++ tailWord_5955715) baseStart_5955715 baseEnd_5955715 := by
    simpa [prefixWord, tailWord_5955715, baseEnd_5955715] using wordTrace_append hprefix tailTrace_5955715
  have hstable : (prefixWord ++ tailWord_5955715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955715).length < 2 ^ (prefixWord ++ tailWord_5955715).sum := by decide
  have hdescent : baseEnd_5955715 < baseStart_5955715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955790 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_5955790 : Nat := 118140960795 + 5955790 * 2 ^ 59
def prefixEnd_5955790 : Nat := 4983230072969 + 3 ^ 40 * 5955790 * 2
def baseEnd_5955790 : Nat := 3058182947241358177934827

theorem tailTrace_5955790 : CollatzResearch.WordTrace tailWord_5955790 prefixEnd_5955790 3058182947241358177934827 := by
  unfold tailWord_5955790
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153188386649684099529103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144817004728798315197488549 27153188386649684099529103)
  ·
    refine ⟨40729782579974526149293655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27153188386649684099529103 40729782579974526149293655)
    ·
      refine ⟨61094673869961789223940483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40729782579974526149293655 61094673869961789223940483)
      ·
        refine ⟨91642010804942683835910725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61094673869961789223940483 91642010804942683835910725)
        ·
          refine ⟨17182877025926753219233261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91642010804942683835910725 17182877025926753219233261)
          ·
            refine ⟨6443578884722532457212473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17182877025926753219233261 6443578884722532457212473)
            ·
              refine ⟨4832684163541899342909355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443578884722532457212473 4832684163541899342909355)
              ·
                refine ⟨7249026245312849014364033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832684163541899342909355 7249026245312849014364033)
                ·
                  refine ⟨5436769683984636760773025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7249026245312849014364033 5436769683984636760773025)
                  ·
                    refine ⟨4077577262988477570579769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5436769683984636760773025 4077577262988477570579769)
                    ·
                      refine ⟨3058182947241358177934827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4077577262988477570579769 3058182947241358177934827)
                      ·
                        rfl

theorem cell23_5955790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_5955790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955790 prefixEnd_5955790 := by exact prefixLift 5955790
  have htrace : WordTrace (prefixWord ++ tailWord_5955790) baseStart_5955790 baseEnd_5955790 := by
    simpa [prefixWord, tailWord_5955790, baseEnd_5955790] using wordTrace_append hprefix tailTrace_5955790
  have hstable : (prefixWord ++ tailWord_5955790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955790).length < 2 ^ (prefixWord ++ tailWord_5955790).sum := by decide
  have hdescent : baseEnd_5955790 < baseStart_5955790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955852 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 6]
def baseStart_5955852 : Nat := 118140960795 + 5955852 * 2 ^ 59
def prefixEnd_5955852 : Nat := 4983230072969 + 3 ^ 40 * 5955852 * 2
def baseEnd_5955852 : Nat := 339801642560215215039949

theorem tailTrace_5955852 : CollatzResearch.WordTrace tailWord_5955852 prefixEnd_5955852 339801642560215215039949 := by
  unfold tailWord_5955852
  simp only [CollatzResearch.WordTrace]
  refine ⟨108613884209486428692494905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144818512279315238256659873 108613884209486428692494905)
  ·
    refine ⟨81460413157114821519371179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108613884209486428692494905 81460413157114821519371179)
    ·
      refine ⟨122190619735672232279056769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81460413157114821519371179 122190619735672232279056769)
      ·
        refine ⟨91642964801754174209292577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122190619735672232279056769 91642964801754174209292577)
        ·
          refine ⟨68732223601315630656969433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91642964801754174209292577 68732223601315630656969433)
          ·
            refine ⟨51549167700986722992727075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68732223601315630656969433 51549167700986722992727075)
            ·
              refine ⟨77323751551480084489090613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51549167700986722992727075 77323751551480084489090613)
              ·
                refine ⟨7249101707951257920852245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77323751551480084489090613 7249101707951257920852245)
                ·
                  refine ⟨339801642560215215039949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7249101707951257920852245 339801642560215215039949)
                  ·
                    rfl

theorem cell23_5955852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_5955852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955852 prefixEnd_5955852 := by exact prefixLift 5955852
  have htrace : WordTrace (prefixWord ++ tailWord_5955852) baseStart_5955852 baseEnd_5955852 := by
    simpa [prefixWord, tailWord_5955852, baseEnd_5955852] using wordTrace_append hprefix tailTrace_5955852
  have hstable : (prefixWord ++ tailWord_5955852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955852).length < 2 ^ (prefixWord ++ tailWord_5955852).sum := by decide
  have hdescent : baseEnd_5955852 < baseStart_5955852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955886 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_5955886 : Nat := 118140960795 + 5955886 * 2 ^ 59
def prefixEnd_5955886 : Nat := 4983230072969 + 3 ^ 40 * 5955886 * 2
def baseEnd_5955886 : Nat := 339803582376021089148265

theorem tailTrace_5955886 : CollatzResearch.WordTrace tailWord_5955886 prefixEnd_5955886 339803582376021089148265 := by
  unfold tailWord_5955886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153626062606210148965939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144819339000566454127818341 27153626062606210148965939)
  ·
    refine ⟨40730439093909315223448909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27153626062606210148965939 40730439093909315223448909)
    ·
      refine ⟨15273914660215993208793341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40730439093909315223448909 15273914660215993208793341)
      ·
        refine ⟨5727717997580997453297503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15273914660215993208793341 5727717997580997453297503)
        ·
          refine ⟨8591576996371496179946255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727717997580997453297503 8591576996371496179946255)
          ·
            refine ⟨12887365494557244269919383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591576996371496179946255 12887365494557244269919383)
            ·
              refine ⟨19331048241835866404879075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12887365494557244269919383 19331048241835866404879075)
              ·
                refine ⟨28996572362753799607318613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19331048241835866404879075 28996572362753799607318613)
                ·
                  refine ⟨339803582376021089148265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28996572362753799607318613 339803582376021089148265)
                  ·
                    rfl

theorem cell23_5955886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_5955886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955886 prefixEnd_5955886 := by exact prefixLift 5955886
  have htrace : WordTrace (prefixWord ++ tailWord_5955886) baseStart_5955886 baseEnd_5955886 := by
    simpa [prefixWord, tailWord_5955886, baseEnd_5955886] using wordTrace_append hprefix tailTrace_5955886
  have hstable : (prefixWord ++ tailWord_5955886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955886).length < 2 ^ (prefixWord ++ tailWord_5955886).sum := by decide
  have hdescent : baseEnd_5955886 < baseStart_5955886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955939 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 5]
def baseStart_5955939 : Nat := 118140960795 + 5955939 * 2 ^ 59
def prefixEnd_5955939 : Nat := 4983230072969 + 3 ^ 40 * 5955939 * 2
def baseEnd_5955939 : Nat := 3058259455858878094971641

theorem tailTrace_5955939 : CollatzResearch.WordTrace tailWord_5955939 prefixEnd_5955939 3058259455858878094971641 := by
  unfold tailWord_5955939
  simp only [CollatzResearch.WordTrace]
  refine ⟨217230941569657671243406871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144820627713105114162271247 217230941569657671243406871)
  ·
    refine ⟨325846412354486506865110307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217230941569657671243406871 325846412354486506865110307)
    ·
      refine ⟨488769618531729760297665461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325846412354486506865110307 488769618531729760297665461)
      ·
        refine ⟨45822151737349665027906137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 488769618531729760297665461 45822151737349665027906137)
        ·
          refine ⟨34366613803012248770929603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45822151737349665027906137 34366613803012248770929603)
          ·
            refine ⟨51549920704518373156394405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34366613803012248770929603 51549920704518373156394405)
            ·
              refine ⟨9665610132097194966823951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51549920704518373156394405 9665610132097194966823951)
              ·
                refine ⟨14498415198145792450235927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9665610132097194966823951 14498415198145792450235927)
                ·
                  refine ⟨21747622797218688675353891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14498415198145792450235927 21747622797218688675353891)
                  ·
                    refine ⟨32621434195828033013030837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21747622797218688675353891 32621434195828033013030837)
                    ·
                      refine ⟨3058259455858878094971641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32621434195828033013030837 3058259455858878094971641)
                      ·
                        rfl

theorem cell23_5955939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_5955939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955939 prefixEnd_5955939 := by exact prefixLift 5955939
  have htrace : WordTrace (prefixWord ++ tailWord_5955939) baseStart_5955939 baseEnd_5955939 := by
    simpa [prefixWord, tailWord_5955939, baseEnd_5955939] using wordTrace_append hprefix tailTrace_5955939
  have hstable : (prefixWord ++ tailWord_5955939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955939).length < 2 ^ (prefixWord ++ tailWord_5955939).sum := by decide
  have hdescent : baseEnd_5955939 < baseStart_5955939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955946 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_5955946 : Nat := 118140960795 + 5955946 * 2 ^ 59
def prefixEnd_5955946 : Nat := 4983230072969 + 3 ^ 40 * 5955946 * 2
def baseEnd_5955946 : Nat := 1019421016741153189194703

theorem tailTrace_5955946 : CollatzResearch.WordTrace tailWord_5955946 prefixEnd_5955946 1019421016741153189194703 := by
  unfold tailWord_5955946
  simp only [CollatzResearch.WordTrace]
  refine ⟨54307799220158077859727923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144820797920421540959274461 54307799220158077859727923)
  ·
    refine ⟨81461698830237116789591885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54307799220158077859727923 81461698830237116789591885)
    ·
      refine ⟨30548137061338918796096957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81461698830237116789591885 30548137061338918796096957)
      ·
        refine ⟨11455551398002094548536359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30548137061338918796096957 11455551398002094548536359)
        ·
          refine ⟨17183327097003141822804539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11455551398002094548536359 17183327097003141822804539)
          ·
            refine ⟨25774990645504712734206809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17183327097003141822804539 25774990645504712734206809)
            ·
              refine ⟨19331242984128534550655107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25774990645504712734206809 19331242984128534550655107)
              ·
                refine ⟨28996864476192801825982661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19331242984128534550655107 28996864476192801825982661)
                ·
                  refine ⟨5436912089286150342371749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28996864476192801825982661 5436912089286150342371749)
                  ·
                    refine ⟨1019421016741153189194703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436912089286150342371749 1019421016741153189194703)
                    ·
                      rfl

theorem cell23_5955946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_5955946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955946 prefixEnd_5955946 := by exact prefixLift 5955946
  have htrace : WordTrace (prefixWord ++ tailWord_5955946) baseStart_5955946 baseEnd_5955946 := by
    simpa [prefixWord, tailWord_5955946, baseEnd_5955946] using wordTrace_append hprefix tailTrace_5955946
  have hstable : (prefixWord ++ tailWord_5955946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955946).length < 2 ^ (prefixWord ++ tailWord_5955946).sum := by decide
  have hdescent : baseEnd_5955946 < baseStart_5955946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5955963 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 2, 4]
def baseStart_5955963 : Nat := 118140960795 + 5955963 * 2 ^ 59
def prefixEnd_5955963 : Nat := 4983230072969 + 3 ^ 40 * 5955963 * 2
def baseEnd_5955963 : Nat := 1019423926464862000357177

theorem tailTrace_5955963 : CollatzResearch.WordTrace tailWord_5955963 prefixEnd_5955963 1019423926464862000357177 := by
  unfold tailWord_5955963
  simp only [CollatzResearch.WordTrace]
  refine ⟨217231816921570723342280543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144821211281047148894853695 217231816921570723342280543)
  ·
    refine ⟨325847725382356085013420815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217231816921570723342280543 325847725382356085013420815)
    ·
      refine ⟨488771588073534127520131223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325847725382356085013420815 488771588073534127520131223)
      ·
        refine ⟨733157382110301191280196835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488771588073534127520131223 733157382110301191280196835)
        ·
          refine ⟨1099736073165451786920295253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733157382110301191280196835 1099736073165451786920295253)
          ·
            refine ⟨6443766053703819063986105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1099736073165451786920295253 6443766053703819063986105)
            ·
              refine ⟨4832824540277864297989579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443766053703819063986105 4832824540277864297989579)
              ·
                refine ⟨7249236810416796446984369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832824540277864297989579 7249236810416796446984369)
                ·
                  refine ⟨5436927607812597335238277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7249236810416796446984369 5436927607812597335238277)
                  ·
                    refine ⟨1019423926464862000357177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5436927607812597335238277 1019423926464862000357177)
                    ·
                      rfl

theorem cell23_5955963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 4].length) (baseStart_5955963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5955963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5955963 prefixEnd_5955963 := by exact prefixLift 5955963
  have htrace : WordTrace (prefixWord ++ tailWord_5955963) baseStart_5955963 baseEnd_5955963 := by
    simpa [prefixWord, tailWord_5955963, baseEnd_5955963] using wordTrace_append hprefix tailTrace_5955963
  have hstable : (prefixWord ++ tailWord_5955963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5955963).length < 2 ^ (prefixWord ++ tailWord_5955963).sum := by decide
  have hdescent : baseEnd_5955963 < baseStart_5955963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5955963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956003 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 3]
def baseStart_5956003 : Nat := 118140960795 + 5956003 * 2 ^ 59
def prefixEnd_5956003 : Nat := 4983230072969 + 3 ^ 40 * 5956003 * 2
def baseEnd_5956003 : Nat := 3058292318620765844571347

theorem tailTrace_5956003 : CollatzResearch.WordTrace tailWord_5956003 prefixEnd_5956003 3058292318620765844571347 := by
  unfold tailWord_5956003
  simp only [CollatzResearch.WordTrace]
  refine ⟨217233275841425810173736663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144822183894283873449157775 217233275841425810173736663)
  ·
    refine ⟨325849913762138715260604995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217233275841425810173736663 325849913762138715260604995)
    ·
      refine ⟨488774870643208072890907493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325849913762138715260604995 488774870643208072890907493)
      ·
        refine ⟨91645288245601513667045155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 488774870643208072890907493 91645288245601513667045155)
        ·
          refine ⟨137467932368402270500567733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91645288245601513667045155 137467932368402270500567733)
          ·
            refine ⟨12887618659537712859428225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137467932368402270500567733 12887618659537712859428225)
            ·
              refine ⟨9665713994653284644571169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12887618659537712859428225 9665713994653284644571169)
              ·
                refine ⟨7249285495989963483428377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9665713994653284644571169 7249285495989963483428377)
                ·
                  refine ⟨5436964121992472612571283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7249285495989963483428377 5436964121992472612571283)
                  ·
                    refine ⟨8155446182988708918856925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5436964121992472612571283 8155446182988708918856925)
                    ·
                      refine ⟨3058292318620765844571347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8155446182988708918856925 3058292318620765844571347)
                      ·
                        rfl

theorem cell23_5956003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_5956003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956003 prefixEnd_5956003 := by exact prefixLift 5956003
  have htrace : WordTrace (prefixWord ++ tailWord_5956003) baseStart_5956003 baseEnd_5956003 := by
    simpa [prefixWord, tailWord_5956003, baseEnd_5956003] using wordTrace_append hprefix tailTrace_5956003
  have hstable : (prefixWord ++ tailWord_5956003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956003).length < 2 ^ (prefixWord ++ tailWord_5956003).sum := by decide
  have hdescent : baseEnd_5956003 < baseStart_5956003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956010 : List Nat := [3, 1, 6, 1, 1, 2, 1, 8]
def baseStart_5956010 : Nat := 118140960795 + 5956010 * 2 ^ 59
def prefixEnd_5956010 : Nat := 4983230072969 + 3 ^ 40 * 5956010 * 2
def baseEnd_5956010 : Nat := 113270218999457308043845

theorem tailTrace_5956010 : CollatzResearch.WordTrace tailWord_5956010 prefixEnd_5956010 113270218999457308043845 := by
  unfold tailWord_5956010
  simp only [CollatzResearch.WordTrace]
  refine ⟨54308382788100112592310371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144822354101600300246160989 54308382788100112592310371)
  ·
    refine ⟨81462574182150168888465557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54308382788100112592310371 81462574182150168888465557)
    ·
      refine ⟨3818558164788289166646823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81462574182150168888465557 3818558164788289166646823)
      ·
        refine ⟨5727837247182433749970235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3818558164788289166646823 5727837247182433749970235)
        ·
          refine ⟨8591755870773650624955353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727837247182433749970235 8591755870773650624955353)
          ·
            refine ⟨6443816903080237968716515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8591755870773650624955353 6443816903080237968716515)
            ·
              refine ⟨9665725354620356953074773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443816903080237968716515 9665725354620356953074773)
              ·
                refine ⟨113270218999457308043845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9665725354620356953074773 113270218999457308043845)
                ·
                  rfl

theorem cell23_5956010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_5956010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956010 prefixEnd_5956010 := by exact prefixLift 5956010
  have htrace : WordTrace (prefixWord ++ tailWord_5956010) baseStart_5956010 baseEnd_5956010 := by
    simpa [prefixWord, tailWord_5956010, baseEnd_5956010] using wordTrace_append hprefix tailTrace_5956010
  have hstable : (prefixWord ++ tailWord_5956010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956010).length < 2 ^ (prefixWord ++ tailWord_5956010).sum := by decide
  have hdescent : baseEnd_5956010 < baseStart_5956010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956099 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4]
def baseStart_5956099 : Nat := 118140960795 + 5956099 * 2 ^ 59
def prefixEnd_5956099 : Nat := 4983230072969 + 3 ^ 40 * 5956099 * 2
def baseEnd_5956099 : Nat := 3058341612763597468970905

theorem tailTrace_5956099 : CollatzResearch.WordTrace tailWord_5956099 prefixEnd_5956099 3058341612763597468970905 := by
  unfold tailWord_5956099
  simp only [CollatzResearch.WordTrace]
  refine ⟨217236777249078018569231351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144824518166052012379487567 217236777249078018569231351)
  ·
    refine ⟨325855165873617027853847027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217236777249078018569231351 325855165873617027853847027)
    ·
      refine ⟨488782748810425541780770541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325855165873617027853847027 488782748810425541780770541)
      ·
        refine ⟨183293530803909578167788953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488782748810425541780770541 183293530803909578167788953)
        ·
          refine ⟨137470148102932183625841715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183293530803909578167788953 137470148102932183625841715)
          ·
            refine ⟨206205222154398275438762573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137470148102932183625841715 206205222154398275438762573)
            ·
              refine ⟨77326958307899353289535965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206205222154398275438762573 77326958307899353289535965)
              ·
                refine ⟨28997609365462257483575987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77326958307899353289535965 28997609365462257483575987)
                ·
                  refine ⟨43496414048193386225363981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28997609365462257483575987 43496414048193386225363981)
                  ·
                    refine ⟨16311155268072519834511493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43496414048193386225363981 16311155268072519834511493)
                    ·
                      refine ⟨3058341612763597468970905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16311155268072519834511493 3058341612763597468970905)
                      ·
                        rfl

theorem cell23_5956099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_5956099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956099 prefixEnd_5956099 := by exact prefixLift 5956099
  have htrace : WordTrace (prefixWord ++ tailWord_5956099) baseStart_5956099 baseEnd_5956099 := by
    simpa [prefixWord, tailWord_5956099, baseEnd_5956099] using wordTrace_append hprefix tailTrace_5956099
  have hstable : (prefixWord ++ tailWord_5956099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956099).length < 2 ^ (prefixWord ++ tailWord_5956099).sum := by decide
  have hdescent : baseEnd_5956099 < baseStart_5956099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956100 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 5]
def baseStart_5956100 : Nat := 118140960795 + 5956100 * 2 ^ 59
def prefixEnd_5956100 : Nat := 4983230072969 + 3 ^ 40 * 5956100 * 2
def baseEnd_5956100 : Nat := 339815791804916885006489

theorem tailTrace_5956100 : CollatzResearch.WordTrace tailWord_5956100 prefixEnd_5956100 339815791804916885006489 := by
  unfold tailWord_5956100
  simp only [CollatzResearch.WordTrace]
  refine ⟨108618406861037197870008877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144824542481382930493345169 108618406861037197870008877)
  ·
    refine ⟨40731902572888949201253329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108618406861037197870008877 40731902572888949201253329)
    ·
      refine ⟨30548926929666711900939997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40731902572888949201253329 30548926929666711900939997)
      ·
        refine ⟨11455847598625016962852499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30548926929666711900939997 11455847598625016962852499)
        ·
          refine ⟨17183771397937525444278749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11455847598625016962852499 17183771397937525444278749)
          ·
            refine ⟨6443914274226572041604531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17183771397937525444278749 6443914274226572041604531)
            ·
              refine ⟨9665871411339858062406797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443914274226572041604531 9665871411339858062406797)
              ·
                refine ⟨3624701779252446773402549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9665871411339858062406797 3624701779252446773402549)
                ·
                  refine ⟨339815791804916885006489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3624701779252446773402549 339815791804916885006489)
                  ·
                    rfl

theorem cell23_5956100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_5956100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956100 prefixEnd_5956100 := by exact prefixLift 5956100
  have htrace : WordTrace (prefixWord ++ tailWord_5956100) baseStart_5956100 baseEnd_5956100 := by
    simpa [prefixWord, tailWord_5956100, baseEnd_5956100] using wordTrace_append hprefix tailTrace_5956100
  have hstable : (prefixWord ++ tailWord_5956100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956100).length < 2 ^ (prefixWord ++ tailWord_5956100).sum := by decide
  have hdescent : baseEnd_5956100 < baseStart_5956100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956150 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_5956150 : Nat := 118140960795 + 5956150 * 2 ^ 59
def prefixEnd_5956150 : Nat := 4983230072969 + 3 ^ 40 * 5956150 * 2
def baseEnd_5956150 : Nat := 3058367800276976769433171

theorem tailTrace_5956150 : CollatzResearch.WordTrace tailWord_5956150 prefixEnd_5956150 3058367800276976769433171 := by
  unfold tailWord_5956150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577414835743328392458619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144825758247928836186225269 13577414835743328392458619)
  ·
    refine ⟨20366122253614992588687929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13577414835743328392458619 20366122253614992588687929)
    ·
      refine ⟨15274591690211244441515947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20366122253614992588687929 15274591690211244441515947)
      ·
        refine ⟨22911887535316866662273921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15274591690211244441515947 22911887535316866662273921)
        ·
          refine ⟨17183915651487649996705441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22911887535316866662273921 17183915651487649996705441)
          ·
            refine ⟨12887936738615737497529081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17183915651487649996705441 12887936738615737497529081)
            ·
              refine ⟨9665952553961803123146811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12887936738615737497529081 9665952553961803123146811)
              ·
                refine ⟨14498928830942704684720217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9665952553961803123146811 14498928830942704684720217)
                ·
                  refine ⟨10874196623207028513540163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14498928830942704684720217 10874196623207028513540163)
                  ·
                    refine ⟨16311294934810542770310245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10874196623207028513540163 16311294934810542770310245)
                    ·
                      refine ⟨3058367800276976769433171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16311294934810542770310245 3058367800276976769433171)
                      ·
                        rfl

theorem cell23_5956150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_5956150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956150 prefixEnd_5956150 := by exact prefixLift 5956150
  have htrace : WordTrace (prefixWord ++ tailWord_5956150) baseStart_5956150 baseEnd_5956150 := by
    simpa [prefixWord, tailWord_5956150, baseEnd_5956150] using wordTrace_append hprefix tailTrace_5956150
  have hstable : (prefixWord ++ tailWord_5956150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956150).length < 2 ^ (prefixWord ++ tailWord_5956150).sum := by decide
  have hdescent : baseEnd_5956150 < baseStart_5956150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956153 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5956153 : Nat := 118140960795 + 5956153 * 2 ^ 59
def prefixEnd_5956153 : Nat := 4983230072969 + 3 ^ 40 * 5956153 * 2
def baseEnd_5956153 : Nat := 3058369340718940257695657

theorem tailTrace_5956153 : CollatzResearch.WordTrace tailWord_5956153 prefixEnd_5956153 3058369340718940257695657 := by
  unfold tailWord_5956153
  simp only [CollatzResearch.WordTrace]
  refine ⟨217238746790882385791697113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144825831193921590527798075 217238746790882385791697113)
  ·
    refine ⟨162929060093161789343772835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217238746790882385791697113 162929060093161789343772835)
    ·
      refine ⟨244393590139742684015659253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162929060093161789343772835 244393590139742684015659253)
      ·
        refine ⟨22911899075600876626468055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244393590139742684015659253 22911899075600876626468055)
        ·
          refine ⟨34367848613401314939702083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22911899075600876626468055 34367848613401314939702083)
          ·
            refine ⟨51551772920101972409553125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34367848613401314939702083 51551772920101972409553125)
            ·
              refine ⟨9665957422519119826791211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51551772920101972409553125 9665957422519119826791211)
              ·
                refine ⟨14498936133778679740186817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9665957422519119826791211 14498936133778679740186817)
                ·
                  refine ⟨10874202100334009805140113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14498936133778679740186817 10874202100334009805140113)
                  ·
                    refine ⟨8155651575250507353855085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10874202100334009805140113 8155651575250507353855085)
                    ·
                      refine ⟨3058369340718940257695657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8155651575250507353855085 3058369340718940257695657)
                      ·
                        rfl

theorem cell23_5956153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5956153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956153 prefixEnd_5956153 := by exact prefixLift 5956153
  have htrace : WordTrace (prefixWord ++ tailWord_5956153) baseStart_5956153 baseEnd_5956153 := by
    simpa [prefixWord, tailWord_5956153, baseEnd_5956153] using wordTrace_append hprefix tailTrace_5956153
  have hstable : (prefixWord ++ tailWord_5956153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956153).length < 2 ^ (prefixWord ++ tailWord_5956153).sum := by decide
  have hdescent : baseEnd_5956153 < baseStart_5956153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956173 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5956173 : Nat := 118140960795 + 5956173 * 2 ^ 59
def prefixEnd_5956173 : Nat := 4983230072969 + 3 ^ 40 * 5956173 * 2
def baseEnd_5956173 : Nat := 339819956703558908827285

theorem tailTrace_5956173 : CollatzResearch.WordTrace tailWord_5956173 prefixEnd_5956173 339819956703558908827285 := by
  unfold tailWord_5956173
  simp only [CollatzResearch.WordTrace]
  refine ⟨217239476250809929207425173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144826317500539952804950115 217239476250809929207425173)
  ·
    refine ⟨10183100449256715431598055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217239476250809929207425173 10183100449256715431598055)
    ·
      refine ⟨15274650673885073147397083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10183100449256715431598055 15274650673885073147397083)
      ·
        refine ⟨22911976010827609721095625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15274650673885073147397083 22911976010827609721095625)
        ·
          refine ⟨17183982008120707290821719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22911976010827609721095625 17183982008120707290821719)
          ·
            refine ⟨25775973012181060936232579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17183982008120707290821719 25775973012181060936232579)
            ·
              refine ⟨38663959518271591404348869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25775973012181060936232579 38663959518271591404348869)
              ·
                refine ⟨7249492409675923388315413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38663959518271591404348869 7249492409675923388315413)
                ·
                  refine ⟨339819956703558908827285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7249492409675923388315413 339819956703558908827285)
                  ·
                    rfl

theorem cell23_5956173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5956173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956173 prefixEnd_5956173 := by exact prefixLift 5956173
  have htrace : WordTrace (prefixWord ++ tailWord_5956173) baseStart_5956173 baseEnd_5956173 := by
    simpa [prefixWord, tailWord_5956173, baseEnd_5956173] using wordTrace_append hprefix tailTrace_5956173
  have hstable : (prefixWord ++ tailWord_5956173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956173).length < 2 ^ (prefixWord ++ tailWord_5956173).sum := by decide
  have hdescent : baseEnd_5956173 < baseStart_5956173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956177 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 1, 4]
def baseStart_5956177 : Nat := 118140960795 + 5956177 * 2 ^ 59
def prefixEnd_5956177 : Nat := 4983230072969 + 3 ^ 40 * 5956177 * 2
def baseEnd_5956177 : Nat := 1019460554751549387931849

theorem tailTrace_5956177 : CollatzResearch.WordTrace tailWord_5956177 prefixEnd_5956177 1019460554751549387931849 := by
  unfold tailWord_5956177
  simp only [CollatzResearch.WordTrace]
  refine ⟨217239622142795437890570785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144826414761863625260380523 217239622142795437890570785)
  ·
    refine ⟨162929716607096578417928089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217239622142795437890570785 162929716607096578417928089)
    ·
      refine ⟨122197287455322433813446067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162929716607096578417928089 122197287455322433813446067)
      ·
        refine ⟨183295931182983650720169101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122197287455322433813446067 183295931182983650720169101)
        ·
          refine ⟨68735974193618869020063413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183295931182983650720169101 68735974193618869020063413)
          ·
            refine ⟨6443997580651768970630945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68735974193618869020063413 6443997580651768970630945)
            ·
              refine ⟨4832998185488826727973209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443997580651768970630945 4832998185488826727973209)
              ·
                refine ⟨3624748639116620045979907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832998185488826727973209 3624748639116620045979907)
                ·
                  refine ⟨5437122958674930068969861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624748639116620045979907 5437122958674930068969861)
                  ·
                    refine ⟨1019460554751549387931849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437122958674930068969861 1019460554751549387931849)
                    ·
                      rfl

theorem cell23_5956177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_5956177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956177 prefixEnd_5956177 := by exact prefixLift 5956177
  have htrace : WordTrace (prefixWord ++ tailWord_5956177) baseStart_5956177 baseEnd_5956177 := by
    simpa [prefixWord, tailWord_5956177, baseEnd_5956177] using wordTrace_append hprefix tailTrace_5956177
  have hstable : (prefixWord ++ tailWord_5956177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956177).length < 2 ^ (prefixWord ++ tailWord_5956177).sum := by decide
  have hdescent : baseEnd_5956177 < baseStart_5956177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956183 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_5956183 : Nat := 118140960795 + 5956183 * 2 ^ 59
def prefixEnd_5956183 : Nat := 4983230072969 + 3 ^ 40 * 5956183 * 2
def baseEnd_5956183 : Nat := 3058384745138575140320519

theorem tailTrace_5956183 : CollatzResearch.WordTrace tailWord_5956183 prefixEnd_5956183 3058384745138575140320519 := by
  unfold tailWord_5956183
  simp only [CollatzResearch.WordTrace]
  refine ⟨217239840980773700915289203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144826560653849133943526135 217239840980773700915289203)
  ·
    refine ⟨325859761471160551372933805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217239840980773700915289203 325859761471160551372933805)
    ·
      refine ⟨122197410551685206764850177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325859761471160551372933805 122197410551685206764850177)
      ·
        refine ⟨91648057913763905073637633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122197410551685206764850177 91648057913763905073637633)
        ·
          refine ⟨68736043435322928805228225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91648057913763905073637633 68736043435322928805228225)
          ·
            refine ⟨51552032576492196603921169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68736043435322928805228225 51552032576492196603921169)
            ·
              refine ⟨38664024432369147452940877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51552032576492196603921169 38664024432369147452940877)
              ·
                refine ⟨14499009162138430294852829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38664024432369147452940877 14499009162138430294852829)
                ·
                  refine ⟨5437128435801911360569811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14499009162138430294852829 5437128435801911360569811)
                  ·
                    refine ⟨8155692653702867040854717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437128435801911360569811 8155692653702867040854717)
                    ·
                      refine ⟨3058384745138575140320519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8155692653702867040854717 3058384745138575140320519)
                      ·
                        rfl

theorem cell23_5956183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_5956183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956183 prefixEnd_5956183 := by exact prefixLift 5956183
  have htrace : WordTrace (prefixWord ++ tailWord_5956183) baseStart_5956183 baseEnd_5956183 := by
    simpa [prefixWord, tailWord_5956183, baseEnd_5956183] using wordTrace_append hprefix tailTrace_5956183
  have hstable : (prefixWord ++ tailWord_5956183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956183).length < 2 ^ (prefixWord ++ tailWord_5956183).sum := by decide
  have hdescent : baseEnd_5956183 < baseStart_5956183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956210 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_5956210 : Nat := 118140960795 + 5956210 * 2 ^ 59
def prefixEnd_5956210 : Nat := 4983230072969 + 3 ^ 40 * 5956210 * 2
def baseEnd_5956210 : Nat := 3058398609116246534682895

theorem tailTrace_5956210 : CollatzResearch.WordTrace tailWord_5956210 prefixEnd_5956210 3058398609116246534682895 := by
  unfold tailWord_5956210
  simp only [CollatzResearch.WordTrace]
  refine ⟨54310206437918971131630521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144827217167783923017681389 54310206437918971131630521)
  ·
    refine ⟨40732654828439228348722891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54310206437918971131630521 40732654828439228348722891)
    ·
      refine ⟨61098982242658842523084337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40732654828439228348722891 61098982242658842523084337)
      ·
        refine ⟨45824236681994131892313253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61098982242658842523084337 45824236681994131892313253)
        ·
          refine ⟨8592044377873899729808735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45824236681994131892313253 8592044377873899729808735)
          ·
            refine ⟨12888066566810849594713103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592044377873899729808735 12888066566810849594713103)
            ·
              refine ⟨19332099850216274392069655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888066566810849594713103 19332099850216274392069655)
              ·
                refine ⟨28998149775324411588104483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19332099850216274392069655 28998149775324411588104483)
                ·
                  refine ⟨43497224662986617382156725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28998149775324411588104483 43497224662986617382156725)
                  ·
                    refine ⟨4077864812154995379577193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43497224662986617382156725 4077864812154995379577193)
                    ·
                      refine ⟨3058398609116246534682895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4077864812154995379577193 3058398609116246534682895)
                      ·
                        rfl

theorem cell23_5956210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_5956210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956210 prefixEnd_5956210 := by exact prefixLift 5956210
  have htrace : WordTrace (prefixWord ++ tailWord_5956210) baseStart_5956210 baseEnd_5956210 := by
    simpa [prefixWord, tailWord_5956210, baseEnd_5956210] using wordTrace_append hprefix tailTrace_5956210
  have hstable : (prefixWord ++ tailWord_5956210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956210).length < 2 ^ (prefixWord ++ tailWord_5956210).sum := by decide
  have hdescent : baseEnd_5956210 < baseStart_5956210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956216 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 6, 4]
def baseStart_5956216 : Nat := 118140960795 + 5956216 * 2 ^ 59
def prefixEnd_5956216 : Nat := 4983230072969 + 3 ^ 40 * 5956216 * 2
def baseEnd_5956216 : Nat := 1019467230000057837069289

theorem tailTrace_5956216 : CollatzResearch.WordTrace tailWord_5956216 prefixEnd_5956216 1019467230000057837069289 := by
  unfold tailWord_5956216
  simp only [CollatzResearch.WordTrace]
  refine ⟨108620522294827073775620251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144827363059769431700827001 108620522294827073775620251)
  ·
    refine ⟨162930783442240610663430377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108620522294827073775620251 162930783442240610663430377)
    ·
      refine ⟨122198087581680457997572783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162930783442240610663430377 122198087581680457997572783)
      ·
        refine ⟨183297131372520686996359175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122198087581680457997572783 183297131372520686996359175)
        ·
          refine ⟨274945697058781030494538763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183297131372520686996359175 274945697058781030494538763)
          ·
            refine ⟨412418545588171545741808145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274945697058781030494538763 412418545588171545741808145)
            ·
              refine ⟨309313909191128659306356109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412418545588171545741808145 309313909191128659306356109)
              ·
                refine ⟨115992715946673247239883541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309313909191128659306356109 115992715946673247239883541)
                ·
                  refine ⟨5437158560000308464369541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115992715946673247239883541 5437158560000308464369541)
                  ·
                    refine ⟨1019467230000057837069289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437158560000308464369541 1019467230000057837069289)
                    ·
                      rfl

theorem cell23_5956216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_5956216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956216 prefixEnd_5956216 := by exact prefixLift 5956216
  have htrace : WordTrace (prefixWord ++ tailWord_5956216) baseStart_5956216 baseEnd_5956216 := by
    simpa [prefixWord, tailWord_5956216, baseEnd_5956216] using wordTrace_append hprefix tailTrace_5956216
  have hstable : (prefixWord ++ tailWord_5956216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956216).length < 2 ^ (prefixWord ++ tailWord_5956216).sum := by decide
  have hdescent : baseEnd_5956216 < baseStart_5956216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956217 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 1, 1, 3]
def baseStart_5956217 : Nat := 118140960795 + 5956217 * 2 ^ 59
def prefixEnd_5956217 : Nat := 4983230072969 + 3 ^ 40 * 5956217 * 2
def baseEnd_5956217 : Nat := 3058402203480828007295363

theorem tailTrace_5956217 : CollatzResearch.WordTrace tailWord_5956217 prefixEnd_5956217 3058402203480828007295363 := by
  unfold tailWord_5956217
  simp only [CollatzResearch.WordTrace]
  refine ⟨217241081062650524722026905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144827387375100349814684603 217241081062650524722026905)
  ·
    refine ⟨162930810796987893541520179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217241081062650524722026905 162930810796987893541520179)
    ·
      refine ⟨244396216195481840312280269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162930810796987893541520179 244396216195481840312280269)
      ·
        refine ⟨91648581073305690117105101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244396216195481840312280269 91648581073305690117105101)
        ·
          refine ⟨34368217902489633793914413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91648581073305690117105101 34368217902489633793914413)
          ·
            refine ⟨12888081713433612672717905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34368217902489633793914413 12888081713433612672717905)
            ·
              refine ⟨9666061285075209504538429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12888081713433612672717905 9666061285075209504538429)
              ·
                refine ⟨3624772981903203564201911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9666061285075209504538429 3624772981903203564201911)
                ·
                  refine ⟨5437159472854805346302867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624772981903203564201911 5437159472854805346302867)
                  ·
                    refine ⟨8155739209282208019454301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437159472854805346302867 8155739209282208019454301)
                    ·
                      refine ⟨3058402203480828007295363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8155739209282208019454301 3058402203480828007295363)
                      ·
                        rfl

theorem cell23_5956217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_5956217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956217 prefixEnd_5956217 := by exact prefixLift 5956217
  have htrace : WordTrace (prefixWord ++ tailWord_5956217) baseStart_5956217 baseEnd_5956217 := by
    simpa [prefixWord, tailWord_5956217, baseEnd_5956217] using wordTrace_append hprefix tailTrace_5956217
  have hstable : (prefixWord ++ tailWord_5956217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956217).length < 2 ^ (prefixWord ++ tailWord_5956217).sum := by decide
  have hdescent : baseEnd_5956217 < baseStart_5956217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956253 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_5956253 : Nat := 118140960795 + 5956253 * 2 ^ 59
def prefixEnd_5956253 : Nat := 4983230072969 + 3 ^ 40 * 5956253 * 2
def baseEnd_5956253 : Nat := 3058420688784389866445197

theorem tailTrace_5956253 : CollatzResearch.WordTrace tailWord_5956253 prefixEnd_5956253 3058420688784389866445197 := by
  unfold tailWord_5956253
  simp only [CollatzResearch.WordTrace]
  refine ⟨217242394090520102870337413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144828262727013401913558275 217242394090520102870337413)
  ·
    refine ⟨40732948891972519288188265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217242394090520102870337413 40732948891972519288188265)
    ·
      refine ⟨30549711668979389466141199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40732948891972519288188265 30549711668979389466141199)
      ·
        refine ⟨45824567503469084199211799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30549711668979389466141199 45824567503469084199211799)
        ·
          refine ⟨68736851255203626298817699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45824567503469084199211799 68736851255203626298817699)
          ·
            refine ⟨103105276882805439448226549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68736851255203626298817699 103105276882805439448226549)
            ·
              refine ⟨9666119707763009948271239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103105276882805439448226549 9666119707763009948271239)
              ·
                refine ⟨14499179561644514922406859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9666119707763009948271239 14499179561644514922406859)
                ·
                  refine ⟨21748769342466772383610289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14499179561644514922406859 21748769342466772383610289)
                  ·
                    refine ⟨16311577006850079287707717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21748769342466772383610289 16311577006850079287707717)
                    ·
                      refine ⟨3058420688784389866445197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16311577006850079287707717 3058420688784389866445197)
                      ·
                        rfl

theorem cell23_5956253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_5956253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956253 prefixEnd_5956253 := by exact prefixLift 5956253
  have htrace : WordTrace (prefixWord ++ tailWord_5956253) baseStart_5956253 baseEnd_5956253 := by
    simpa [prefixWord, tailWord_5956253, baseEnd_5956253] using wordTrace_append hprefix tailTrace_5956253
  have hstable : (prefixWord ++ tailWord_5956253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956253).length < 2 ^ (prefixWord ++ tailWord_5956253).sum := by decide
  have hdescent : baseEnd_5956253 < baseStart_5956253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956260 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_5956260 : Nat := 118140960795 + 5956260 * 2 ^ 59
def prefixEnd_5956260 : Nat := 4983230072969 + 3 ^ 40 * 5956260 * 2
def baseEnd_5956260 : Nat := 3058424283148971339057665

theorem tailTrace_5956260 : CollatzResearch.WordTrace tailWord_5956260 prefixEnd_5956260 3058424283148971339057665 := by
  unfold tailWord_5956260
  simp only [CollatzResearch.WordTrace]
  refine ⟨108621324700747371532921117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144828432934329828710561489 108621324700747371532921117)
  ·
    refine ⟨40732996762780264324845419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108621324700747371532921117 40732996762780264324845419)
    ·
      refine ⟨61099495144170396487268129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40732996762780264324845419 61099495144170396487268129)
      ·
        refine ⟨45824621358127797365451097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61099495144170396487268129 45824621358127797365451097)
        ·
          refine ⟨34368466018595848024088323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45824621358127797365451097 34368466018595848024088323)
          ·
            refine ⟨51552699027893772036132485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34368466018595848024088323 51552699027893772036132485)
            ·
              refine ⟨9666131067730082256774841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51552699027893772036132485 9666131067730082256774841)
              ·
                refine ⟨7249598300797561692581131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9666131067730082256774841 7249598300797561692581131)
                ·
                  refine ⟨10874397451196342538871697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7249598300797561692581131 10874397451196342538871697)
                  ·
                    refine ⟨8155798088397256904153773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10874397451196342538871697 8155798088397256904153773)
                    ·
                      refine ⟨3058424283148971339057665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8155798088397256904153773 3058424283148971339057665)
                      ·
                        rfl

theorem cell23_5956260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_5956260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956260 prefixEnd_5956260 := by exact prefixLift 5956260
  have htrace : WordTrace (prefixWord ++ tailWord_5956260) baseStart_5956260 baseEnd_5956260 := by
    simpa [prefixWord, tailWord_5956260, baseEnd_5956260] using wordTrace_append hprefix tailTrace_5956260
  have hstable : (prefixWord ++ tailWord_5956260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956260).length < 2 ^ (prefixWord ++ tailWord_5956260).sum := by decide
  have hdescent : baseEnd_5956260 < baseStart_5956260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956283 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 7, 3, 2]
def baseStart_5956283 : Nat := 118140960795 + 5956283 * 2 ^ 59
def prefixEnd_5956283 : Nat := 4983230072969 + 3 ^ 40 * 5956283 * 2
def baseEnd_5956283 : Nat := 3058436093204024749070059

theorem tailTrace_5956283 : CollatzResearch.WordTrace tailWord_5956283 prefixEnd_5956283 3058436093204024749070059 := by
  unfold tailWord_5956283
  simp only [CollatzResearch.WordTrace]
  refine ⟨217243488280411417993929503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144828992186940945329286335 217243488280411417993929503)
  ·
    refine ⟨325865232420617126990894255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217243488280411417993929503 325865232420617126990894255)
    ·
      refine ⟨488797848630925690486341383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325865232420617126990894255 488797848630925690486341383)
      ·
        refine ⟨733196772946388535729512075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488797848630925690486341383 733196772946388535729512075)
        ·
          refine ⟨1099795159419582803594268113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733196772946388535729512075 1099795159419582803594268113)
          ·
            refine ⟨824846369564687102695701085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099795159419582803594268113 824846369564687102695701085)
            ·
              refine ⟨309317388586757663510887907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 824846369564687102695701085 309317388586757663510887907)
              ·
                refine ⟨463976082880136495266331861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309317388586757663510887907 463976082880136495266331861)
                ·
                  refine ⟨10874439442503199107804653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 463976082880136495266331861 10874439442503199107804653)
                  ·
                    refine ⟨4077914790938699665426745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10874439442503199107804653 4077914790938699665426745)
                    ·
                      refine ⟨3058436093204024749070059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4077914790938699665426745 3058436093204024749070059)
                      ·
                        rfl

theorem cell23_5956283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3, 2].length) (baseStart_5956283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956283 prefixEnd_5956283 := by exact prefixLift 5956283
  have htrace : WordTrace (prefixWord ++ tailWord_5956283) baseStart_5956283 baseEnd_5956283 := by
    simpa [prefixWord, tailWord_5956283, baseEnd_5956283] using wordTrace_append hprefix tailTrace_5956283
  have hstable : (prefixWord ++ tailWord_5956283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956283).length < 2 ^ (prefixWord ++ tailWord_5956283).sum := by decide
  have hdescent : baseEnd_5956283 < baseStart_5956283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956301 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5956301 : Nat := 118140960795 + 5956301 * 2 ^ 59
def prefixEnd_5956301 : Nat := 4983230072969 + 3 ^ 40 * 5956301 * 2
def baseEnd_5956301 : Nat := 1019481778618601892881659

theorem tailTrace_5956301 : CollatzResearch.WordTrace tailWord_5956301 prefixEnd_5956301 1019481778618601892881659 := by
  unfold tailWord_5956301
  simp only [CollatzResearch.WordTrace]
  refine ⟨217244144794346207068084757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144829429862897471378723171 217244144794346207068084757)
  ·
    refine ⟨10183319287234978456316473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217244144794346207068084757 10183319287234978456316473)
    ·
      refine ⟨7637489465426233842237355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10183319287234978456316473 7637489465426233842237355)
      ·
        refine ⟨11456234198139350763356033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7637489465426233842237355 11456234198139350763356033)
        ·
          refine ⟨8592175648604513072517025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11456234198139350763356033 8592175648604513072517025)
          ·
            refine ⟨6444131736453384804387769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8592175648604513072517025 6444131736453384804387769)
            ·
              refine ⟨4833098802340038603290827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6444131736453384804387769 4833098802340038603290827)
              ·
                refine ⟨7249648203510057904936241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833098802340038603290827 7249648203510057904936241)
                ·
                  refine ⟨5437236152632543428702181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7249648203510057904936241 5437236152632543428702181)
                  ·
                    refine ⟨1019481778618601892881659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437236152632543428702181 1019481778618601892881659)
                    ·
                      rfl

theorem cell23_5956301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5956301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956301 prefixEnd_5956301 := by exact prefixLift 5956301
  have htrace : WordTrace (prefixWord ++ tailWord_5956301) baseStart_5956301 baseEnd_5956301 := by
    simpa [prefixWord, tailWord_5956301, baseEnd_5956301] using wordTrace_append hprefix tailTrace_5956301
  have hstable : (prefixWord ++ tailWord_5956301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956301).length < 2 ^ (prefixWord ++ tailWord_5956301).sum := by decide
  have hdescent : baseEnd_5956301 < baseStart_5956301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956333 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5956333 : Nat := 118140960795 + 5956333 * 2 ^ 59
def prefixEnd_5956333 : Nat := 4983230072969 + 3 ^ 40 * 5956333 * 2
def baseEnd_5956333 : Nat := 3058461767236749553444829

theorem tailTrace_5956333 : CollatzResearch.WordTrace tailWord_5956333 prefixEnd_5956333 3058461767236749553444829 := by
  unfold tailWord_5956333
  simp only [CollatzResearch.WordTrace]
  refine ⟨217245311930230276533249653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144830207953486851022166435 217245311930230276533249653)
  ·
    refine ⟨20366747993459088424992155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217245311930230276533249653 20366747993459088424992155)
    ·
      refine ⟨30550121990188632637488233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20366747993459088424992155 30550121990188632637488233)
      ·
        refine ⟨22912591492641474478116175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30550121990188632637488233 22912591492641474478116175)
        ·
          refine ⟨34368887238962211717174263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22912591492641474478116175 34368887238962211717174263)
          ·
            refine ⟨51553330858443317575761395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34368887238962211717174263 51553330858443317575761395)
            ·
              refine ⟨77329996287664976363642093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51553330858443317575761395 77329996287664976363642093)
              ·
                refine ⟨28998748607874366136365785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77329996287664976363642093 28998748607874366136365785)
                ·
                  refine ⟨21749061455905774602274339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28998748607874366136365785 21749061455905774602274339)
                  ·
                    refine ⟨32623592183858661903411509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21749061455905774602274339 32623592183858661903411509)
                    ·
                      refine ⟨3058461767236749553444829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32623592183858661903411509 3058461767236749553444829)
                      ·
                        rfl

theorem cell23_5956333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5956333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956333 prefixEnd_5956333 := by exact prefixLift 5956333
  have htrace : WordTrace (prefixWord ++ tailWord_5956333) baseStart_5956333 baseEnd_5956333 := by
    simpa [prefixWord, tailWord_5956333, baseEnd_5956333] using wordTrace_append hprefix tailTrace_5956333
  have hstable : (prefixWord ++ tailWord_5956333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956333).length < 2 ^ (prefixWord ++ tailWord_5956333).sum := by decide
  have hdescent : baseEnd_5956333 < baseStart_5956333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956334 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_5956334 : Nat := 118140960795 + 5956334 * 2 ^ 59
def prefixEnd_5956334 : Nat := 4983230072969 + 3 ^ 40 * 5956334 * 2
def baseEnd_5956334 : Nat := 3058462280717404049532325

theorem tailTrace_5956334 : CollatzResearch.WordTrace tailWord_5956334 prefixEnd_5956334 3058462280717404049532325 := by
  unfold tailWord_5956334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27155668550403331713004507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144830232268817769136024037 27155668550403331713004507)
  ·
    refine ⟨40733502825604997569506761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27155668550403331713004507 40733502825604997569506761)
    ·
      refine ⟨30550127119203748177130071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40733502825604997569506761 30550127119203748177130071)
      ·
        refine ⟨45825190678805622265695107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30550127119203748177130071 45825190678805622265695107)
        ·
          refine ⟨68737786018208433398542661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45825190678805622265695107 68737786018208433398542661)
          ·
            refine ⟨12888334878414081262226749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68737786018208433398542661 12888334878414081262226749)
            ·
              refine ⟨4833125579405280473335031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12888334878414081262226749 4833125579405280473335031)
              ·
                refine ⟨7249688369107920710002547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833125579405280473335031 7249688369107920710002547)
                ·
                  refine ⟨10874532553661881065003821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7249688369107920710002547 10874532553661881065003821)
                  ·
                    refine ⟨4077949707623205399376433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10874532553661881065003821 4077949707623205399376433)
                    ·
                      refine ⟨3058462280717404049532325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4077949707623205399376433 3058462280717404049532325)
                      ·
                        rfl

theorem cell23_5956334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_5956334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956334 prefixEnd_5956334 := by exact prefixLift 5956334
  have htrace : WordTrace (prefixWord ++ tailWord_5956334) baseStart_5956334 baseEnd_5956334 := by
    simpa [prefixWord, tailWord_5956334, baseEnd_5956334] using wordTrace_append hprefix tailTrace_5956334
  have hstable : (prefixWord ++ tailWord_5956334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956334).length < 2 ^ (prefixWord ++ tailWord_5956334).sum := by decide
  have hdescent : baseEnd_5956334 < baseStart_5956334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956346 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_5956346 : Nat := 118140960795 + 5956346 * 2 ^ 59
def prefixEnd_5956346 : Nat := 4983230072969 + 3 ^ 40 * 5956346 * 2
def baseEnd_5956346 : Nat := 3058468442485258002582269

theorem tailTrace_5956346 : CollatzResearch.WordTrace tailWord_5956346 prefixEnd_5956346 3058468442485258002582269 := by
  unfold tailWord_5956346
  simp only [CollatzResearch.WordTrace]
  refine ⟨54311446519795794938368223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144830524052788786502315261 54311446519795794938368223)
  ·
    refine ⟨81467169779693692407552335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54311446519795794938368223 81467169779693692407552335)
    ·
      refine ⟨122200754669540538611328503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81467169779693692407552335 122200754669540538611328503)
      ·
        refine ⟨183301132004310807916992755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122200754669540538611328503 183301132004310807916992755)
        ·
          refine ⟨274951698006466211875489133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183301132004310807916992755 274951698006466211875489133)
          ·
            refine ⟨103106886752424829453308425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274951698006466211875489133 103106886752424829453308425)
            ·
              refine ⟨77330165064318622089981319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103106886752424829453308425 77330165064318622089981319)
              ·
                refine ⟨115995247596477933134971979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77330165064318622089981319 115995247596477933134971979)
                ·
                  refine ⟨173992871394716899702457969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115995247596477933134971979 173992871394716899702457969)
                  ·
                    refine ⟨130494653546037674776843477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173992871394716899702457969 130494653546037674776843477)
                    ·
                      refine ⟨3058468442485258002582269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130494653546037674776843477 3058468442485258002582269)
                      ·
                        rfl

theorem cell23_5956346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_5956346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956346 prefixEnd_5956346 := by exact prefixLift 5956346
  have htrace : WordTrace (prefixWord ++ tailWord_5956346) baseStart_5956346 baseEnd_5956346 := by
    simpa [prefixWord, tailWord_5956346, baseEnd_5956346] using wordTrace_append hprefix tailTrace_5956346
  have hstable : (prefixWord ++ tailWord_5956346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956346).length < 2 ^ (prefixWord ++ tailWord_5956346).sum := by decide
  have hdescent : baseEnd_5956346 < baseStart_5956346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956350 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5956350 : Nat := 118140960795 + 5956350 * 2 ^ 59
def prefixEnd_5956350 : Nat := 4983230072969 + 3 ^ 40 * 5956350 * 2
def baseEnd_5956350 : Nat := 3058470496407875986932251

theorem tailTrace_5956350 : CollatzResearch.WordTrace tailWord_5956350 prefixEnd_5956350 3058470496407875986932251 := by
  unfold tailWord_5956350
  simp only [CollatzResearch.WordTrace]
  refine ⟨27155741496396086054577313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144830621314112458957745669 27155741496396086054577313)
  ·
    refine ⟨20366806122297064540932985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27155741496396086054577313 20366806122297064540932985)
    ·
      refine ⟨15275104591722798405699739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20366806122297064540932985 15275104591722798405699739)
      ·
        refine ⟨22912656887584197608549609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15275104591722798405699739 22912656887584197608549609)
        ·
          refine ⟨17184492665688148206412207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22912656887584197608549609 17184492665688148206412207)
          ·
            refine ⟨25776738998532222309618311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17184492665688148206412207 25776738998532222309618311)
            ·
              refine ⟨38665108497798333464427467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25776738998532222309618311 38665108497798333464427467)
              ·
                refine ⟨57997662746697500196641201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38665108497798333464427467 57997662746697500196641201)
                ·
                  refine ⟨43498247060023125147480901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57997662746697500196641201 43498247060023125147480901)
                  ·
                    refine ⟨8155921323754335965152669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43498247060023125147480901 8155921323754335965152669)
                    ·
                      refine ⟨3058470496407875986932251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8155921323754335965152669 3058470496407875986932251)
                      ·
                        rfl

theorem cell23_5956350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5956350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956350 prefixEnd_5956350 := by exact prefixLift 5956350
  have htrace : WordTrace (prefixWord ++ tailWord_5956350) baseStart_5956350 baseEnd_5956350 := by
    simpa [prefixWord, tailWord_5956350, baseEnd_5956350] using wordTrace_append hprefix tailTrace_5956350
  have hstable : (prefixWord ++ tailWord_5956350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956350).length < 2 ^ (prefixWord ++ tailWord_5956350).sum := by decide
  have hdescent : baseEnd_5956350 < baseStart_5956350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956383 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 1, 7]
def baseStart_5956383 : Nat := 118140960795 + 5956383 * 2 ^ 59
def prefixEnd_5956383 : Nat := 4983230072969 + 3 ^ 40 * 5956383 * 2
def baseEnd_5956383 : Nat := 1019495813756491452606533

theorem tailTrace_5956383 : CollatzResearch.WordTrace tailWord_5956383 prefixEnd_5956383 1019495813756491452606533 := by
  unfold tailWord_5956383
  simp only [CollatzResearch.WordTrace]
  refine ⟨217247135580049135072569803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144831423720032756715046535 217247135580049135072569803)
  ·
    refine ⟨325870703370073702608854705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217247135580049135072569803 325870703370073702608854705)
    ·
      refine ⟨244403027527555276956641029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325870703370073702608854705 244403027527555276956641029)
      ·
        refine ⟨45825567661416614429370193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244403027527555276956641029 45825567661416614429370193)
        ·
          refine ⟨34369175746062460822027645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45825567661416614429370193 34369175746062460822027645)
          ·
            refine ⟨12888440904773422808260367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34369175746062460822027645 12888440904773422808260367)
            ·
              refine ⟨19332661357160134212390551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888440904773422808260367 19332661357160134212390551)
              ·
                refine ⟨28998992035740201318585827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19332661357160134212390551 28998992035740201318585827)
                ·
                  refine ⟨43498488053610301977878741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28998992035740201318585827 43498488053610301977878741)
                  ·
                    refine ⟨1019495813756491452606533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43498488053610301977878741 1019495813756491452606533)
                    ·
                      rfl

theorem cell23_5956383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_5956383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956383 prefixEnd_5956383 := by exact prefixLift 5956383
  have htrace : WordTrace (prefixWord ++ tailWord_5956383) baseStart_5956383 baseEnd_5956383 := by
    simpa [prefixWord, tailWord_5956383, baseEnd_5956383] using wordTrace_append hprefix tailTrace_5956383
  have hstable : (prefixWord ++ tailWord_5956383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956383).length < 2 ^ (prefixWord ++ tailWord_5956383).sum := by decide
  have hdescent : baseEnd_5956383 < baseStart_5956383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956480 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 1, 5, 2]
def baseStart_5956480 : Nat := 118140960795 + 5956480 * 2 ^ 59
def prefixEnd_5956480 : Nat := 4983230072969 + 3 ^ 40 * 5956480 * 2
def baseEnd_5956480 : Nat := 3058537248892960478306653

theorem tailTrace_5956480 : CollatzResearch.WordTrace tailWord_5956480 prefixEnd_5956480 3058537248892960478306653 := by
  unfold tailWord_5956480
  simp only [CollatzResearch.WordTrace]
  refine ⟨108625336730348860319425447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144833782307131813759233929 108625336730348860319425447)
  ·
    refine ⟨162938005095523290479138171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108625336730348860319425447 162938005095523290479138171)
    ·
      refine ⟨244407007643284935718707257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162938005095523290479138171 244407007643284935718707257)
      ·
        refine ⟨183305255732463701789030443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244407007643284935718707257 183305255732463701789030443)
        ·
          refine ⟨274957883598695552683545665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183305255732463701789030443 274957883598695552683545665)
          ·
            refine ⟨206218412699021664512659249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274957883598695552683545665 206218412699021664512659249)
            ·
              refine ⟨154663809524266248384494437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206218412699021664512659249 154663809524266248384494437)
              ·
                refine ⟨28999464285799921572092707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154663809524266248384494437 28999464285799921572092707)
                ·
                  refine ⟨43499196428699882358139061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28999464285799921572092707 43499196428699882358139061)
                  ·
                    refine ⟨4078049665190613971075537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43499196428699882358139061 4078049665190613971075537)
                    ·
                      refine ⟨3058537248892960478306653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078049665190613971075537 3058537248892960478306653)
                      ·
                        rfl

theorem cell23_5956480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_5956480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956480 prefixEnd_5956480 := by exact prefixLift 5956480
  have htrace : WordTrace (prefixWord ++ tailWord_5956480) baseStart_5956480 baseEnd_5956480 := by
    simpa [prefixWord, tailWord_5956480, baseEnd_5956480] using wordTrace_append hprefix tailTrace_5956480
  have hstable : (prefixWord ++ tailWord_5956480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956480).length < 2 ^ (prefixWord ++ tailWord_5956480).sum := by decide
  have hdescent : baseEnd_5956480 < baseStart_5956480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956514 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5956514 : Nat := 118140960795 + 5956514 * 2 ^ 59
def prefixEnd_5956514 : Nat := 4983230072969 + 3 ^ 40 * 5956514 * 2
def baseEnd_5956514 : Nat := 3058554707235213345281497

theorem tailTrace_5956514 : CollatzResearch.WordTrace tailWord_5956514 prefixEnd_5956514 3058554707235213345281497 := by
  unfold tailWord_5956514
  simp only [CollatzResearch.WordTrace]
  refine ⟨54312978385643636111397149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144834609028383029630392397 54312978385643636111397149)
  ·
    refine ⟨20367366894616363541773931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54312978385643636111397149 20367366894616363541773931)
    ·
      refine ⟨30551050341924545312660897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20367366894616363541773931 30551050341924545312660897)
      ·
        refine ⟨22913287756443408984495673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30551050341924545312660897 22913287756443408984495673)
        ·
          refine ⟨17184965817332556738371755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22913287756443408984495673 17184965817332556738371755)
          ·
            refine ⟨25777448725998835107557633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17184965817332556738371755 25777448725998835107557633)
            ·
              refine ⟨19333086544499126330668225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25777448725998835107557633 19333086544499126330668225)
              ·
                refine ⟨14499814908374344748001169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19333086544499126330668225 14499814908374344748001169)
                ·
                  refine ⟨10874861181280758561000877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14499814908374344748001169 10874861181280758561000877)
                  ·
                    refine ⟨4078072942980284460375329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10874861181280758561000877 4078072942980284460375329)
                    ·
                      refine ⟨3058554707235213345281497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078072942980284460375329 3058554707235213345281497)
                      ·
                        rfl

theorem cell23_5956514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5956514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956514 prefixEnd_5956514 := by exact prefixLift 5956514
  have htrace : WordTrace (prefixWord ++ tailWord_5956514) baseStart_5956514 baseEnd_5956514 := by
    simpa [prefixWord, tailWord_5956514, baseEnd_5956514] using wordTrace_append hprefix tailTrace_5956514
  have hstable : (prefixWord ++ tailWord_5956514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956514).length < 2 ^ (prefixWord ++ tailWord_5956514).sum := by decide
  have hdescent : baseEnd_5956514 < baseStart_5956514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956537 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 2, 4]
def baseStart_5956537 : Nat := 118140960795 + 5956537 * 2 ^ 59
def prefixEnd_5956537 : Nat := 4983230072969 + 3 ^ 40 * 5956537 * 2
def baseEnd_5956537 : Nat := 1019522172430088918431297

theorem tailTrace_5956537 : CollatzResearch.WordTrace tailWord_5956537 prefixEnd_5956537 1019522172430088918431297 := by
  unfold tailWord_5956537
  simp only [CollatzResearch.WordTrace]
  refine ⟨217252752421491219373675865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144835168280994146249117243 217252752421491219373675865)
  ·
    refine ⟨162939564316118414530256899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217252752421491219373675865 162939564316118414530256899)
    ·
      refine ⟨244409346474177621795385349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162939564316118414530256899 244409346474177621795385349)
      ·
        refine ⟨45826752463908304086634753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244409346474177621795385349 45826752463908304086634753)
        ·
          refine ⟨34370064347931228064976065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45826752463908304086634753 34370064347931228064976065)
          ·
            refine ⟨25777548260948421048732049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34370064347931228064976065 25777548260948421048732049)
            ·
              refine ⟨19333161195711315786549037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25777548260948421048732049 19333161195711315786549037)
              ·
                refine ⟨7249935448391743419955889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19333161195711315786549037 7249935448391743419955889)
                ·
                  refine ⟨5437451586293807564966917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7249935448391743419955889 5437451586293807564966917)
                  ·
                    refine ⟨1019522172430088918431297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437451586293807564966917 1019522172430088918431297)
                    ·
                      rfl

theorem cell23_5956537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_5956537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956537 prefixEnd_5956537 := by exact prefixLift 5956537
  have htrace : WordTrace (prefixWord ++ tailWord_5956537) baseStart_5956537 baseEnd_5956537 := by
    simpa [prefixWord, tailWord_5956537, baseEnd_5956537] using wordTrace_append hprefix tailTrace_5956537
  have hstable : (prefixWord ++ tailWord_5956537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956537).length < 2 ^ (prefixWord ++ tailWord_5956537).sum := by decide
  have hdescent : baseEnd_5956537 < baseStart_5956537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956544 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 3, 2, 2]
def baseStart_5956544 : Nat := 118140960795 + 5956544 * 2 ^ 59
def prefixEnd_5956544 : Nat := 4983230072969 + 3 ^ 40 * 5956544 * 2
def baseEnd_5956544 : Nat := 3058570111654848227906359

theorem tailTrace_5956544 : CollatzResearch.WordTrace tailWord_5956544 prefixEnd_5956544 3058570111654848227906359 := by
  unfold tailWord_5956544
  simp only [CollatzResearch.WordTrace]
  refine ⟨108626503866232929784590343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144835338488310573046120457 108626503866232929784590343)
  ·
    refine ⟨162939755799349394676885515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108626503866232929784590343 162939755799349394676885515)
    ·
      refine ⟨244409633699024092015328273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162939755799349394676885515 244409633699024092015328273)
      ·
        refine ⟨183307225274268069011496205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244409633699024092015328273 183307225274268069011496205)
        ·
          refine ⟨68740209477850525879311077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183307225274268069011496205 68740209477850525879311077)
          ·
            refine ⟨12888789277096973602370827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68740209477850525879311077 12888789277096973602370827)
            ·
              refine ⟨19333183915645460403556241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888789277096973602370827 19333183915645460403556241)
              ·
                refine ⟨14499887936734095302667181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19333183915645460403556241 14499887936734095302667181)
                ·
                  refine ⟨5437457976275285738500193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14499887936734095302667181 5437457976275285738500193)
                  ·
                    refine ⟨4078093482206464303875145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437457976275285738500193 4078093482206464303875145)
                    ·
                      refine ⟨3058570111654848227906359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078093482206464303875145 3058570111654848227906359)
                      ·
                        rfl

theorem cell23_5956544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_5956544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956544 prefixEnd_5956544 := by exact prefixLift 5956544
  have htrace : WordTrace (prefixWord ++ tailWord_5956544) baseStart_5956544 baseEnd_5956544 := by
    simpa [prefixWord, tailWord_5956544, baseEnd_5956544] using wordTrace_append hprefix tailTrace_5956544
  have hstable : (prefixWord ++ tailWord_5956544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956544).length < 2 ^ (prefixWord ++ tailWord_5956544).sum := by decide
  have hdescent : baseEnd_5956544 < baseStart_5956544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956548 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5956548 : Nat := 118140960795 + 5956548 * 2 ^ 59
def prefixEnd_5956548 : Nat := 4983230072969 + 3 ^ 40 * 5956548 * 2
def baseEnd_5956548 : Nat := 3058572165577466212256341

theorem tailTrace_5956548 : CollatzResearch.WordTrace tailWord_5956548 prefixEnd_5956548 3058572165577466212256341 := by
  unfold tailWord_5956548
  simp only [CollatzResearch.WordTrace]
  refine ⟨108626576812225684126163149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144835435749634245501550865 108626576812225684126163149)
  ·
    refine ⟨40734966304584631547311181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108626576812225684126163149 40734966304584631547311181)
    ·
      refine ⟨15275612364219236830241693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40734966304584631547311181 15275612364219236830241693)
      ·
        refine ⟨5728354636582213811340635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15275612364219236830241693 5728354636582213811340635)
        ·
          refine ⟨8592531954873320717010953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728354636582213811340635 8592531954873320717010953)
          ·
            refine ⟨6444398966154990537758215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8592531954873320717010953 6444398966154990537758215)
            ·
              refine ⟨9666598449232485806637323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6444398966154990537758215 9666598449232485806637323)
              ·
                refine ⟨14499897673848728709955985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9666598449232485806637323 14499897673848728709955985)
                ·
                  refine ⟨10874923255386546532466989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14499897673848728709955985 10874923255386546532466989)
                  ·
                    refine ⟨4078096220769954949675121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10874923255386546532466989 4078096220769954949675121)
                    ·
                      refine ⟨3058572165577466212256341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078096220769954949675121 3058572165577466212256341)
                      ·
                        rfl

theorem cell23_5956548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5956548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956548 prefixEnd_5956548 := by exact prefixLift 5956548
  have htrace : WordTrace (prefixWord ++ tailWord_5956548) baseStart_5956548 baseEnd_5956548 := by
    simpa [prefixWord, tailWord_5956548, baseEnd_5956548] using wordTrace_append hprefix tailTrace_5956548
  have hstable : (prefixWord ++ tailWord_5956548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956548).length < 2 ^ (prefixWord ++ tailWord_5956548).sum := by decide
  have hdescent : baseEnd_5956548 < baseStart_5956548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956561 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 1, 2, 2]
def baseStart_5956561 : Nat := 118140960795 + 5956561 * 2 ^ 59
def prefixEnd_5956561 : Nat := 4983230072969 + 3 ^ 40 * 5956561 * 2
def baseEnd_5956561 : Nat := 3058578840825974661393781

theorem tailTrace_5956561 : CollatzResearch.WordTrace tailWord_5956561 prefixEnd_5956561 3058578840825974661393781 := by
  unfold tailWord_5956561
  simp only [CollatzResearch.WordTrace]
  refine ⟨217253627773404271472549537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144835751848936180981699691 217253627773404271472549537)
  ·
    refine ⟨162940220830053203604412153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217253627773404271472549537 162940220830053203604412153)
    ·
      refine ⟨122205165622539902703309115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162940220830053203604412153 122205165622539902703309115)
      ·
        refine ⟨183307748433809854054963673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122205165622539902703309115 183307748433809854054963673)
        ·
          refine ⟨137480811325357390541222755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183307748433809854054963673 137480811325357390541222755)
          ·
            refine ⟨206221216988036085811834133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137480811325357390541222755 206221216988036085811834133)
            ·
              refine ⟨9666619546314191522429725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206221216988036085811834133 9666619546314191522429725)
              ·
                refine ⟨3624982329867821820911147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9666619546314191522429725 3624982329867821820911147)
                ·
                  refine ⟨5437473494801732731366721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624982329867821820911147 5437473494801732731366721)
                  ·
                    refine ⟨4078105121101299548525041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437473494801732731366721 4078105121101299548525041)
                    ·
                      refine ⟨3058578840825974661393781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078105121101299548525041 3058578840825974661393781)
                      ·
                        rfl

theorem cell23_5956561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_5956561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956561 prefixEnd_5956561 := by exact prefixLift 5956561
  have htrace : WordTrace (prefixWord ++ tailWord_5956561) baseStart_5956561 baseEnd_5956561 := by
    simpa [prefixWord, tailWord_5956561, baseEnd_5956561] using wordTrace_append hprefix tailTrace_5956561
  have hstable : (prefixWord ++ tailWord_5956561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956561).length < 2 ^ (prefixWord ++ tailWord_5956561).sum := by decide
  have hdescent : baseEnd_5956561 < baseStart_5956561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956564 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_5956564 : Nat := 118140960795 + 5956564 * 2 ^ 59
def prefixEnd_5956564 : Nat := 4983230072969 + 3 ^ 40 * 5956564 * 2
def baseEnd_5956564 : Nat := 3058580381267938149656267

theorem tailTrace_5956564 : CollatzResearch.WordTrace tailWord_5956564 prefixEnd_5956564 3058580381267938149656267 := by
  unfold tailWord_5956564
  simp only [CollatzResearch.WordTrace]
  refine ⟨108626868596196701492454373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144835824794928935323272497 108626868596196701492454373)
  ·
    refine ⟨20367537861786881529835195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108626868596196701492454373 20367537861786881529835195)
    ·
      refine ⟨30551306792680322294752793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20367537861786881529835195 30551306792680322294752793)
      ·
        refine ⟨22913480094510241721064595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30551306792680322294752793 22913480094510241721064595)
        ·
          refine ⟨34370220141765362581596893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22913480094510241721064595 34370220141765362581596893)
          ·
            refine ⟨12888832553162010968098835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34370220141765362581596893 12888832553162010968098835)
            ·
              refine ⟨19333248829743016452148253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888832553162010968098835 19333248829743016452148253)
              ·
                refine ⟨7249968311153631169555595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19333248829743016452148253 7249968311153631169555595)
                ·
                  refine ⟨10874952466730446754333393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7249968311153631169555595 10874952466730446754333393)
                  ·
                    refine ⟨8156214350047835065750045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10874952466730446754333393 8156214350047835065750045)
                    ·
                      refine ⟨3058580381267938149656267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156214350047835065750045 3058580381267938149656267)
                      ·
                        rfl

theorem cell23_5956564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_5956564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956564 prefixEnd_5956564 := by exact prefixLift 5956564
  have htrace : WordTrace (prefixWord ++ tailWord_5956564) baseStart_5956564 baseEnd_5956564 := by
    simpa [prefixWord, tailWord_5956564, baseEnd_5956564] using wordTrace_append hprefix tailTrace_5956564
  have hstable : (prefixWord ++ tailWord_5956564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956564).length < 2 ^ (prefixWord ++ tailWord_5956564).sum := by decide
  have hdescent : baseEnd_5956564 < baseStart_5956564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956578 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5956578 : Nat := 118140960795 + 5956578 * 2 ^ 59
def prefixEnd_5956578 : Nat := 4983230072969 + 3 ^ 40 * 5956578 * 2
def baseEnd_5956578 : Nat := 3058587569997101094881203

theorem tailTrace_5956578 : CollatzResearch.WordTrace tailWord_5956578 prefixEnd_5956578 3058587569997101094881203 := by
  unfold tailWord_5956578
  simp only [CollatzResearch.WordTrace]
  refine ⟨54313561953585670843979597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144836165209561788917278925 54313561953585670843979597)
  ·
    refine ⟨20367585732594626566492349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54313561953585670843979597 20367585732594626566492349)
    ·
      refine ⟨7637844649722984962434631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20367585732594626566492349 7637844649722984962434631)
      ·
        refine ⟨11456766974584477443651947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7637844649722984962434631 11456766974584477443651947)
        ·
          refine ⟨17185150461876716165477921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11456766974584477443651947 17185150461876716165477921)
          ·
            refine ⟨12888862846407537124108441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17185150461876716165477921 12888862846407537124108441)
            ·
              refine ⟨9666647134805652843081331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12888862846407537124108441 9666647134805652843081331)
              ·
                refine ⟨14499970702208479264621997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9666647134805652843081331 14499970702208479264621997)
                ·
                  refine ⟨5437489013328179724233249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14499970702208479264621997 5437489013328179724233249)
                  ·
                    refine ⟨4078116759996134793174937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437489013328179724233249 4078116759996134793174937)
                    ·
                      refine ⟨3058587569997101094881203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078116759996134793174937 3058587569997101094881203)
                      ·
                        rfl

theorem cell23_5956578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5956578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956578 prefixEnd_5956578 := by exact prefixLift 5956578
  have htrace : WordTrace (prefixWord ++ tailWord_5956578) baseStart_5956578 baseEnd_5956578 := by
    simpa [prefixWord, tailWord_5956578, baseEnd_5956578] using wordTrace_append hprefix tailTrace_5956578
  have hstable : (prefixWord ++ tailWord_5956578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956578).length < 2 ^ (prefixWord ++ tailWord_5956578).sum := by decide
  have hdescent : baseEnd_5956578 < baseStart_5956578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956604 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_5956604 : Nat := 118140960795 + 5956604 * 2 ^ 59
def prefixEnd_5956604 : Nat := 4983230072969 + 3 ^ 40 * 5956604 * 2
def baseEnd_5956604 : Nat := 3058600920494117993156083

theorem tailTrace_5956604 : CollatzResearch.WordTrace tailWord_5956604 prefixEnd_5956604 3058600920494117993156083 := by
  unfold tailWord_5956604
  simp only [CollatzResearch.WordTrace]
  refine ⟨108627598056124244908182433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144836797408165659877576577 108627598056124244908182433)
  ·
    refine ⟨81470698542093183681136825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108627598056124244908182433 81470698542093183681136825)
    ·
      refine ⟨61103023906569887760852619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81470698542093183681136825 61103023906569887760852619)
      ·
        refine ⟨91654535859854831641278929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61103023906569887760852619 91654535859854831641278929)
        ·
          refine ⟨68740901894891123730959197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91654535859854831641278929 68740901894891123730959197)
          ·
            refine ⟨25777838210584171399109699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68740901894891123730959197 25777838210584171399109699)
            ·
              refine ⟨38666757315876257098664549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25777838210584171399109699 38666757315876257098664549)
              ·
                refine ⟨7250016996726798205999603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38666757315876257098664549 7250016996726798205999603)
                ·
                  refine ⟨10875025495090197308999405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250016996726798205999603 10875025495090197308999405)
                  ·
                    refine ⟨4078134560658823990874777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10875025495090197308999405 4078134560658823990874777)
                    ·
                      refine ⟨3058600920494117993156083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078134560658823990874777 3058600920494117993156083)
                      ·
                        rfl

theorem cell23_5956604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_5956604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956604 prefixEnd_5956604 := by exact prefixLift 5956604
  have htrace : WordTrace (prefixWord ++ tailWord_5956604) baseStart_5956604 baseEnd_5956604 := by
    simpa [prefixWord, tailWord_5956604, baseEnd_5956604] using wordTrace_append hprefix tailTrace_5956604
  have hstable : (prefixWord ++ tailWord_5956604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956604).length < 2 ^ (prefixWord ++ tailWord_5956604).sum := by decide
  have hdescent : baseEnd_5956604 < baseStart_5956604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956617 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 1, 4, 2]
def baseStart_5956617 : Nat := 118140960795 + 5956617 * 2 ^ 59
def prefixEnd_5956617 : Nat := 4983230072969 + 3 ^ 40 * 5956617 * 2
def baseEnd_5956617 : Nat := 3058607595742626442293523

theorem tailTrace_5956617 : CollatzResearch.WordTrace tailWord_5956617 prefixEnd_5956617 3058607595742626442293523 := by
  unfold tailWord_5956617
  simp only [CollatzResearch.WordTrace]
  refine ⟨217255670261201393036588105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144837113507467595357725403 217255670261201393036588105)
  ·
    refine ⟨162941752695901044777441079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217255670261201393036588105 162941752695901044777441079)
    ·
      refine ⟨244412629043851567166161619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162941752695901044777441079 244412629043851567166161619)
      ·
        refine ⟨366618943565777350749242429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244412629043851567166161619 366618943565777350749242429)
        ·
          refine ⟨137482103837166506530965911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366618943565777350749242429 137482103837166506530965911)
          ·
            refine ⟨206223155755749759796448867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137482103837166506530965911 206223155755749759796448867)
            ·
              refine ⟨309334733633624639694673301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206223155755749759796448867 309334733633624639694673301)
              ·
                refine ⟨14500065639076154985687811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 309334733633624639694673301 14500065639076154985687811)
                ·
                  refine ⟨21750098458614232478531717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14500065639076154985687811 21750098458614232478531717)
                  ·
                    refine ⟨4078143460990168589724697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21750098458614232478531717 4078143460990168589724697)
                    ·
                      refine ⟨3058607595742626442293523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078143460990168589724697 3058607595742626442293523)
                      ·
                        rfl

theorem cell23_5956617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 4, 2].length) (baseStart_5956617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956617 prefixEnd_5956617 := by exact prefixLift 5956617
  have htrace : WordTrace (prefixWord ++ tailWord_5956617) baseStart_5956617 baseEnd_5956617 := by
    simpa [prefixWord, tailWord_5956617, baseEnd_5956617] using wordTrace_append hprefix tailTrace_5956617
  have hstable : (prefixWord ++ tailWord_5956617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956617).length < 2 ^ (prefixWord ++ tailWord_5956617).sum := by decide
  have hdescent : baseEnd_5956617 < baseStart_5956617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956620 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_5956620 : Nat := 118140960795 + 5956620 * 2 ^ 59
def prefixEnd_5956620 : Nat := 4983230072969 + 3 ^ 40 * 5956620 * 2
def baseEnd_5956620 : Nat := 3058609136184589930556009

theorem tailTrace_5956620 : CollatzResearch.WordTrace tailWord_5956620 prefixEnd_5956620 3058609136184589930556009 := by
  unfold tailWord_5956620
  simp only [CollatzResearch.WordTrace]
  refine ⟨108627889840095262274473657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144837186453460349699298209 108627889840095262274473657)
  ·
    refine ⟨81470917380071446705855243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108627889840095262274473657 81470917380071446705855243)
    ·
      refine ⟨122206376070107170058782865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81470917380071446705855243 122206376070107170058782865)
      ·
        refine ⟨91654782052580377544087149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122206376070107170058782865 91654782052580377544087149)
        ·
          refine ⟨34370543269717641579032681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91654782052580377544087149 34370543269717641579032681)
          ·
            refine ⟨25777907452288231184274511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34370543269717641579032681 25777907452288231184274511)
            ·
              refine ⟨38666861178432346776411767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25777907452288231184274511 38666861178432346776411767)
              ·
                refine ⟨58000291767648520164617651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38666861178432346776411767 58000291767648520164617651)
                ·
                  refine ⟨87000437651472780246926477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58000291767648520164617651 87000437651472780246926477)
                  ·
                    refine ⟨32625164119302292592597429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87000437651472780246926477 32625164119302292592597429)
                    ·
                      refine ⟨3058609136184589930556009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32625164119302292592597429 3058609136184589930556009)
                      ·
                        rfl

theorem cell23_5956620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_5956620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956620 prefixEnd_5956620 := by exact prefixLift 5956620
  have htrace : WordTrace (prefixWord ++ tailWord_5956620) baseStart_5956620 baseEnd_5956620 := by
    simpa [prefixWord, tailWord_5956620, baseEnd_5956620] using wordTrace_append hprefix tailTrace_5956620
  have hstable : (prefixWord ++ tailWord_5956620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956620).length < 2 ^ (prefixWord ++ tailWord_5956620).sum := by decide
  have hdescent : baseEnd_5956620 < baseStart_5956620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956634 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2]
def baseStart_5956634 : Nat := 118140960795 + 5956634 * 2 ^ 59
def prefixEnd_5956634 : Nat := 4983230072969 + 3 ^ 40 * 5956634 * 2
def baseEnd_5956634 : Nat := 3058616324913752875780945

theorem tailTrace_5956634 : CollatzResearch.WordTrace tailWord_5956634 prefixEnd_5956634 3058616324913752875780945 := by
  unfold tailWord_5956634
  simp only [CollatzResearch.WordTrace]
  refine ⟨54314072575534951234989239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144837526868093203293304637 54314072575534951234989239)
  ·
    refine ⟨81471108863302426852483859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54314072575534951234989239 81471108863302426852483859)
    ·
      refine ⟨122206663294953640278725789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81471108863302426852483859 122206663294953640278725789)
      ·
        refine ⟨45827498735607615104522171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122206663294953640278725789 45827498735607615104522171)
        ·
          refine ⟨68741248103411422656783257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45827498735607615104522171 68741248103411422656783257)
          ·
            refine ⟨51555936077558566992587443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68741248103411422656783257 51555936077558566992587443)
            ·
              refine ⟨77333904116337850488881165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51555936077558566992587443 77333904116337850488881165)
              ·
                refine ⟨29000214043626693933330437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77333904116337850488881165 29000214043626693933330437)
                ·
                  refine ⟨5437540133180005112499457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29000214043626693933330437 5437540133180005112499457)
                  ·
                    refine ⟨4078155099885003834374593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437540133180005112499457 4078155099885003834374593)
                    ·
                      refine ⟨3058616324913752875780945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078155099885003834374593 3058616324913752875780945)
                      ·
                        rfl

theorem cell23_5956634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_5956634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956634 prefixEnd_5956634 := by exact prefixLift 5956634
  have htrace : WordTrace (prefixWord ++ tailWord_5956634) baseStart_5956634 baseEnd_5956634 := by
    simpa [prefixWord, tailWord_5956634, baseEnd_5956634] using wordTrace_append hprefix tailTrace_5956634
  have hstable : (prefixWord ++ tailWord_5956634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956634).length < 2 ^ (prefixWord ++ tailWord_5956634).sum := by decide
  have hdescent : baseEnd_5956634 < baseStart_5956634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956680 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_5956680 : Nat := 118140960795 + 5956680 * 2 ^ 59
def prefixEnd_5956680 : Nat := 4983230072969 + 3 ^ 40 * 5956680 * 2
def baseEnd_5956680 : Nat := 3058639945023859695805733

theorem tailTrace_5956680 : CollatzResearch.WordTrace tailWord_5956680 prefixEnd_5956680 3058639945023859695805733 := by
  unfold tailWord_5956680
  simp only [CollatzResearch.WordTrace]
  refine ⟨108628984029986577398065747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144838645373315436530754329 108628984029986577398065747)
  ·
    refine ⟨162943476044979866097098621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108628984029986577398065747 162943476044979866097098621)
    ·
      refine ⟨61103803516867449786411983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162943476044979866097098621 61103803516867449786411983)
      ·
        refine ⟨91655705275301174679617975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61103803516867449786411983 91655705275301174679617975)
        ·
          refine ⟨137483557912951762019426963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91655705275301174679617975 137483557912951762019426963)
          ·
            refine ⟨206225336869427643029140445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137483557912951762019426963 206225336869427643029140445)
            ·
              refine ⟨77334501326035366135927667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206225336869427643029140445 77334501326035366135927667)
              ·
                refine ⟨116001751989053049203891501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77334501326035366135927667 116001751989053049203891501)
                ·
                  refine ⟨43500656995894893451459313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116001751989053049203891501 43500656995894893451459313)
                  ·
                    refine ⟨32625492746921170088594485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43500656995894893451459313 32625492746921170088594485)
                    ·
                      refine ⟨3058639945023859695805733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32625492746921170088594485 3058639945023859695805733)
                      ·
                        rfl

theorem cell23_5956680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_5956680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956680 prefixEnd_5956680 := by exact prefixLift 5956680
  have htrace : WordTrace (prefixWord ++ tailWord_5956680) baseStart_5956680 baseEnd_5956680 := by
    simpa [prefixWord, tailWord_5956680, baseEnd_5956680] using wordTrace_append hprefix tailTrace_5956680
  have hstable : (prefixWord ++ tailWord_5956680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956680).length < 2 ^ (prefixWord ++ tailWord_5956680).sum := by decide
  have hdescent : baseEnd_5956680 < baseStart_5956680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956701 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5956701 : Nat := 118140960795 + 5956701 * 2 ^ 59
def prefixEnd_5956701 : Nat := 4983230072969 + 3 ^ 40 * 5956701 * 2
def baseEnd_5956701 : Nat := 3058650728117604113643137

theorem tailTrace_5956701 : CollatzResearch.WordTrace tailWord_5956701 prefixEnd_5956701 3058650728117604113643137 := by
  unfold tailWord_5956701
  simp only [CollatzResearch.WordTrace]
  refine ⟨217258733992897075382645957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144839155995264716921763971 217258733992897075382645957)
  ·
    refine ⟨40736012623668201634246117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217258733992897075382645957 40736012623668201634246117)
    ·
      refine ⟨7638002366937787806421147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40736012623668201634246117 7638002366937787806421147)
      ·
        refine ⟨11457003550406681709631721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7638002366937787806421147 11457003550406681709631721)
        ·
          refine ⟨8592752662805011282223791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11457003550406681709631721 8592752662805011282223791)
          ·
            refine ⟨12889128994207516923335687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592752662805011282223791 12889128994207516923335687)
            ·
              refine ⟨19333693491311275385003531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12889128994207516923335687 19333693491311275385003531)
              ·
                refine ⟨29000540236966913077505297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19333693491311275385003531 29000540236966913077505297)
                ·
                  refine ⟨21750405177725184808128973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29000540236966913077505297 21750405177725184808128973)
                  ·
                    refine ⟨8156401941646944303048365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21750405177725184808128973 8156401941646944303048365)
                    ·
                      refine ⟨3058650728117604113643137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156401941646944303048365 3058650728117604113643137)
                      ·
                        rfl

theorem cell23_5956701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5956701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956701 prefixEnd_5956701 := by exact prefixLift 5956701
  have htrace : WordTrace (prefixWord ++ tailWord_5956701) baseStart_5956701 baseEnd_5956701 := by
    simpa [prefixWord, tailWord_5956701, baseEnd_5956701] using wordTrace_append hprefix tailTrace_5956701
  have hstable : (prefixWord ++ tailWord_5956701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956701).length < 2 ^ (prefixWord ++ tailWord_5956701).sum := by decide
  have hdescent : baseEnd_5956701 < baseStart_5956701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956727 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_5956727 : Nat := 118140960795 + 5956727 * 2 ^ 59
def prefixEnd_5956727 : Nat := 4983230072969 + 3 ^ 40 * 5956727 * 2
def baseEnd_5956727 : Nat := 3058664078614621011918017

theorem tailTrace_5956727 : CollatzResearch.WordTrace tailWord_5956727 prefixEnd_5956727 3058664078614621011918017 := by
  unfold tailWord_5956727
  simp only [CollatzResearch.WordTrace]
  refine ⟨217259682290802881823092435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144839788193868587882061623 217259682290802881823092435)
  ·
    refine ⟨325889523436204322734638653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217259682290802881823092435 325889523436204322734638653)
    ·
      refine ⟨122208571288576621025489495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325889523436204322734638653 122208571288576621025489495)
      ·
        refine ⟨183312856932864931538234243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122208571288576621025489495 183312856932864931538234243)
        ·
          refine ⟨274969285399297397307351365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183312856932864931538234243 274969285399297397307351365)
          ·
            refine ⟨51556741012368261995128381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274969285399297397307351365 51556741012368261995128381)
            ·
              refine ⟨19333777879638098248173143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51556741012368261995128381 19333777879638098248173143)
              ·
                refine ⟨29000666819457147372259715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19333777879638098248173143 29000666819457147372259715)
                ·
                  refine ⟨43501000229185721058389573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29000666819457147372259715 43501000229185721058389573)
                  ·
                    refine ⟨8156437542972322698448045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43501000229185721058389573 8156437542972322698448045)
                    ·
                      refine ⟨3058664078614621011918017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156437542972322698448045 3058664078614621011918017)
                      ·
                        rfl

theorem cell23_5956727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_5956727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956727 prefixEnd_5956727 := by exact prefixLift 5956727
  have htrace : WordTrace (prefixWord ++ tailWord_5956727) baseStart_5956727 baseEnd_5956727 := by
    simpa [prefixWord, tailWord_5956727, baseEnd_5956727] using wordTrace_append hprefix tailTrace_5956727
  have hstable : (prefixWord ++ tailWord_5956727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956727).length < 2 ^ (prefixWord ++ tailWord_5956727).sum := by decide
  have hdescent : baseEnd_5956727 < baseStart_5956727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956737 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5956737 : Nat := 118140960795 + 5956737 * 2 ^ 59
def prefixEnd_5956737 : Nat := 4983230072969 + 3 ^ 40 * 5956737 * 2
def baseEnd_5956737 : Nat := 3058669213421165972792971

theorem tailTrace_5956737 : CollatzResearch.WordTrace tailWord_5956737 prefixEnd_5956737 3058669213421165972792971 := by
  unfold tailWord_5956737
  simp only [CollatzResearch.WordTrace]
  refine ⟨217260047020766653530956465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144840031347177769020637643 217260047020766653530956465)
  ·
    refine ⟨162945035265574990148217349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217260047020766653530956465 162945035265574990148217349)
    ·
      refine ⟨30552194112295310652790753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162945035265574990148217349 30552194112295310652790753)
      ·
        refine ⟨22914145584221482989593065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30552194112295310652790753 22914145584221482989593065)
        ·
          refine ⟨17185609188166112242194799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22914145584221482989593065 17185609188166112242194799)
          ·
            refine ⟨25778413782249168363292199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17185609188166112242194799 25778413782249168363292199)
            ·
              refine ⟨38667620673373752544938299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25778413782249168363292199 38667620673373752544938299)
              ·
                refine ⟨58001431010060628817407449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38667620673373752544938299 58001431010060628817407449)
                ·
                  refine ⟨43501073257545471613055587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58001431010060628817407449 43501073257545471613055587)
                  ·
                    refine ⟨65251609886318207419583381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43501073257545471613055587 65251609886318207419583381)
                    ·
                      refine ⟨3058669213421165972792971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65251609886318207419583381 3058669213421165972792971)
                      ·
                        rfl

theorem cell23_5956737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5956737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956737 prefixEnd_5956737 := by exact prefixLift 5956737
  have htrace : WordTrace (prefixWord ++ tailWord_5956737) baseStart_5956737 baseEnd_5956737 := by
    simpa [prefixWord, tailWord_5956737, baseEnd_5956737] using wordTrace_append hprefix tailTrace_5956737
  have hstable : (prefixWord ++ tailWord_5956737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956737).length < 2 ^ (prefixWord ++ tailWord_5956737).sum := by decide
  have hdescent : baseEnd_5956737 < baseStart_5956737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956802 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5956802 : Nat := 118140960795 + 5956802 * 2 ^ 59
def prefixEnd_5956802 : Nat := 4983230072969 + 3 ^ 40 * 5956802 * 2
def baseEnd_5956802 : Nat := 1019567529887902739493391

theorem tailTrace_5956802 : CollatzResearch.WordTrace tailWord_5956802 prefixEnd_5956802 1019567529887902739493391 := by
  unfold tailWord_5956802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54315604441382792408018165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144841611843687446421381773 54315604441382792408018165)
  ·
    refine ⟨5092087916379636788251703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54315604441382792408018165 5092087916379636788251703)
    ·
      refine ⟨7638131874569455182377555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5092087916379636788251703 7638131874569455182377555)
      ·
        refine ⟨11457197811854182773566333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7638131874569455182377555 11457197811854182773566333)
        ·
          refine ⟨4296449179445318540087375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11457197811854182773566333 4296449179445318540087375)
          ·
            refine ⟨6444673769167977810131063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296449179445318540087375 6444673769167977810131063)
            ·
              refine ⟨9667010653751966715196595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6444673769167977810131063 9667010653751966715196595)
              ·
                refine ⟨14500515980627950072794893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9667010653751966715196595 14500515980627950072794893)
                ·
                  refine ⟨5437693492735481277298085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14500515980627950072794893 5437693492735481277298085)
                  ·
                    refine ⟨1019567529887902739493391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437693492735481277298085 1019567529887902739493391)
                    ·
                      rfl

theorem cell23_5956802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5956802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956802 prefixEnd_5956802 := by exact prefixLift 5956802
  have htrace : WordTrace (prefixWord ++ tailWord_5956802) baseStart_5956802 baseEnd_5956802 := by
    simpa [prefixWord, tailWord_5956802, baseEnd_5956802] using wordTrace_append hprefix tailTrace_5956802
  have hstable : (prefixWord ++ tailWord_5956802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956802).length < 2 ^ (prefixWord ++ tailWord_5956802).sum := by decide
  have hdescent : baseEnd_5956802 < baseStart_5956802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956817 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_5956817 : Nat := 118140960795 + 5956817 * 2 ^ 59
def prefixEnd_5956817 : Nat := 4983230072969 + 3 ^ 40 * 5956817 * 2
def baseEnd_5956817 : Nat := 3058710291873525659792603

theorem tailTrace_5956817 : CollatzResearch.WordTrace tailWord_5956817 prefixEnd_5956817 3058710291873525659792603 := by
  unfold tailWord_5956817
  simp only [CollatzResearch.WordTrace]
  refine ⟨217262964860476827193868705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144841976573651218129245803 217262964860476827193868705)
  ·
    refine ⟨162947223645357620395401529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217262964860476827193868705 162947223645357620395401529)
    ·
      refine ⟨122210417734018215296551147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162947223645357620395401529 122210417734018215296551147)
      ·
        refine ⟨183315626601027322944826721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122210417734018215296551147 183315626601027322944826721)
        ·
          refine ⟨137486719950770492208620041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183315626601027322944826721 137486719950770492208620041)
          ·
            refine ⟨103115039963077869156465031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137486719950770492208620041 103115039963077869156465031)
            ·
              refine ⟨154672559944616803734697547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103115039963077869156465031 154672559944616803734697547)
              ·
                refine ⟨232008839916925205602046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154672559944616803734697547 232008839916925205602046321)
                ·
                  refine ⟨174006629937693904201534741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232008839916925205602046321 174006629937693904201534741)
                  ·
                    refine ⟨8156560778329401759446941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174006629937693904201534741 8156560778329401759446941)
                    ·
                      refine ⟨3058710291873525659792603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156560778329401759446941 3058710291873525659792603)
                      ·
                        rfl

theorem cell23_5956817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_5956817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956817 prefixEnd_5956817 := by exact prefixLift 5956817
  have htrace : WordTrace (prefixWord ++ tailWord_5956817) baseStart_5956817 baseEnd_5956817 := by
    simpa [prefixWord, tailWord_5956817, baseEnd_5956817] using wordTrace_append hprefix tailTrace_5956817
  have hstable : (prefixWord ++ tailWord_5956817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956817).length < 2 ^ (prefixWord ++ tailWord_5956817).sum := by decide
  have hdescent : baseEnd_5956817 < baseStart_5956817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956831 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 3, 2, 2]
def baseStart_5956831 : Nat := 118140960795 + 5956831 * 2 ^ 59
def prefixEnd_5956831 : Nat := 4983230072969 + 3 ^ 40 * 5956831 * 2
def baseEnd_5956831 : Nat := 3058717480602688605017539

theorem tailTrace_5956831 : CollatzResearch.WordTrace tailWord_5956831 prefixEnd_5956831 3058717480602688605017539 := by
  unfold tailWord_5956831
  simp only [CollatzResearch.WordTrace]
  refine ⟨217263475482426107584878347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144842316988284071723252231 217263475482426107584878347)
  ·
    refine ⟨325895213223639161377317521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217263475482426107584878347 325895213223639161377317521)
    ·
      refine ⟨244421409917729371032988141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325895213223639161377317521 244421409917729371032988141)
      ·
        refine ⟨91658028719148514137370553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244421409917729371032988141 91658028719148514137370553)
        ·
          refine ⟨68743521539361385603027915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91658028719148514137370553 68743521539361385603027915)
          ·
            refine ⟨103115282309042078404541873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68743521539361385603027915 103115282309042078404541873)
            ·
              refine ⟨77336461731781558803406405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103115282309042078404541873 77336461731781558803406405)
              ·
                refine ⟨14500586574709042275638701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77336461731781558803406405 14500586574709042275638701)
                ·
                  refine ⟨5437719965515890853364513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14500586574709042275638701 5437719965515890853364513)
                  ·
                    refine ⟨4078289974136918140023385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437719965515890853364513 4078289974136918140023385)
                    ·
                      refine ⟨3058717480602688605017539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078289974136918140023385 3058717480602688605017539)
                      ·
                        rfl

theorem cell23_5956831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_5956831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956831 prefixEnd_5956831 := by exact prefixLift 5956831
  have htrace : WordTrace (prefixWord ++ tailWord_5956831) baseStart_5956831 baseEnd_5956831 := by
    simpa [prefixWord, tailWord_5956831, baseEnd_5956831] using wordTrace_append hprefix tailTrace_5956831
  have hstable : (prefixWord ++ tailWord_5956831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956831).length < 2 ^ (prefixWord ++ tailWord_5956831).sum := by decide
  have hdescent : baseEnd_5956831 < baseStart_5956831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956844 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_5956844 : Nat := 118140960795 + 5956844 * 2 ^ 59
def prefixEnd_5956844 : Nat := 4983230072969 + 3 ^ 40 * 5956844 * 2
def baseEnd_5956844 : Nat := 3058724155851197054154979

theorem tailTrace_5956844 : CollatzResearch.WordTrace tailWord_5956844 prefixEnd_5956844 3058724155851197054154979 := by
  unfold tailWord_5956844
  simp only [CollatzResearch.WordTrace]
  refine ⟨108631974815689505402550793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144842633087586007203401057 108631974815689505402550793)
  ·
    refine ⟨81473981111767129051913095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108631974815689505402550793 81473981111767129051913095)
    ·
      refine ⟨122210971667650693577869643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81473981111767129051913095 122210971667650693577869643)
      ·
        refine ⟨183316457501476040366804465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122210971667650693577869643 183316457501476040366804465)
        ·
          refine ⟨137487343126107030275103349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183316457501476040366804465 137487343126107030275103349)
          ·
            refine ⟨12889438418072534088290939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137487343126107030275103349 12889438418072534088290939)
            ·
              refine ⟨19334157627108801132436409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12889438418072534088290939 19334157627108801132436409)
              ·
                refine ⟨14500618220331600849327307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19334157627108801132436409 14500618220331600849327307)
                ·
                  refine ⟨21750927330497401273990961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14500618220331600849327307 21750927330497401273990961)
                  ·
                    refine ⟨16313195497873050955493221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21750927330497401273990961 16313195497873050955493221)
                    ·
                      refine ⟨3058724155851197054154979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16313195497873050955493221 3058724155851197054154979)
                      ·
                        rfl

theorem cell23_5956844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_5956844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956844 prefixEnd_5956844 := by exact prefixLift 5956844
  have htrace : WordTrace (prefixWord ++ tailWord_5956844) baseStart_5956844 baseEnd_5956844 := by
    simpa [prefixWord, tailWord_5956844, baseEnd_5956844] using wordTrace_append hprefix tailTrace_5956844
  have hstable : (prefixWord ++ tailWord_5956844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956844).length < 2 ^ (prefixWord ++ tailWord_5956844).sum := by decide
  have hdescent : baseEnd_5956844 < baseStart_5956844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956865 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_5956865 : Nat := 118140960795 + 5956865 * 2 ^ 59
def prefixEnd_5956865 : Nat := 4983230072969 + 3 ^ 40 * 5956865 * 2
def baseEnd_5956865 : Nat := 3058734938944941471992383

theorem tailTrace_5956865 : CollatzResearch.WordTrace tailWord_5956865 prefixEnd_5956865 3058734938944941471992383 := by
  unfold tailWord_5956865
  simp only [CollatzResearch.WordTrace]
  refine ⟨217264715564302931391616049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144843143709535287594410699 217264715564302931391616049)
  ·
    refine ⟨162948536673227198543712037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217264715564302931391616049 162948536673227198543712037)
    ·
      refine ⟨30552850626230099726946007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162948536673227198543712037 30552850626230099726946007)
      ·
        refine ⟨45829275939345149590419011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30552850626230099726946007 45829275939345149590419011)
        ·
          refine ⟨68743913909017724385628517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45829275939345149590419011 68743913909017724385628517)
          ·
            refine ⟨12889483857940823322305347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68743913909017724385628517 12889483857940823322305347)
            ·
              refine ⟨19334225786911234983458021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12889483857940823322305347 19334225786911234983458021)
              ·
                refine ⟨3625167335045856559398379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19334225786911234983458021 3625167335045856559398379)
                ·
                  refine ⟨5437751002568784839097569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625167335045856559398379 5437751002568784839097569)
                  ·
                    refine ⟨4078313251926588629323177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437751002568784839097569 4078313251926588629323177)
                    ·
                      refine ⟨3058734938944941471992383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078313251926588629323177 3058734938944941471992383)
                      ·
                        rfl

theorem cell23_5956865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_5956865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956865 prefixEnd_5956865 := by exact prefixLift 5956865
  have htrace : WordTrace (prefixWord ++ tailWord_5956865) baseStart_5956865 baseEnd_5956865 := by
    simpa [prefixWord, tailWord_5956865, baseEnd_5956865] using wordTrace_append hprefix tailTrace_5956865
  have hstable : (prefixWord ++ tailWord_5956865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956865).length < 2 ^ (prefixWord ++ tailWord_5956865).sum := by decide
  have hdescent : baseEnd_5956865 < baseStart_5956865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956867 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 2, 7]
def baseStart_5956867 : Nat := 118140960795 + 5956867 * 2 ^ 59
def prefixEnd_5956867 : Nat := 4983230072969 + 3 ^ 40 * 5956867 * 2
def baseEnd_5956867 : Nat := 1019578655302083488055791

theorem tailTrace_5956867 : CollatzResearch.WordTrace tailWord_5956867 prefixEnd_5956867 1019578655302083488055791 := by
  unfold tailWord_5956867
  simp only [CollatzResearch.WordTrace]
  refine ⟨217264788510295685733188855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144843192340197123822125903 217264788510295685733188855)
  ·
    refine ⟨325897182765443528599783283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217264788510295685733188855 325897182765443528599783283)
    ·
      refine ⟨488845774148165292899674925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325897182765443528599783283 488845774148165292899674925)
      ·
        refine ⟨183317165305561984837378097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488845774148165292899674925 183317165305561984837378097)
        ·
          refine ⟨137487873979171488628033573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183317165305561984837378097 137487873979171488628033573)
          ·
            refine ⟨25778976371094654117756295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137487873979171488628033573 25778976371094654117756295)
            ·
              refine ⟨38668464556641981176634443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25778976371094654117756295 38668464556641981176634443)
              ·
                refine ⟨58002696834962971764951665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38668464556641981176634443 58002696834962971764951665)
                ·
                  refine ⟨43502022626222228823713749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58002696834962971764951665 43502022626222228823713749)
                  ·
                    refine ⟨1019578655302083488055791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43502022626222228823713749 1019578655302083488055791)
                    ·
                      rfl

theorem cell23_5956867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 7].length) (baseStart_5956867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956867 prefixEnd_5956867 := by exact prefixLift 5956867
  have htrace : WordTrace (prefixWord ++ tailWord_5956867) baseStart_5956867 baseEnd_5956867 := by
    simpa [prefixWord, tailWord_5956867, baseEnd_5956867] using wordTrace_append hprefix tailTrace_5956867
  have hstable : (prefixWord ++ tailWord_5956867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956867).length < 2 ^ (prefixWord ++ tailWord_5956867).sum := by decide
  have hdescent : baseEnd_5956867 < baseStart_5956867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956881 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_5956881 : Nat := 118140960795 + 5956881 * 2 ^ 59
def prefixEnd_5956881 : Nat := 4983230072969 + 3 ^ 40 * 5956881 * 2
def baseEnd_5956881 : Nat := 3058743154635413409392309

theorem tailTrace_5956881 : CollatzResearch.WordTrace tailWord_5956881 prefixEnd_5956881 3058743154635413409392309 := by
  unfold tailWord_5956881
  simp only [CollatzResearch.WordTrace]
  refine ⟨217265299132244966124198497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144843532754829977416132331 217265299132244966124198497)
  ·
    refine ⟨162948974349183724593148873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217265299132244966124198497 162948974349183724593148873)
    ·
      refine ⟨122211730761887793444861655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162948974349183724593148873 122211730761887793444861655)
      ·
        refine ⟨183317596142831690167292483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122211730761887793444861655 183317596142831690167292483)
        ·
          refine ⟨274976394214247535250938725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183317596142831690167292483 274976394214247535250938725)
          ·
            refine ⟨51558073915171412859551011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 274976394214247535250938725 51558073915171412859551011)
            ·
              refine ⟨77337110872757119289326517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51558073915171412859551011 77337110872757119289326517)
              ·
                refine ⟨7250354144320979933374361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77337110872757119289326517 7250354144320979933374361)
                ·
                  refine ⟨5437765608240734950030771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250354144320979933374361 5437765608240734950030771)
                  ·
                    refine ⟨8156648412361102425046157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437765608240734950030771 8156648412361102425046157)
                    ·
                      refine ⟨3058743154635413409392309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156648412361102425046157 3058743154635413409392309)
                      ·
                        rfl

theorem cell23_5956881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_5956881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956881 prefixEnd_5956881 := by exact prefixLift 5956881
  have htrace : WordTrace (prefixWord ++ tailWord_5956881) baseStart_5956881 baseEnd_5956881 := by
    simpa [prefixWord, tailWord_5956881, baseEnd_5956881] using wordTrace_append hprefix tailTrace_5956881
  have hstable : (prefixWord ++ tailWord_5956881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956881).length < 2 ^ (prefixWord ++ tailWord_5956881).sum := by decide
  have hdescent : baseEnd_5956881 < baseStart_5956881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956882 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5956882 : Nat := 118140960795 + 5956882 * 2 ^ 59
def prefixEnd_5956882 : Nat := 4983230072969 + 3 ^ 40 * 5956882 * 2
def baseEnd_5956882 : Nat := 3058743668116067905479805

theorem tailTrace_5956882 : CollatzResearch.WordTrace tailWord_5956882 prefixEnd_5956882 3058743668116067905479805 := by
  unfold tailWord_5956882
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316333901310335823746225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144843557070160895529989933 54316333901310335823746225)
  ·
    refine ⟨40737250425982751867809669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54316333901310335823746225 40737250425982751867809669)
    ·
      refine ⟨7638234454871765975214313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40737250425982751867809669 7638234454871765975214313)
      ·
        refine ⟨5728675841153824481410735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7638234454871765975214313 5728675841153824481410735)
        ·
          refine ⟨8593013761730736722116103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728675841153824481410735 8593013761730736722116103)
          ·
            refine ⟨12889520642596105083174155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8593013761730736722116103 12889520642596105083174155)
            ·
              refine ⟨19334280963894157624761233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12889520642596105083174155 19334280963894157624761233)
              ·
                refine ⟨14500710722920618218570925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19334280963894157624761233 14500710722920618218570925)
                ·
                  refine ⟨5437766521095231831964097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14500710722920618218570925 5437766521095231831964097)
                  ·
                    refine ⟨4078324890821423873973073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437766521095231831964097 4078324890821423873973073)
                    ·
                      refine ⟨3058743668116067905479805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078324890821423873973073 3058743668116067905479805)
                      ·
                        rfl

theorem cell23_5956882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5956882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956882 prefixEnd_5956882 := by exact prefixLift 5956882
  have htrace : WordTrace (prefixWord ++ tailWord_5956882) baseStart_5956882 baseEnd_5956882 := by
    simpa [prefixWord, tailWord_5956882, baseEnd_5956882] using wordTrace_append hprefix tailTrace_5956882
  have hstable : (prefixWord ++ tailWord_5956882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956882).length < 2 ^ (prefixWord ++ tailWord_5956882).sum := by decide
  have hdescent : baseEnd_5956882 < baseStart_5956882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956891 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 1, 3, 2]
def baseStart_5956891 : Nat := 118140960795 + 5956891 * 2 ^ 59
def prefixEnd_5956891 : Nat := 4983230072969 + 3 ^ 40 * 5956891 * 2
def baseEnd_5956891 : Nat := 3058748289441958370267263

theorem tailTrace_5956891 : CollatzResearch.WordTrace tailWord_5956891 prefixEnd_5956891 3058748289441958370267263 := by
  unfold tailWord_5956891
  simp only [CollatzResearch.WordTrace]
  refine ⟨217265663862208737832062527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144843775908139158554708351 217265663862208737832062527)
  ·
    refine ⟨325898495793313106748093791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217265663862208737832062527 325898495793313106748093791)
    ·
      refine ⟨488847743689969660122140687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325898495793313106748093791 488847743689969660122140687)
      ·
        refine ⟨733271615534954490183211031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488847743689969660122140687 733271615534954490183211031)
        ·
          refine ⟨1099907423302431735274816547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733271615534954490183211031 1099907423302431735274816547)
          ·
            refine ⟨1649861134953647602912224821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099907423302431735274816547 1649861134953647602912224821)
            ·
              refine ⟨154674481401904462773021077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1649861134953647602912224821 154674481401904462773021077)
              ·
                refine ⟨7250366315714271692485363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154674481401904462773021077 7250366315714271692485363)
                ·
                  refine ⟨10875549473571407538728045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250366315714271692485363 10875549473571407538728045)
                  ·
                    refine ⟨4078331052589277827023017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10875549473571407538728045 4078331052589277827023017)
                    ·
                      refine ⟨3058748289441958370267263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078331052589277827023017 3058748289441958370267263)
                      ·
                        rfl

theorem cell23_5956891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 3, 2].length) (baseStart_5956891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956891 prefixEnd_5956891 := by exact prefixLift 5956891
  have htrace : WordTrace (prefixWord ++ tailWord_5956891) baseStart_5956891 baseEnd_5956891 := by
    simpa [prefixWord, tailWord_5956891, baseEnd_5956891] using wordTrace_append hprefix tailTrace_5956891
  have hstable : (prefixWord ++ tailWord_5956891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956891).length < 2 ^ (prefixWord ++ tailWord_5956891).sum := by decide
  have hdescent : baseEnd_5956891 < baseStart_5956891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956897 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_5956897 : Nat := 118140960795 + 5956897 * 2 ^ 59
def prefixEnd_5956897 : Nat := 4983230072969 + 3 ^ 40 * 5956897 * 2
def baseEnd_5956897 : Nat := 1019583790108628448930745

theorem tailTrace_5956897 : CollatzResearch.WordTrace tailWord_5956897 prefixEnd_5956897 1019583790108628448930745 := by
  unfold tailWord_5956897
  simp only [CollatzResearch.WordTrace]
  refine ⟨217265882700187000856780945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144843921800124667237853963 217265882700187000856780945)
  ·
    refine ⟨162949412025140250642585709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217265882700187000856780945 162949412025140250642585709)
    ·
      refine ⟨61106029509427593990969641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162949412025140250642585709 61106029509427593990969641)
      ·
        refine ⟨45829522132070695493227231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61106029509427593990969641 45829522132070695493227231)
        ·
          refine ⟨68744283198106043239840847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45829522132070695493227231 68744283198106043239840847)
          ·
            refine ⟨103116424797159064859761271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68744283198106043239840847 103116424797159064859761271)
            ·
              refine ⟨154674637195738597289641907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103116424797159064859761271 154674637195738597289641907)
              ·
                refine ⟨232011955793607895934462861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154674637195738597289641907 232011955793607895934462861)
                ·
                  refine ⟨87004483422602960975423573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232011955793607895934462861 87004483422602960975423573)
                  ·
                    refine ⟨1019583790108628448930745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87004483422602960975423573 1019583790108628448930745)
                    ·
                      rfl

theorem cell23_5956897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_5956897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956897 prefixEnd_5956897 := by exact prefixLift 5956897
  have htrace : WordTrace (prefixWord ++ tailWord_5956897) baseStart_5956897 baseEnd_5956897 := by
    simpa [prefixWord, tailWord_5956897, baseEnd_5956897] using wordTrace_append hprefix tailTrace_5956897
  have hstable : (prefixWord ++ tailWord_5956897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956897).length < 2 ^ (prefixWord ++ tailWord_5956897).sum := by decide
  have hdescent : baseEnd_5956897 < baseStart_5956897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956914 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_5956914 : Nat := 118140960795 + 5956914 * 2 ^ 59
def prefixEnd_5956914 : Nat := 4983230072969 + 3 ^ 40 * 5956914 * 2
def baseEnd_5956914 : Nat := 1019586699832337260093219

theorem tailTrace_5956914 : CollatzResearch.WordTrace tailWord_5956914 prefixEnd_5956914 1019586699832337260093219 := by
  unfold tailWord_5956914
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316625685281353190037449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144844335160750275173433197 54316625685281353190037449)
  ·
    refine ⟨40737469263961014892528087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54316625685281353190037449 40737469263961014892528087)
    ·
      refine ⟨61106203895941522338792131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40737469263961014892528087 61106203895941522338792131)
      ·
        refine ⟨91659305843912283508188197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61106203895941522338792131 91659305843912283508188197)
        ·
          refine ⟨17186119845733553157785287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91659305843912283508188197 17186119845733553157785287)
          ·
            refine ⟨25779179768600329736677931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17186119845733553157785287 25779179768600329736677931)
            ·
              refine ⟨38668769652900494605016897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25779179768600329736677931 38668769652900494605016897)
              ·
                refine ⟨29001577239675370953762673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38668769652900494605016897 29001577239675370953762673)
                ·
                  refine ⟨21751182929756528215322005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29001577239675370953762673 21751182929756528215322005)
                  ·
                    refine ⟨1019586699832337260093219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21751182929756528215322005 1019586699832337260093219)
                    ·
                      rfl

theorem cell23_5956914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_5956914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956914 prefixEnd_5956914 := by exact prefixLift 5956914
  have htrace : WordTrace (prefixWord ++ tailWord_5956914) baseStart_5956914 baseEnd_5956914 := by
    simpa [prefixWord, tailWord_5956914, baseEnd_5956914] using wordTrace_append hprefix tailTrace_5956914
  have hstable : (prefixWord ++ tailWord_5956914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956914).length < 2 ^ (prefixWord ++ tailWord_5956914).sum := by decide
  have hdescent : baseEnd_5956914 < baseStart_5956914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956932 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5956932 : Nat := 118140960795 + 5956932 * 2 ^ 59
def prefixEnd_5956932 : Nat := 4983230072969 + 3 ^ 40 * 5956932 * 2
def baseEnd_5956932 : Nat := 3058769342148792709854575

theorem tailTrace_5956932 : CollatzResearch.WordTrace tailWord_5956932 prefixEnd_5956932 3058769342148792709854575 := by
  unfold tailWord_5956932
  simp only [CollatzResearch.WordTrace]
  refine ⟨108633579627530100917152525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144844772836706801222870033 108633579627530100917152525)
  ·
    refine ⟨40737592360323787843932197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108633579627530100917152525 40737592360323787843932197)
    ·
      refine ⟨7638298567560710220737287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40737592360323787843932197 7638298567560710220737287)
      ·
        refine ⟨11457447851341065331105931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7638298567560710220737287 11457447851341065331105931)
        ·
          refine ⟨17186171777011597996658897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11457447851341065331105931 17186171777011597996658897)
          ·
            refine ⟨12889628832758698497494173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17186171777011597996658897 12889628832758698497494173)
            ·
              refine ⟨4833610812284511936560315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12889628832758698497494173 4833610812284511936560315)
              ·
                refine ⟨7250416218426767904840473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833610812284511936560315 7250416218426767904840473)
                ·
                  refine ⟨5437812163820075928630355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250416218426767904840473 5437812163820075928630355)
                  ·
                    refine ⟨8156718245730113892945533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437812163820075928630355 8156718245730113892945533)
                    ·
                      refine ⟨3058769342148792709854575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156718245730113892945533 3058769342148792709854575)
                      ·
                        rfl

theorem cell23_5956932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5956932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956932 prefixEnd_5956932 := by exact prefixLift 5956932
  have htrace : WordTrace (prefixWord ++ tailWord_5956932) baseStart_5956932 baseEnd_5956932 := by
    simpa [prefixWord, tailWord_5956932, baseEnd_5956932] using wordTrace_append hprefix tailTrace_5956932
  have hstable : (prefixWord ++ tailWord_5956932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956932).length < 2 ^ (prefixWord ++ tailWord_5956932).sum := by decide
  have hdescent : baseEnd_5956932 < baseStart_5956932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956938 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_5956938 : Nat := 118140960795 + 5956938 * 2 ^ 59
def prefixEnd_5956938 : Nat := 4983230072969 + 3 ^ 40 * 5956938 * 2
def baseEnd_5956938 : Nat := 3058772423032719686379547

theorem tailTrace_5956938 : CollatzResearch.WordTrace tailWord_5956938 prefixEnd_5956938 3058772423032719686379547 := by
  unfold tailWord_5956938
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316844523259616214755867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144844918728692309906015645 54316844523259616214755867)
  ·
    refine ⟨81475266784889424322133801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54316844523259616214755867 81475266784889424322133801)
    ·
      refine ⟨61106450088667068241600351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81475266784889424322133801 61106450088667068241600351)
      ·
        refine ⟨91659675133000602362400527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61106450088667068241600351 91659675133000602362400527)
        ·
          refine ⟨137489512699500903543600791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91659675133000602362400527 137489512699500903543600791)
          ·
            refine ⟨206234269049251355315401187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137489512699500903543600791 206234269049251355315401187)
            ·
              refine ⟨309351403573877032973101781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206234269049251355315401187 309351403573877032973101781)
              ·
                refine ⟨7250423521262742960307073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 309351403573877032973101781 7250423521262742960307073)
                ·
                  refine ⟨5437817640947057220230305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250423521262742960307073 5437817640947057220230305)
                  ·
                    refine ⟨4078363230710292915172729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437817640947057220230305 4078363230710292915172729)
                    ·
                      refine ⟨3058772423032719686379547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078363230710292915172729 3058772423032719686379547)
                      ·
                        rfl

theorem cell23_5956938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_5956938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956938 prefixEnd_5956938 := by exact prefixLift 5956938
  have htrace : WordTrace (prefixWord ++ tailWord_5956938) baseStart_5956938 baseEnd_5956938 := by
    simpa [prefixWord, tailWord_5956938, baseEnd_5956938] using wordTrace_append hprefix tailTrace_5956938
  have hstable : (prefixWord ++ tailWord_5956938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956938).length < 2 ^ (prefixWord ++ tailWord_5956938).sum := by decide
  have hdescent : baseEnd_5956938 < baseStart_5956938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956950 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5956950 : Nat := 118140960795 + 5956950 * 2 ^ 59
def prefixEnd_5956950 : Nat := 4983230072969 + 3 ^ 40 * 5956950 * 2
def baseEnd_5956950 : Nat := 3058778584800573639429493

theorem tailTrace_5956950 : CollatzResearch.WordTrace tailWord_5956950 prefixEnd_5956950 3058778584800573639429493 := by
  unfold tailWord_5956950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13579238485562186931778769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144845210512663327272306869 13579238485562186931778769)
  ·
    refine ⟨10184428864171640198834077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13579238485562186931778769 10184428864171640198834077)
    ·
      refine ⟨3819160824064365074562779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10184428864171640198834077 3819160824064365074562779)
      ·
        refine ⟨5728741236096547611844169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819160824064365074562779 5728741236096547611844169)
        ·
          refine ⟨4296555927072410708883127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5728741236096547611844169 4296555927072410708883127)
          ·
            refine ⟨6444833890608616063324691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296555927072410708883127 6444833890608616063324691)
            ·
              refine ⟨9667250835912924094987037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6444833890608616063324691 9667250835912924094987037)
              ·
                refine ⟨3625219063467346535620139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9667250835912924094987037 3625219063467346535620139)
                ·
                  refine ⟨5437828595201019803430209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625219063467346535620139 5437828595201019803430209)
                  ·
                    refine ⟨4078371446400764852572657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437828595201019803430209 4078371446400764852572657)
                    ·
                      refine ⟨3058778584800573639429493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078371446400764852572657 3058778584800573639429493)
                      ·
                        rfl

theorem cell23_5956950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5956950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956950 prefixEnd_5956950 := by exact prefixLift 5956950
  have htrace : WordTrace (prefixWord ++ tailWord_5956950) baseStart_5956950 baseEnd_5956950 := by
    simpa [prefixWord, tailWord_5956950, baseEnd_5956950] using wordTrace_append hprefix tailTrace_5956950
  have hstable : (prefixWord ++ tailWord_5956950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956950).length < 2 ^ (prefixWord ++ tailWord_5956950).sum := by decide
  have hdescent : baseEnd_5956950 < baseStart_5956950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956954 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_5956954 : Nat := 118140960795 + 5956954 * 2 ^ 59
def prefixEnd_5956954 : Nat := 4983230072969 + 3 ^ 40 * 5956954 * 2
def baseEnd_5956954 : Nat := 3058780638723191623779473

theorem tailTrace_5956954 : CollatzResearch.WordTrace tailWord_5956954 prefixEnd_5956954 3058780638723191623779473 := by
  unfold tailWord_5956954
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316990415245124897901479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144845307773986999727737277 54316990415245124897901479)
  ·
    refine ⟨81475485622867687346852219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54316990415245124897901479 81475485622867687346852219)
    ·
      refine ⟨122213228434301531020278329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81475485622867687346852219 122213228434301531020278329)
      ·
        refine ⟨91659921325726148265208747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122213228434301531020278329 91659921325726148265208747)
        ·
          refine ⟨137489881988589222397813121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91659921325726148265208747 137489881988589222397813121)
          ·
            refine ⟨103117411491441916798359841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137489881988589222397813121 103117411491441916798359841)
            ·
              refine ⟨77338058618581437598769881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103117411491441916798359841 77338058618581437598769881)
              ·
                refine ⟨58003543963936078199077411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77338058618581437598769881 58003543963936078199077411)
                ·
                  refine ⟨87005315945904117298616117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58003543963936078199077411 87005315945904117298616117)
                  ·
                    refine ⟨8156748369928510996745261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87005315945904117298616117 8156748369928510996745261)
                    ·
                      refine ⟨3058780638723191623779473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156748369928510996745261 3058780638723191623779473)
                      ·
                        rfl

theorem cell23_5956954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_5956954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956954 prefixEnd_5956954 := by exact prefixLift 5956954
  have htrace : WordTrace (prefixWord ++ tailWord_5956954) baseStart_5956954 baseEnd_5956954 := by
    simpa [prefixWord, tailWord_5956954, baseEnd_5956954] using wordTrace_append hprefix tailTrace_5956954
  have hstable : (prefixWord ++ tailWord_5956954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956954).length < 2 ^ (prefixWord ++ tailWord_5956954).sum := by decide
  have hdescent : baseEnd_5956954 < baseStart_5956954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5956978 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_5956978 : Nat := 118140960795 + 5956978 * 2 ^ 59
def prefixEnd_5956978 : Nat := 4983230072969 + 3 ^ 40 * 5956978 * 2
def baseEnd_5956978 : Nat := 339865884695433281097707

theorem tailTrace_5956978 : CollatzResearch.WordTrace tailWord_5956978 prefixEnd_5956978 339865884695433281097707 := by
  unfold tailWord_5956978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54317209253223387922619897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144845891341929034460319725 54317209253223387922619897)
  ·
    refine ⟨40737906939917540941964923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54317209253223387922619897 40737906939917540941964923)
    ·
      refine ⟨61106860409876311412947385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40737906939917540941964923 61106860409876311412947385)
      ·
        refine ⟨45830145307407233559710539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61106860409876311412947385 45830145307407233559710539)
        ·
          refine ⟨68745217961110850339565809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45830145307407233559710539 68745217961110850339565809)
          ·
            refine ⟨51558913470833137754674357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68745217961110850339565809 51558913470833137754674357)
            ·
              refine ⟨4833648137890606664500721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51558913470833137754674357 4833648137890606664500721)
              ·
                refine ⟨3625236103417954998375541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4833648137890606664500721 3625236103417954998375541)
                ·
                  refine ⟨339865884695433281097707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3625236103417954998375541 339865884695433281097707)
                  ·
                    rfl

theorem cell23_5956978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_5956978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5956978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5956978 prefixEnd_5956978 := by exact prefixLift 5956978
  have htrace : WordTrace (prefixWord ++ tailWord_5956978) baseStart_5956978 baseEnd_5956978 := by
    simpa [prefixWord, tailWord_5956978, baseEnd_5956978] using wordTrace_append hprefix tailTrace_5956978
  have hstable : (prefixWord ++ tailWord_5956978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5956978).length < 2 ^ (prefixWord ++ tailWord_5956978).sum := by decide
  have hdescent : baseEnd_5956978 < baseStart_5956978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5956978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957024 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_5957024 : Nat := 118140960795 + 5957024 * 2 ^ 59
def prefixEnd_5957024 : Nat := 4983230072969 + 3 ^ 40 * 5957024 * 2
def baseEnd_5957024 : Nat := 3058816582369006349904151

theorem tailTrace_5957024 : CollatzResearch.WordTrace tailWord_5957024 prefixEnd_5957024 3058816582369006349904151 := by
  unfold tailWord_5957024
  simp only [CollatzResearch.WordTrace]
  refine ⟨108635257385363450773327063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144847009847151267697769417 108635257385363450773327063)
  ·
    refine ⟨162952886078045176159990595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108635257385363450773327063 162952886078045176159990595)
    ·
      refine ⟨244429329117067764239985893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162952886078045176159990595 244429329117067764239985893)
      ·
        refine ⟨45830499209450205794997355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244429329117067764239985893 45830499209450205794997355)
        ·
          refine ⟨68745748814175308692496033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45830499209450205794997355 68745748814175308692496033)
          ·
            refine ⟨51559311610631481519372025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68745748814175308692496033 51559311610631481519372025)
            ·
              refine ⟨38669483707973611139529019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51559311610631481519372025 38669483707973611139529019)
              ·
                refine ⟨58004225561960416709293529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38669483707973611139529019 58004225561960416709293529)
                ·
                  refine ⟨43503169171470312531970147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58004225561960416709293529 43503169171470312531970147)
                  ·
                    refine ⟨65254753757205468797955221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43503169171470312531970147 65254753757205468797955221)
                    ·
                      refine ⟨3058816582369006349904151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65254753757205468797955221 3058816582369006349904151)
                      ·
                        rfl

theorem cell23_5957024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_5957024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957024 prefixEnd_5957024 := by exact prefixLift 5957024
  have htrace : WordTrace (prefixWord ++ tailWord_5957024) baseStart_5957024 baseEnd_5957024 := by
    simpa [prefixWord, tailWord_5957024, baseEnd_5957024] using wordTrace_append hprefix tailTrace_5957024
  have hstable : (prefixWord ++ tailWord_5957024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957024).length < 2 ^ (prefixWord ++ tailWord_5957024).sum := by decide
  have hdescent : baseEnd_5957024 < baseStart_5957024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957095 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_5957095 : Nat := 118140960795 + 5957095 * 2 ^ 59
def prefixEnd_5957095 : Nat := 4983230072969 + 3 ^ 40 * 5957095 * 2
def baseEnd_5957095 : Nat := 3058853039495475572116325

theorem tailTrace_5957095 : CollatzResearch.WordTrace tailWord_5957095 prefixEnd_5957095 3058853039495475572116325 := by
  unfold tailWord_5957095
  simp only [CollatzResearch.WordTrace]
  refine ⟨217273104353469680672488739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144848736235646453781659159 217273104353469680672488739)
  ·
    refine ⟨325909656530204521008733109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217273104353469680672488739 325909656530204521008733109)
    ·
      refine ⟨30554030299706673844568729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325909656530204521008733109 30554030299706673844568729)
      ·
        refine ⟨22915522724780005383426547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30554030299706673844568729 22915522724780005383426547)
        ·
          refine ⟨34373284087170008075139821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22915522724780005383426547 34373284087170008075139821)
          ·
            refine ⟨12889981532688753028177433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34373284087170008075139821 12889981532688753028177433)
            ·
              refine ⟨9667486149516564771133075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12889981532688753028177433 9667486149516564771133075)
              ·
                refine ⟨14501229224274847156699613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9667486149516564771133075 14501229224274847156699613)
                ·
                  refine ⟨5437960959103067683762355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14501229224274847156699613 5437960959103067683762355)
                  ·
                    refine ⟨8156941438654601525643533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437960959103067683762355 8156941438654601525643533)
                    ·
                      refine ⟨3058853039495475572116325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8156941438654601525643533 3058853039495475572116325)
                      ·
                        rfl

theorem cell23_5957095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_5957095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957095 prefixEnd_5957095 := by exact prefixLift 5957095
  have htrace : WordTrace (prefixWord ++ tailWord_5957095) baseStart_5957095 baseEnd_5957095 := by
    simpa [prefixWord, tailWord_5957095, baseEnd_5957095] using wordTrace_append hprefix tailTrace_5957095
  have hstable : (prefixWord ++ tailWord_5957095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957095).length < 2 ^ (prefixWord ++ tailWord_5957095).sum := by decide
  have hdescent : baseEnd_5957095 < baseStart_5957095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957141 : List Nat := [1, 3, 2, 1, 3, 4, 9]
def baseStart_5957141 : Nat := 118140960795 + 5957141 * 2 ^ 59
def prefixEnd_5957141 : Nat := 4983230072969 + 3 ^ 40 * 5957141 * 2
def baseEnd_5957141 : Nat := 37763909377846696199273

theorem tailTrace_5957141 : CollatzResearch.WordTrace tailWord_5957141 prefixEnd_5957141 37763909377846696199273 := by
  unfold tailWord_5957141
  simp only [CollatzResearch.WordTrace]
  refine ⟨217274782111303030528663277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144849854740868687019108851 217274782111303030528663277)
  ·
    refine ⟨81478043291738636448248729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217274782111303030528663277 81478043291738636448248729)
    ·
      refine ⟨61108532468803977336186547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81478043291738636448248729 61108532468803977336186547)
      ·
        refine ⟨91662798703205966004279821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61108532468803977336186547 91662798703205966004279821)
        ·
          refine ⟨34373549513702237251604933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91662798703205966004279821 34373549513702237251604933)
          ·
            refine ⟨6445040533819169484675925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34373549513702237251604933 6445040533819169484675925)
            ·
              refine ⟨37763909377846696199273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6445040533819169484675925 37763909377846696199273)
              ·
                rfl

theorem cell23_5957141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 9].length) (baseStart_5957141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957141 prefixEnd_5957141 := by exact prefixLift 5957141
  have htrace : WordTrace (prefixWord ++ tailWord_5957141) baseStart_5957141 baseEnd_5957141 := by
    simpa [prefixWord, tailWord_5957141, baseEnd_5957141] using wordTrace_append hprefix tailTrace_5957141
  have hstable : (prefixWord ++ tailWord_5957141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957141).length < 2 ^ (prefixWord ++ tailWord_5957141).sum := by decide
  have hdescent : baseEnd_5957141 < baseStart_5957141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957152 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5957152 : Nat := 118140960795 + 5957152 * 2 ^ 59
def prefixEnd_5957152 : Nat := 4983230072969 + 3 ^ 40 * 5957152 * 2
def baseEnd_5957152 : Nat := 3058882307892781849103563

theorem tailTrace_5957152 : CollatzResearch.WordTrace tailWord_5957152 prefixEnd_5957152 3058882307892781849103563 := by
  unfold tailWord_5957152
  simp only [CollatzResearch.WordTrace]
  refine ⟨108637591657131589703656855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144850122209508786271542473 108637591657131589703656855)
  ·
    refine ⟨162956387485697384555485283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108637591657131589703656855 162956387485697384555485283)
    ·
      refine ⟨244434581228546076833227925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162956387485697384555485283 244434581228546076833227925)
      ·
        refine ⟨11457870995088097351557559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244434581228546076833227925 11457870995088097351557559)
        ·
          refine ⟨17186806492632146027336339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11457870995088097351557559 17186806492632146027336339)
          ·
            refine ⟨25780209738948219041004509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17186806492632146027336339 25780209738948219041004509)
            ·
              refine ⟨9667578652105582140376691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25780209738948219041004509 9667578652105582140376691)
              ·
                refine ⟨14501367978158373210565037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9667578652105582140376691 14501367978158373210565037)
                ·
                  refine ⟨5438012991809389953961889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14501367978158373210565037 5438012991809389953961889)
                  ·
                    refine ⟨4078509743857042465471417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5438012991809389953961889 4078509743857042465471417)
                    ·
                      refine ⟨3058882307892781849103563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078509743857042465471417 3058882307892781849103563)
                      ·
                        rfl

theorem cell23_5957152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5957152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957152 prefixEnd_5957152 := by exact prefixLift 5957152
  have htrace : WordTrace (prefixWord ++ tailWord_5957152) baseStart_5957152 baseEnd_5957152 := by
    simpa [prefixWord, tailWord_5957152, baseEnd_5957152] using wordTrace_append hprefix tailTrace_5957152
  have hstable : (prefixWord ++ tailWord_5957152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957152).length < 2 ^ (prefixWord ++ tailWord_5957152).sum := by decide
  have hdescent : baseEnd_5957152 < baseStart_5957152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957201 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_5957201 : Nat := 118140960795 + 5957201 * 2 ^ 59
def prefixEnd_5957201 : Nat := 4983230072969 + 3 ^ 40 * 5957201 * 2
def baseEnd_5957201 : Nat := 1019635822814950719130279

theorem tailTrace_5957201 : CollatzResearch.WordTrace tailWord_5957201 prefixEnd_5957201 1019635822814950719130279 := by
  unfold tailWord_5957201
  simp only [CollatzResearch.WordTrace]
  refine ⟨217276970491085660775847457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144851313660723773850564971 217276970491085660775847457)
  ·
    refine ⟨162957727868314245581885593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217276970491085660775847457 162957727868314245581885593)
    ·
      refine ⟨122218295901235684186414195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162957727868314245581885593 122218295901235684186414195)
      ·
        refine ⟨183327443851853526279621293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122218295901235684186414195 183327443851853526279621293)
        ·
          refine ⟨68747791444445072354857985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183327443851853526279621293 68747791444445072354857985)
          ·
            refine ⟨51560843583333804266143489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68747791444445072354857985 51560843583333804266143489)
            ·
              refine ⟨38670632687500353199607617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51560843583333804266143489 38670632687500353199607617)
              ·
                refine ⟨29002974515625264899705713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38670632687500353199607617 29002974515625264899705713)
                ·
                  refine ⟨21752230886718948674779285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29002974515625264899705713 21752230886718948674779285)
                  ·
                    refine ⟨1019635822814950719130279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21752230886718948674779285 1019635822814950719130279)
                    ·
                      rfl

theorem cell23_5957201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_5957201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957201 prefixEnd_5957201 := by exact prefixLift 5957201
  have htrace : WordTrace (prefixWord ++ tailWord_5957201) baseStart_5957201 baseEnd_5957201 := by
    simpa [prefixWord, tailWord_5957201, baseEnd_5957201] using wordTrace_append hprefix tailTrace_5957201
  have hstable : (prefixWord ++ tailWord_5957201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957201).length < 2 ^ (prefixWord ++ tailWord_5957201).sum := by decide
  have hdescent : baseEnd_5957201 < baseStart_5957201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957202 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_5957202 : Nat := 118140960795 + 5957202 * 2 ^ 59
def prefixEnd_5957202 : Nat := 4983230072969 + 3 ^ 40 * 5957202 * 2
def baseEnd_5957202 : Nat := 3058907981925506653478333

theorem tailTrace_5957202 : CollatzResearch.WordTrace tailWord_5957202 prefixEnd_5957202 3058907981925506653478333 := by
  unfold tailWord_5957202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54319251741020509486658465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144851337976054691964422573 54319251741020509486658465)
  ·
    refine ⟨40739438805765382114993849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54319251741020509486658465 40739438805765382114993849)
    ·
      refine ⟨30554579104324036586245387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40739438805765382114993849 30554579104324036586245387)
      ·
        refine ⟨45831868656486054879368081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30554579104324036586245387 45831868656486054879368081)
        ·
          refine ⟨34373901492364541159526061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45831868656486054879368081 34373901492364541159526061)
          ·
            refine ⟨12890213059636702934822273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34373901492364541159526061 12890213059636702934822273)
            ·
              refine ⟨9667659794727527201116705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12890213059636702934822273 9667659794727527201116705)
              ·
                refine ⟨7250744846045645400837529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9667659794727527201116705 7250744846045645400837529)
                ·
                  refine ⟨5438058634534234050628147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250744846045645400837529 5438058634534234050628147)
                  ·
                    refine ⟨8157087951801351075942221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438058634534234050628147 8157087951801351075942221)
                    ·
                      refine ⟨3058907981925506653478333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157087951801351075942221 3058907981925506653478333)
                      ·
                        rfl

theorem cell23_5957202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_5957202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957202 prefixEnd_5957202 := by exact prefixLift 5957202
  have htrace : WordTrace (prefixWord ++ tailWord_5957202) baseStart_5957202 baseEnd_5957202 := by
    simpa [prefixWord, tailWord_5957202, baseEnd_5957202] using wordTrace_append hprefix tailTrace_5957202
  have hstable : (prefixWord ++ tailWord_5957202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957202).length < 2 ^ (prefixWord ++ tailWord_5957202).sum := by decide
  have hdescent : baseEnd_5957202 < baseStart_5957202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957208 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 5, 4, 2]
def baseStart_5957208 : Nat := 118140960795 + 5957208 * 2 ^ 59
def prefixEnd_5957208 : Nat := 4983230072969 + 3 ^ 40 * 5957208 * 2
def baseEnd_5957208 : Nat := 3058911062809433630003305

theorem tailTrace_5957208 : CollatzResearch.WordTrace tailWord_5957208 prefixEnd_5957208 3058911062809433630003305 := by
  unfold tailWord_5957208
  simp only [CollatzResearch.WordTrace]
  refine ⟨108638612901030150485676139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144851483868040200647568185 108638612901030150485676139)
  ·
    refine ⟨162957919351545225728514209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108638612901030150485676139 162957919351545225728514209)
    ·
      refine ⟨122218439513658919296385657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162957919351545225728514209 122218439513658919296385657)
      ·
        refine ⟨91663829635244189472289243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122218439513658919296385657 91663829635244189472289243)
        ·
          refine ⟨137495744452866284208433865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91663829635244189472289243 137495744452866284208433865)
          ·
            refine ⟨103121808339649713156325399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137495744452866284208433865 103121808339649713156325399)
            ·
              refine ⟨154682712509474569734488099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103121808339649713156325399 154682712509474569734488099)
              ·
                refine ⟨232024068764211854601732149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154682712509474569734488099 232024068764211854601732149)
                ·
                  refine ⟨21752256446644861368912389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232024068764211854601732149 21752256446644861368912389)
                  ·
                    refine ⟨4078548083745911506671073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21752256446644861368912389 4078548083745911506671073)
                    ·
                      refine ⟨3058911062809433630003305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078548083745911506671073 3058911062809433630003305)
                      ·
                        rfl

theorem cell23_5957208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_5957208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957208 prefixEnd_5957208 := by exact prefixLift 5957208
  have htrace : WordTrace (prefixWord ++ tailWord_5957208) baseStart_5957208 baseEnd_5957208 := by
    simpa [prefixWord, tailWord_5957208, baseEnd_5957208] using wordTrace_append hprefix tailTrace_5957208
  have hstable : (prefixWord ++ tailWord_5957208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957208).length < 2 ^ (prefixWord ++ tailWord_5957208).sum := by decide
  have hdescent : baseEnd_5957208 < baseStart_5957208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957276 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5957276 : Nat := 118140960795 + 5957276 * 2 ^ 59
def prefixEnd_5957276 : Nat := 4983230072969 + 3 ^ 40 * 5957276 * 2
def baseEnd_5957276 : Nat := 3058945979493939363952993

theorem tailTrace_5957276 : CollatzResearch.WordTrace tailWord_5957276 prefixEnd_5957276 3058945979493939363952993 := by
  unfold tailWord_5957276
  simp only [CollatzResearch.WordTrace]
  refine ⟨108639852982906974292413841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144853137310542632389885121 108639852982906974292413841)
  ·
    refine ⟨81479889737180230719310381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108639852982906974292413841 81479889737180230719310381)
    ·
      refine ⟨30554958651442586519741393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81479889737180230719310381 30554958651442586519741393)
      ·
        refine ⟨22916218988581939889806045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30554958651442586519741393 22916218988581939889806045)
        ·
          refine ⟨8593582120718227458677267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22916218988581939889806045 8593582120718227458677267)
          ·
            refine ⟨12890373181077341188015901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8593582120718227458677267 12890373181077341188015901)
            ·
              refine ⟨4833889942904002945505963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12890373181077341188015901 4833889942904002945505963)
              ·
                refine ⟨7250834914356004418258945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833889942904002945505963 7250834914356004418258945)
                ·
                  refine ⟨5438126185767003313694209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7250834914356004418258945 5438126185767003313694209)
                  ·
                    refine ⟨4078594639325252485270657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5438126185767003313694209 4078594639325252485270657)
                    ·
                      refine ⟨3058945979493939363952993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078594639325252485270657 3058945979493939363952993)
                      ·
                        rfl

theorem cell23_5957276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5957276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957276 prefixEnd_5957276 := by exact prefixLift 5957276
  have htrace : WordTrace (prefixWord ++ tailWord_5957276) baseStart_5957276 baseEnd_5957276 := by
    simpa [prefixWord, tailWord_5957276, baseEnd_5957276] using wordTrace_append hprefix tailTrace_5957276
  have hstable : (prefixWord ++ tailWord_5957276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957276).length < 2 ^ (prefixWord ++ tailWord_5957276).sum := by decide
  have hdescent : baseEnd_5957276 < baseStart_5957276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957298 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_5957298 : Nat := 118140960795 + 5957298 * 2 ^ 59
def prefixEnd_5957298 : Nat := 4983230072969 + 3 ^ 40 * 5957298 * 2
def baseEnd_5957298 : Nat := 3058957276068338277877891

theorem tailTrace_5957298 : CollatzResearch.WordTrace tailWord_5957298 prefixEnd_5957298 3058957276068338277877891 := by
  unfold tailWord_5957298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54320127092933561585532137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144853672247822830894752365 54320127092933561585532137)
  ·
    refine ⟨40740095319700171189149103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54320127092933561585532137 40740095319700171189149103)
    ·
      refine ⟨61110142979550256783723655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40740095319700171189149103 61110142979550256783723655)
      ·
        refine ⟨91665214469325385175585483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61110142979550256783723655 91665214469325385175585483)
        ·
          refine ⟨137497821703988077763378225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91665214469325385175585483 137497821703988077763378225)
          ·
            refine ⟨103123366277991058322533669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137497821703988077763378225 103123366277991058322533669)
            ·
              refine ⟨19335631177123323435475063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103123366277991058322533669 19335631177123323435475063)
              ·
                refine ⟨29003446765684985153212595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19335631177123323435475063 29003446765684985153212595)
                ·
                  refine ⟨43505170148527477729818893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29003446765684985153212595 43505170148527477729818893)
                  ·
                    refine ⟨16314438805697804148682085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43505170148527477729818893 16314438805697804148682085)
                    ·
                      refine ⟨3058957276068338277877891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16314438805697804148682085 3058957276068338277877891)
                      ·
                        rfl

theorem cell23_5957298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_5957298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957298 prefixEnd_5957298 := by exact prefixLift 5957298
  have htrace : WordTrace (prefixWord ++ tailWord_5957298) baseStart_5957298 baseEnd_5957298 := by
    simpa [prefixWord, tailWord_5957298, baseEnd_5957298] using wordTrace_append hprefix tailTrace_5957298
  have hstable : (prefixWord ++ tailWord_5957298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957298).length < 2 ^ (prefixWord ++ tailWord_5957298).sum := by decide
  have hdescent : baseEnd_5957298 < baseStart_5957298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957331 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_5957331 : Nat := 118140960795 + 5957331 * 2 ^ 59
def prefixEnd_5957331 : Nat := 4983230072969 + 3 ^ 40 * 5957331 * 2
def baseEnd_5957331 : Nat := 3058974220929936648765239

theorem tailTrace_5957331 : CollatzResearch.WordTrace tailWord_5957331 prefixEnd_5957331 3058974220929936648765239 := by
  unfold tailWord_5957331
  simp only [CollatzResearch.WordTrace]
  refine ⟨217281711980614692978079847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144854474653743128652053231 217281711980614692978079847)
  ·
    refine ⟨325922567970922039467119771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217281711980614692978079847 325922567970922039467119771)
    ·
      refine ⟨488883851956383059200679657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325922567970922039467119771 488883851956383059200679657)
      ·
        refine ⟨366662888967287294400509743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488883851956383059200679657 366662888967287294400509743)
        ·
          refine ⟨549994333450930941600764615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366662888967287294400509743 549994333450930941600764615)
          ·
            refine ⟨824991500176396412401146923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549994333450930941600764615 824991500176396412401146923)
            ·
              refine ⟨1237487250264594618601720385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824991500176396412401146923 1237487250264594618601720385)
              ·
                refine ⟨928115437698445963951290289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237487250264594618601720385 928115437698445963951290289)
                ·
                  refine ⟨696086578273834472963467717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928115437698445963951290289 696086578273834472963467717)
                  ·
                    refine ⟨130516233426343963680650197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696086578273834472963467717 130516233426343963680650197)
                    ·
                      refine ⟨3058974220929936648765239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130516233426343963680650197 3058974220929936648765239)
                      ·
                        rfl

theorem cell23_5957331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_5957331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957331 prefixEnd_5957331 := by exact prefixLift 5957331
  have htrace : WordTrace (prefixWord ++ tailWord_5957331) baseStart_5957331 baseEnd_5957331 := by
    simpa [prefixWord, tailWord_5957331, baseEnd_5957331] using wordTrace_append hprefix tailTrace_5957331
  have hstable : (prefixWord ++ tailWord_5957331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957331).length < 2 ^ (prefixWord ++ tailWord_5957331).sum := by decide
  have hdescent : baseEnd_5957331 < baseStart_5957331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957352 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5957352 : Nat := 118140960795 + 5957352 * 2 ^ 59
def prefixEnd_5957352 : Nat := 4983230072969 + 3 ^ 40 * 5957352 * 2
def baseEnd_5957352 : Nat := 3058985004023681066602643

theorem tailTrace_5957352 : CollatzResearch.WordTrace tailWord_5957352 prefixEnd_5957352 3058985004023681066602643 := by
  unfold tailWord_5957352
  simp only [CollatzResearch.WordTrace]
  refine ⟨108641238956769306782297155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144854985275692409043062873 108641238956769306782297155)
  ·
    refine ⟨162961858435153960173445733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108641238956769306782297155 162961858435153960173445733)
    ·
      refine ⟨30555348456591367532521075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162961858435153960173445733 30555348456591367532521075)
      ·
        refine ⟨45833022684887051298781613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30555348456591367532521075 45833022684887051298781613)
        ·
          refine ⟨17187383506832644237043105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45833022684887051298781613 17187383506832644237043105)
          ·
            refine ⟨12890537630124483177782329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17187383506832644237043105 12890537630124483177782329)
            ·
              refine ⟨9667903222593362383336747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12890537630124483177782329 9667903222593362383336747)
              ·
                refine ⟨14501854833890043575005121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9667903222593362383336747 14501854833890043575005121)
                ·
                  refine ⟨10876391125417532681253841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14501854833890043575005121 10876391125417532681253841)
                  ·
                    refine ⟨8157293344063149510940381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10876391125417532681253841 8157293344063149510940381)
                    ·
                      refine ⟨3058985004023681066602643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157293344063149510940381 3058985004023681066602643)
                      ·
                        rfl

theorem cell23_5957352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5957352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957352 prefixEnd_5957352 := by exact prefixLift 5957352
  have htrace : WordTrace (prefixWord ++ tailWord_5957352) baseStart_5957352 baseEnd_5957352 := by
    simpa [prefixWord, tailWord_5957352, baseEnd_5957352] using wordTrace_append hprefix tailTrace_5957352
  have hstable : (prefixWord ++ tailWord_5957352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957352).length < 2 ^ (prefixWord ++ tailWord_5957352).sum := by decide
  have hdescent : baseEnd_5957352 < baseStart_5957352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957409 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5957409 : Nat := 118140960795 + 5957409 * 2 ^ 59
def prefixEnd_5957409 : Nat := 4983230072969 + 3 ^ 40 * 5957409 * 2
def baseEnd_5957409 : Nat := 3059014272420987343589881

theorem tailTrace_5957409 : CollatzResearch.WordTrace tailWord_5957409 prefixEnd_5957409 3059014272420987343589881 := by
  unfold tailWord_5957409
  simp only [CollatzResearch.WordTrace]
  refine ⟨217284556874332112299419281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144856371249554741532946187 217284556874332112299419281)
  ·
    refine ⟨162963417655749084224564461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217284556874332112299419281 162963417655749084224564461)
    ·
      refine ⟨61111281620905906584211673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162963417655749084224564461 61111281620905906584211673)
      ·
        refine ⟨45833461215679429938158755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61111281620905906584211673 45833461215679429938158755)
        ·
          refine ⟨68750191823519144907238133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45833461215679429938158755 68750191823519144907238133)
          ·
            refine ⟨6445330483454919835053575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68750191823519144907238133 6445330483454919835053575)
            ·
              refine ⟨9667995725182379752580363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445330483454919835053575 9667995725182379752580363)
              ·
                refine ⟨14501993587773569628870545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9667995725182379752580363 14501993587773569628870545)
                ·
                  refine ⟨10876495190830177221652909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14501993587773569628870545 10876495190830177221652909)
                  ·
                    refine ⟨4078685696561316458119841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10876495190830177221652909 4078685696561316458119841)
                    ·
                      refine ⟨3059014272420987343589881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078685696561316458119841 3059014272420987343589881)
                      ·
                        rfl

theorem cell23_5957409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5957409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957409 prefixEnd_5957409 := by exact prefixLift 5957409
  have htrace : WordTrace (prefixWord ++ tailWord_5957409) baseStart_5957409 baseEnd_5957409 := by
    simpa [prefixWord, tailWord_5957409, baseEnd_5957409] using wordTrace_append hprefix tailTrace_5957409
  have hstable : (prefixWord ++ tailWord_5957409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957409).length < 2 ^ (prefixWord ++ tailWord_5957409).sum := by decide
  have hdescent : baseEnd_5957409 < baseStart_5957409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957416 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_5957416 : Nat := 118140960795 + 5957416 * 2 ^ 59
def prefixEnd_5957416 : Nat := 4983230072969 + 3 ^ 40 * 5957416 * 2
def baseEnd_5957416 : Nat := 3059017866785568816202349

theorem tailTrace_5957416 : CollatzResearch.WordTrace tailWord_5957416 prefixEnd_5957416 3059017866785568816202349 := by
  unfold tailWord_5957416
  simp only [CollatzResearch.WordTrace]
  refine ⟨108642406092653376247462051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144856541456871168329949401 108642406092653376247462051)
  ·
    refine ⟨162963609138980064371193077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108642406092653376247462051 162963609138980064371193077)
    ·
      refine ⟨15277838356779381034799351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162963609138980064371193077 15277838356779381034799351)
      ·
        refine ⟨22916757535169071552199027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15277838356779381034799351 22916757535169071552199027)
        ·
          refine ⟨34375136302753607328298541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22916757535169071552199027 34375136302753607328298541)
          ·
            refine ⟨12890676113532602748111953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34375136302753607328298541 12890676113532602748111953)
            ·
              refine ⟨9668007085149452061083965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12890676113532602748111953 9668007085149452061083965)
              ·
                refine ⟨3625502656931044522906487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9668007085149452061083965 3625502656931044522906487)
                ·
                  refine ⟨5438253985396566784359731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625502656931044522906487 5438253985396566784359731)
                  ·
                    refine ⟨8157380978094850176539597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438253985396566784359731 8157380978094850176539597)
                    ·
                      refine ⟨3059017866785568816202349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157380978094850176539597 3059017866785568816202349)
                      ·
                        rfl

theorem cell23_5957416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_5957416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957416 prefixEnd_5957416 := by exact prefixLift 5957416
  have htrace : WordTrace (prefixWord ++ tailWord_5957416) baseStart_5957416 baseEnd_5957416 := by
    simpa [prefixWord, tailWord_5957416, baseEnd_5957416] using wordTrace_append hprefix tailTrace_5957416
  have hstable : (prefixWord ++ tailWord_5957416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957416).length < 2 ^ (prefixWord ++ tailWord_5957416).sum := by decide
  have hdescent : baseEnd_5957416 < baseStart_5957416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957432 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 2, 4]
def baseStart_5957432 : Nat := 118140960795 + 5957432 * 2 ^ 59
def prefixEnd_5957432 : Nat := 4983230072969 + 3 ^ 40 * 5957432 * 2
def baseEnd_5957432 : Nat := 1019675360825346917867425

theorem tailTrace_5957432 : CollatzResearch.WordTrace tailWord_5957432 prefixEnd_5957432 1019675360825346917867425 := by
  unfold tailWord_5957432
  simp only [CollatzResearch.WordTrace]
  refine ⟨108642697876624393613753275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144856930502165858151671033 108642697876624393613753275)
  ·
    refine ⟨162964046814936590420629913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108642697876624393613753275 162964046814936590420629913)
    ·
      refine ⟨122223035111202442815472435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162964046814936590420629913 122223035111202442815472435)
      ·
        refine ⟨183334552666803664223208653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122223035111202442815472435 183334552666803664223208653)
        ·
          refine ⟨68750457250051374083703245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183334552666803664223208653 68750457250051374083703245)
          ·
            refine ⟨25781421468769265281388717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68750457250051374083703245 25781421468769265281388717)
            ·
              refine ⟨9668033050788474480520769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25781421468769265281388717 9668033050788474480520769)
              ·
                refine ⟨7251024788091355860390577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9668033050788474480520769 7251024788091355860390577)
                ·
                  refine ⟨5438268591068516895292933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7251024788091355860390577 5438268591068516895292933)
                  ·
                    refine ⟨1019675360825346917867425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5438268591068516895292933 1019675360825346917867425)
                    ·
                      rfl

theorem cell23_5957432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_5957432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957432 prefixEnd_5957432 := by exact prefixLift 5957432
  have htrace : WordTrace (prefixWord ++ tailWord_5957432) baseStart_5957432 baseEnd_5957432 := by
    simpa [prefixWord, tailWord_5957432, baseEnd_5957432] using wordTrace_append hprefix tailTrace_5957432
  have hstable : (prefixWord ++ tailWord_5957432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957432).length < 2 ^ (prefixWord ++ tailWord_5957432).sum := by decide
  have hdescent : baseEnd_5957432 < baseStart_5957432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957472 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 4, 1, 3]
def baseStart_5957472 : Nat := 118140960795 + 5957472 * 2 ^ 59
def prefixEnd_5957472 : Nat := 4983230072969 + 3 ^ 40 * 5957472 * 2
def baseEnd_5957472 : Nat := 3059046621702220597102091

theorem tailTrace_5957472 : CollatzResearch.WordTrace tailWord_5957472 prefixEnd_5957472 3059046621702220597102091 := by
  unfold tailWord_5957472
  simp only [CollatzResearch.WordTrace]
  refine ⟨108643427336551937029481335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144857903115402582705975113 108643427336551937029481335)
  ·
    refine ⟨162965141004827905544222003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108643427336551937029481335 162965141004827905544222003)
    ·
      refine ⟨244447711507241858316333005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162965141004827905544222003 244447711507241858316333005)
      ·
        refine ⟨91667891815215696868624877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244447711507241858316333005 91667891815215696868624877)
        ·
          refine ⟨34375459430705886325734329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91667891815215696868624877 34375459430705886325734329)
          ·
            refine ⟨25781594573029414744300747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34375459430705886325734329 25781594573029414744300747)
            ·
              refine ⟨38672391859544122116451121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25781594573029414744300747 38672391859544122116451121)
              ·
                refine ⟨29004293894658091587338341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38672391859544122116451121 29004293894658091587338341)
                ·
                  refine ⟨5438305105248392172625939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29004293894658091587338341 5438305105248392172625939)
                  ·
                    refine ⟨8157457657872588258938909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438305105248392172625939 8157457657872588258938909)
                    ·
                      refine ⟨3059046621702220597102091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157457657872588258938909 3059046621702220597102091)
                      ·
                        rfl

theorem cell23_5957472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_5957472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957472 prefixEnd_5957472 := by exact prefixLift 5957472
  have htrace : WordTrace (prefixWord ++ tailWord_5957472) baseStart_5957472 baseEnd_5957472 := by
    simpa [prefixWord, tailWord_5957472, baseEnd_5957472] using wordTrace_append hprefix tailTrace_5957472
  have hstable : (prefixWord ++ tailWord_5957472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957472).length < 2 ^ (prefixWord ++ tailWord_5957472).sum := by decide
  have hdescent : baseEnd_5957472 < baseStart_5957472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957532 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5957532 : Nat := 118140960795 + 5957532 * 2 ^ 59
def prefixEnd_5957532 : Nat := 4983230072969 + 3 ^ 40 * 5957532 * 2
def baseEnd_5957532 : Nat := 3059077430541490362351815

theorem tailTrace_5957532 : CollatzResearch.WordTrace tailWord_5957532 prefixEnd_5957532 3059077430541490362351815 := by
  unfold tailWord_5957532
  simp only [CollatzResearch.WordTrace]
  refine ⟨108644521526443252153073425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144859362035257669537431233 108644521526443252153073425)
  ·
    refine ⟨81483391144832439114805069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108644521526443252153073425 81483391144832439114805069)
    ·
      refine ⟨30556271679312164668051901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81483391144832439114805069 30556271679312164668051901)
      ·
        refine ⟨11458601879742061750519463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30556271679312164668051901 11458601879742061750519463)
        ·
          refine ⟨17187902819613092625779195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11458601879742061750519463 17187902819613092625779195)
          ·
            refine ⟨25781854229419638938668793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17187902819613092625779195 25781854229419638938668793)
            ·
              refine ⟨19336390672064729204001595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25781854229419638938668793 19336390672064729204001595)
              ·
                refine ⟨29004586008097093806002393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19336390672064729204001595 29004586008097093806002393)
                ·
                  refine ⟨21753439506072820354501795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29004586008097093806002393 21753439506072820354501795)
                  ·
                    refine ⟨32630159259109230531752693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21753439506072820354501795 32630159259109230531752693)
                    ·
                      refine ⟨3059077430541490362351815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32630159259109230531752693 3059077430541490362351815)
                      ·
                        rfl

theorem cell23_5957532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5957532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957532 prefixEnd_5957532 := by exact prefixLift 5957532
  have htrace : WordTrace (prefixWord ++ tailWord_5957532) baseStart_5957532 baseEnd_5957532 := by
    simpa [prefixWord, tailWord_5957532, baseEnd_5957532] using wordTrace_append hprefix tailTrace_5957532
  have hstable : (prefixWord ++ tailWord_5957532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957532).length < 2 ^ (prefixWord ++ tailWord_5957532).sum := by decide
  have hdescent : baseEnd_5957532 < baseStart_5957532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
