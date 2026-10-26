import V185TrunkScan23Chunk0050

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_301877 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_301877 : Nat := 118140960795 + 301877 * 2 ^ 59
def prefixEnd_301877 : Nat := 4983230072969 + 3 ^ 40 * 301877 * 2
def baseEnd_301877 : Nat := 51669333179140212849733

theorem tailTrace_301877 : CollatzResearch.WordTrace tailWord_301877 prefixEnd_301877 51669333179140212849733 := by
  unfold tailWord_301877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010358727358660332087885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7340239151572440221391923 11010358727358660332087885)
  ·
    refine ⟨4128884522759497624532957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11010358727358660332087885 4128884522759497624532957)
    ·
      refine ⟨1548331696034811609199859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4128884522759497624532957 1548331696034811609199859)
      ·
        refine ⟨2322497544052217413799789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1548331696034811609199859 2322497544052217413799789)
        ·
          refine ⟨870936579019581530174921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2322497544052217413799789 870936579019581530174921)
          ·
            refine ⟨653202434264686147631191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870936579019581530174921 653202434264686147631191)
            ·
              refine ⟨979803651397029221446787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653202434264686147631191 979803651397029221446787)
              ·
                refine ⟨1469705477095543832170181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979803651397029221446787 1469705477095543832170181)
                ·
                  refine ⟨275569776955414468531909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469705477095543832170181 275569776955414468531909)
                  ·
                    refine ⟨51669333179140212849733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 275569776955414468531909 51669333179140212849733)
                    ·
                      rfl

theorem cell23_301877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_301877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301877 prefixEnd_301877 := by exact prefixLift 301877
  have htrace : WordTrace (prefixWord ++ tailWord_301877) baseStart_301877 baseEnd_301877 := by
    simpa [prefixWord, tailWord_301877, baseEnd_301877] using wordTrace_append hprefix tailTrace_301877
  have hstable : (prefixWord ++ tailWord_301877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301877).length < 2 ^ (prefixWord ++ tailWord_301877).sum := by decide
  have hdescent : baseEnd_301877 < baseStart_301877 := by decide
  rcases family_descends (prefixWord ++ tailWord_301877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301893 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_301893 : Nat := 118140960795 + 301893 * 2 ^ 59
def prefixEnd_301893 : Nat := 4983230072969 + 3 ^ 40 * 301893 * 2
def baseEnd_301893 : Nat := 155016215227892575949125

theorem tailTrace_301893 : CollatzResearch.WordTrace tailWord_301893 prefixEnd_301893 155016215227892575949125 := by
  unfold tailWord_301893
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010942295300695064670333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7340628196867130043113555 11010942295300695064670333)
  ·
    refine ⟨4129103360737760649251375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11010942295300695064670333 4129103360737760649251375)
    ·
      refine ⟨6193655041106640973877063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129103360737760649251375 6193655041106640973877063)
      ·
        refine ⟨9290482561659961460815595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6193655041106640973877063 9290482561659961460815595)
        ·
          refine ⟨13935723842489942191223393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9290482561659961460815595 13935723842489942191223393)
          ·
            refine ⟨10451792881867456643417545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13935723842489942191223393 10451792881867456643417545)
            ·
              refine ⟨7838844661400592482563159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10451792881867456643417545 7838844661400592482563159)
              ·
                refine ⟨11758266992100888723844739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7838844661400592482563159 11758266992100888723844739)
                ·
                  refine ⟨17637400488151333085767109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11758266992100888723844739 17637400488151333085767109)
                  ·
                    refine ⟨3307012591528374953581333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17637400488151333085767109 3307012591528374953581333)
                    ·
                      refine ⟨155016215227892575949125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3307012591528374953581333 155016215227892575949125)
                      ·
                        rfl

theorem cell23_301893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_301893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301893 prefixEnd_301893 := by exact prefixLift 301893
  have htrace : WordTrace (prefixWord ++ tailWord_301893) baseStart_301893 baseEnd_301893 := by
    simpa [prefixWord, tailWord_301893, baseEnd_301893] using wordTrace_append hprefix tailTrace_301893
  have hstable : (prefixWord ++ tailWord_301893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301893).length < 2 ^ (prefixWord ++ tailWord_301893).sum := by decide
  have hdescent : baseEnd_301893 < baseStart_301893 := by decide
  rcases family_descends (prefixWord ++ tailWord_301893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301897 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 4]
def baseStart_301897 : Nat := 118140960795 + 301897 * 2 ^ 59
def prefixEnd_301897 : Nat := 4983230072969 + 3 ^ 40 * 301897 * 2
def baseEnd_301897 : Nat := 155018269150510560299107

theorem tailTrace_301897 : CollatzResearch.WordTrace tailWord_301897 prefixEnd_301897 155018269150510560299107 := by
  unfold tailWord_301897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011088187286203747815945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7340725458190802498543963 11011088187286203747815945)
  ·
    refine ⟨8258316140464652810861959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11011088187286203747815945 8258316140464652810861959)
    ·
      refine ⟨12387474210696979216292939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8258316140464652810861959 12387474210696979216292939)
      ·
        refine ⟨18581211316045468824439409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12387474210696979216292939 18581211316045468824439409)
        ·
          refine ⟨13935908487034101618329557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18581211316045468824439409 13935908487034101618329557)
          ·
            refine ⟨326622855164861756679599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13935908487034101618329557 326622855164861756679599)
            ·
              refine ⟨489934282747292635019399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326622855164861756679599 489934282747292635019399)
              ·
                refine ⟨734901424120938952529099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489934282747292635019399 734901424120938952529099)
                ·
                  refine ⟨1102352136181408428793649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734901424120938952529099 1102352136181408428793649)
                  ·
                    refine ⟨826764102136056321595237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102352136181408428793649 826764102136056321595237)
                    ·
                      refine ⟨155018269150510560299107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 826764102136056321595237 155018269150510560299107)
                      ·
                        rfl

theorem cell23_301897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_301897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301897 prefixEnd_301897 := by exact prefixLift 301897
  have htrace : WordTrace (prefixWord ++ tailWord_301897) baseStart_301897 baseEnd_301897 := by
    simpa [prefixWord, tailWord_301897, baseEnd_301897] using wordTrace_append hprefix tailTrace_301897
  have hstable : (prefixWord ++ tailWord_301897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301897).length < 2 ^ (prefixWord ++ tailWord_301897).sum := by decide
  have hdescent : baseEnd_301897 < baseStart_301897 := by decide
  rcases family_descends (prefixWord ++ tailWord_301897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301901 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_301901 : Nat := 118140960795 + 301901 * 2 ^ 59
def prefixEnd_301901 : Nat := 4983230072969 + 3 ^ 40 * 301901 * 2
def baseEnd_301901 : Nat := 155020323073128544649089

theorem tailTrace_301901 : CollatzResearch.WordTrace tailWord_301901 prefixEnd_301901 155020323073128544649089 := by
  unfold tailWord_301901
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011234079271712430961557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7340822719514474953974371 11011234079271712430961557)
  ·
    refine ⟨516151597465861520201323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11011234079271712430961557 516151597465861520201323)
    ·
      refine ⟨774227396198792280301985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516151597465861520201323 774227396198792280301985)
      ·
        refine ⟨580670547149094210226489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774227396198792280301985 580670547149094210226489)
        ·
          refine ⟨435502910361820657669867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580670547149094210226489 435502910361820657669867)
          ·
            refine ⟨653254365542730986504801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435502910361820657669867 653254365542730986504801)
            ·
              refine ⟨489940774157048239878601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653254365542730986504801 489940774157048239878601)
              ·
                refine ⟨367455580617786179908951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489940774157048239878601 367455580617786179908951)
                ·
                  refine ⟨551183370926679269863427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367455580617786179908951 551183370926679269863427)
                  ·
                    refine ⟨826775056390018904795141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551183370926679269863427 826775056390018904795141)
                    ·
                      refine ⟨155020323073128544649089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 826775056390018904795141 155020323073128544649089)
                      ·
                        rfl

theorem cell23_301901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_301901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301901 prefixEnd_301901 := by exact prefixLift 301901
  have htrace : WordTrace (prefixWord ++ tailWord_301901) baseStart_301901 baseEnd_301901 := by
    simpa [prefixWord, tailWord_301901, baseEnd_301901] using wordTrace_append hprefix tailTrace_301901
  have hstable : (prefixWord ++ tailWord_301901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301901).length < 2 ^ (prefixWord ++ tailWord_301901).sum := by decide
  have hdescent : baseEnd_301901 < baseStart_301901 := by decide
  rcases family_descends (prefixWord ++ tailWord_301901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301961 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 1, 3, 2]
def baseStart_301961 : Nat := 118140960795 + 301961 * 2 ^ 59
def prefixEnd_301961 : Nat := 4983230072969 + 3 ^ 40 * 301961 * 2
def baseEnd_301961 : Nat := 155051131912398309898813

theorem tailTrace_301961 : CollatzResearch.WordTrace tailWord_301961 prefixEnd_301961 155051131912398309898813 := by
  unfold tailWord_301961
  simp only [CollatzResearch.WordTrace]
  refine ⟨11013422459054342678145737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7342281639369561785430491 11013422459054342678145737)
  ·
    refine ⟨8260066844290757008609303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11013422459054342678145737 8260066844290757008609303)
    ·
      refine ⟨12390100266436135512913955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8260066844290757008609303 12390100266436135512913955)
      ·
        refine ⟨18585150399654203269370933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12390100266436135512913955 18585150399654203269370933)
        ·
          refine ⟨1742357849967581556503525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18585150399654203269370933 1742357849967581556503525)
          ·
            refine ⟨326692096868921541844411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1742357849967581556503525 326692096868921541844411)
            ·
              refine ⟨490038145303382312766617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326692096868921541844411 490038145303382312766617)
              ·
                refine ⟨367528608977536734574963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490038145303382312766617 367528608977536734574963)
                ·
                  refine ⟨551292913466305101862445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367528608977536734574963 551292913466305101862445)
                  ·
                    refine ⟨206734842549864413198417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551292913466305101862445 206734842549864413198417)
                    ·
                      refine ⟨155051131912398309898813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206734842549864413198417 155051131912398309898813)
                      ·
                        rfl

theorem cell23_301961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 3, 2].length) (baseStart_301961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301961 prefixEnd_301961 := by exact prefixLift 301961
  have htrace : WordTrace (prefixWord ++ tailWord_301961) baseStart_301961 baseEnd_301961 := by
    simpa [prefixWord, tailWord_301961, baseEnd_301961] using wordTrace_append hprefix tailTrace_301961
  have hstable : (prefixWord ++ tailWord_301961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301961).length < 2 ^ (prefixWord ++ tailWord_301961).sum := by decide
  have hdescent : baseEnd_301961 < baseStart_301961 := by decide
  rcases family_descends (prefixWord ++ tailWord_301961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301978 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2]
def baseStart_301978 : Nat := 118140960795 + 301978 * 2 ^ 59
def prefixEnd_301978 : Nat := 4983230072969 + 3 ^ 40 * 301978 * 2
def baseEnd_301978 : Nat := 155059861083524743386235

theorem tailTrace_301978 : CollatzResearch.WordTrace tailWord_301978 prefixEnd_301978 155059861083524743386235 := by
  unfold tailWord_301978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753510624998188645378647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7342694999995169721009725 2753510624998188645378647)
  ·
    refine ⟨4130265937497282968067971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2753510624998188645378647 4130265937497282968067971)
    ·
      refine ⟨6195398906245924452101957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4130265937497282968067971 6195398906245924452101957)
      ·
        refine ⟨1161637294921110834769117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6195398906245924452101957 1161637294921110834769117)
        ·
          refine ⟨435613985595416563038419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1161637294921110834769117 435613985595416563038419)
          ·
            refine ⟨653420978393124844557629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435613985595416563038419 653420978393124844557629)
            ·
              refine ⟨245032866897421816709111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653420978393124844557629 245032866897421816709111)
              ·
                refine ⟨367549300346132725063667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245032866897421816709111 367549300346132725063667)
                ·
                  refine ⟨551323950519199087595501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367549300346132725063667 551323950519199087595501)
                  ·
                    refine ⟨206746481444699657848313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551323950519199087595501 206746481444699657848313)
                    ·
                      refine ⟨155059861083524743386235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206746481444699657848313 155059861083524743386235)
                      ·
                        rfl

theorem cell23_301978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_301978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301978 prefixEnd_301978 := by exact prefixLift 301978
  have htrace : WordTrace (prefixWord ++ tailWord_301978) baseStart_301978 baseEnd_301978 := by
    simpa [prefixWord, tailWord_301978, baseEnd_301978] using wordTrace_append hprefix tailTrace_301978
  have hstable : (prefixWord ++ tailWord_301978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301978).length < 2 ^ (prefixWord ++ tailWord_301978).sum := by decide
  have hdescent : baseEnd_301978 < baseStart_301978 := by decide
  rcases family_descends (prefixWord ++ tailWord_301978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302004 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_302004 : Nat := 118140960795 + 302004 * 2 ^ 59
def prefixEnd_302004 : Nat := 4983230072969 + 3 ^ 40 * 302004 * 2
def baseEnd_302004 : Nat := 155073211580541641661115

theorem tailTrace_302004 : CollatzResearch.WordTrace tailWord_302004 prefixEnd_302004 155073211580541641661115 := by
  unfold tailWord_302004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507495398949280510980533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7343327198599040681307377 5507495398949280510980533)
  ·
    refine ⟨516327693651495047904425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5507495398949280510980533 516327693651495047904425)
    ·
      refine ⟨387245770238621285928319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 516327693651495047904425 387245770238621285928319)
      ·
        refine ⟨580868655357931928892479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387245770238621285928319 580868655357931928892479)
        ·
          refine ⟨871302983036897893338719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580868655357931928892479 871302983036897893338719)
          ·
            refine ⟨1306954474555346840008079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871302983036897893338719 1306954474555346840008079)
            ·
              refine ⟨1960431711833020260012119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306954474555346840008079 1960431711833020260012119)
              ·
                refine ⟨2940647567749530390018179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960431711833020260012119 2940647567749530390018179)
                ·
                  refine ⟨4410971351624295585027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940647567749530390018179 4410971351624295585027269)
                  ·
                    refine ⟨827057128429555422192613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410971351624295585027269 827057128429555422192613)
                    ·
                      refine ⟨155073211580541641661115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 827057128429555422192613 155073211580541641661115)
                      ·
                        rfl

theorem cell23_302004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_302004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302004 prefixEnd_302004 := by exact prefixLift 302004
  have htrace : WordTrace (prefixWord ++ tailWord_302004) baseStart_302004 baseEnd_302004 := by
    simpa [prefixWord, tailWord_302004, baseEnd_302004] using wordTrace_append hprefix tailTrace_302004
  have hstable : (prefixWord ++ tailWord_302004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302004).length < 2 ^ (prefixWord ++ tailWord_302004).sum := by decide
  have hdescent : baseEnd_302004 < baseStart_302004 := by decide
  rcases family_descends (prefixWord ++ tailWord_302004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302010 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_302010 : Nat := 118140960795 + 302010 * 2 ^ 59
def prefixEnd_302010 : Nat := 4983230072969 + 3 ^ 40 * 302010 * 2
def baseEnd_302010 : Nat := 51692097488156206062029

theorem tailTrace_302010 : CollatzResearch.WordTrace tailWord_302010 prefixEnd_302010 51692097488156206062029 := by
  unfold tailWord_302010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753802408969206011669871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7343473090584549364452989 2753802408969206011669871)
  ·
    refine ⟨4130703613453809017504807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2753802408969206011669871 4130703613453809017504807)
    ·
      refine ⟨6196055420180713526257211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4130703613453809017504807 6196055420180713526257211)
      ·
        refine ⟨9294083130271070289385817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196055420180713526257211 9294083130271070289385817)
        ·
          refine ⟨6970562347703302717039363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294083130271070289385817 6970562347703302717039363)
          ·
            refine ⟨10455843521554954075559045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970562347703302717039363 10455843521554954075559045)
            ·
              refine ⟨1960470660291553889167321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10455843521554954075559045 1960470660291553889167321)
              ·
                refine ⟨1470352995218665416875491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960470660291553889167321 1470352995218665416875491)
                ·
                  refine ⟨2205529492827998125313237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470352995218665416875491 2205529492827998125313237)
                  ·
                    refine ⟨51692097488156206062029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2205529492827998125313237 51692097488156206062029)
                    ·
                      rfl

theorem cell23_302010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_302010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302010 prefixEnd_302010 := by exact prefixLift 302010
  have htrace : WordTrace (prefixWord ++ tailWord_302010) baseStart_302010 baseEnd_302010 := by
    simpa [prefixWord, tailWord_302010, baseEnd_302010] using wordTrace_append hprefix tailTrace_302010
  have hstable : (prefixWord ++ tailWord_302010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302010).length < 2 ^ (prefixWord ++ tailWord_302010).sum := by decide
  have hdescent : baseEnd_302010 < baseStart_302010 := by decide
  rcases family_descends (prefixWord ++ tailWord_302010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302027 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 2, 5]
def baseStart_302027 : Nat := 118140960795 + 302027 * 2 ^ 59
def prefixEnd_302027 : Nat := 4983230072969 + 3 ^ 40 * 302027 * 2
def baseEnd_302027 : Nat := 51695007211865017224503

theorem tailTrace_302027 : CollatzResearch.WordTrace tailWord_302027 prefixEnd_302027 51695007211865017224503 := by
  unfold tailWord_302027
  simp only [CollatzResearch.WordTrace]
  refine ⟨11015829676815235950048335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7343886451210157300032223 11015829676815235950048335)
  ·
    refine ⟨16523744515222853925072503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11015829676815235950048335 16523744515222853925072503)
    ·
      refine ⟨24785616772834280887608755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16523744515222853925072503 24785616772834280887608755)
      ·
        refine ⟨37178425159251421331413133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24785616772834280887608755 37178425159251421331413133)
        ·
          refine ⟨13941909434719282999279925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37178425159251421331413133 13941909434719282999279925)
          ·
            refine ⟨1307054009504932781182493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13941909434719282999279925 1307054009504932781182493)
            ·
              refine ⟨490145253564349792943435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1307054009504932781182493 490145253564349792943435)
              ·
                refine ⟨735217880346524689415153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490145253564349792943435 735217880346524689415153)
                ·
                  refine ⟨551413410259893517061365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 735217880346524689415153 551413410259893517061365)
                  ·
                    refine ⟨51695007211865017224503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 551413410259893517061365 51695007211865017224503)
                    ·
                      rfl

theorem cell23_302027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 5].length) (baseStart_302027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302027 prefixEnd_302027 := by exact prefixLift 302027
  have htrace : WordTrace (prefixWord ++ tailWord_302027) baseStart_302027 baseEnd_302027 := by
    simpa [prefixWord, tailWord_302027, baseEnd_302027] using wordTrace_append hprefix tailTrace_302027
  have hstable : (prefixWord ++ tailWord_302027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302027).length < 2 ^ (prefixWord ++ tailWord_302027).sum := by decide
  have hdescent : baseEnd_302027 < baseStart_302027 := by decide
  rcases family_descends (prefixWord ++ tailWord_302027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302029 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_302029 : Nat := 118140960795 + 302029 * 2 ^ 59
def prefixEnd_302029 : Nat := 4983230072969 + 3 ^ 40 * 302029 * 2
def baseEnd_302029 : Nat := 155086048596904043848501

theorem tailTrace_302029 : CollatzResearch.WordTrace tailWord_302029 prefixEnd_302029 155086048596904043848501 := by
  unfold tailWord_302029
  simp only [CollatzResearch.WordTrace]
  refine ⟨11015902622807990291621141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7343935081871993527747427 11015902622807990291621141)
  ·
    refine ⟨516370435444124544919741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11015902622807990291621141 516370435444124544919741)
    ·
      refine ⟨193638913291546704344903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 516370435444124544919741 193638913291546704344903)
      ·
        refine ⟨290458369937320056517355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193638913291546704344903 290458369937320056517355)
        ·
          refine ⟨435687554905980084776033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290458369937320056517355 435687554905980084776033)
          ·
            refine ⟨326765666179485063582025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435687554905980084776033 326765666179485063582025)
            ·
              refine ⟨245074249634613797686519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326765666179485063582025 245074249634613797686519)
              ·
                refine ⟨367611374451920696529779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245074249634613797686519 367611374451920696529779)
                ·
                  refine ⟨551417061677881044794669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367611374451920696529779 551417061677881044794669)
                  ·
                    refine ⟨206781398129205391798001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551417061677881044794669 206781398129205391798001)
                    ·
                      refine ⟨155086048596904043848501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206781398129205391798001 155086048596904043848501)
                      ·
                        rfl

theorem cell23_302029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_302029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302029 prefixEnd_302029 := by exact prefixLift 302029
  have htrace : WordTrace (prefixWord ++ tailWord_302029) baseStart_302029 baseEnd_302029 := by
    simpa [prefixWord, tailWord_302029, baseEnd_302029] using wordTrace_append hprefix tailTrace_302029
  have hstable : (prefixWord ++ tailWord_302029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302029).length < 2 ^ (prefixWord ++ tailWord_302029).sum := by decide
  have hdescent : baseEnd_302029 < baseStart_302029 := by decide
  rcases family_descends (prefixWord ++ tailWord_302029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302091 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 1, 4]
def baseStart_302091 : Nat := 118140960795 + 302091 * 2 ^ 59
def prefixEnd_302091 : Nat := 4983230072969 + 3 ^ 40 * 302091 * 2
def baseEnd_302091 : Nat := 51705961465827600424405

theorem tailTrace_302091 : CollatzResearch.WordTrace tailWord_302091 prefixEnd_302091 51705961465827600424405 := by
  unfold tailWord_302091
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018163948583374880378127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7345442632388916586918751 11018163948583374880378127)
  ·
    refine ⟨16527245922875062320567191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11018163948583374880378127 16527245922875062320567191)
    ·
      refine ⟨24790868884312593480850787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16527245922875062320567191 24790868884312593480850787)
      ·
        refine ⟨37186303326468890221276181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24790868884312593480850787 37186303326468890221276181)
        ·
          refine ⟨1743107968428229229122321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37186303326468890221276181 1743107968428229229122321)
          ·
            refine ⟨1307330976321171921841741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743107968428229229122321 1307330976321171921841741)
            ·
              refine ⟨490249116120439470690653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1307330976321171921841741 490249116120439470690653)
              ·
                refine ⟨183843418545164801508995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 490249116120439470690653 183843418545164801508995)
                ·
                  refine ⟨275765127817747202263493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183843418545164801508995 275765127817747202263493)
                  ·
                    refine ⟨51705961465827600424405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 275765127817747202263493 51705961465827600424405)
                    ·
                      rfl

theorem cell23_302091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 4].length) (baseStart_302091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302091 prefixEnd_302091 := by exact prefixLift 302091
  have htrace : WordTrace (prefixWord ++ tailWord_302091) baseStart_302091 baseEnd_302091 := by
    simpa [prefixWord, tailWord_302091, baseEnd_302091] using wordTrace_append hprefix tailTrace_302091
  have hstable : (prefixWord ++ tailWord_302091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302091).length < 2 ^ (prefixWord ++ tailWord_302091).sum := by decide
  have hdescent : baseEnd_302091 < baseStart_302091 := by decide
  rcases family_descends (prefixWord ++ tailWord_302091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302108 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_302108 : Nat := 118140960795 + 302108 * 2 ^ 59
def prefixEnd_302108 : Nat := 4983230072969 + 3 ^ 40 * 302108 * 2
def baseEnd_302108 : Nat := 51708871189536411586879

theorem tailTrace_302108 : CollatzResearch.WordTrace tailWord_302108 prefixEnd_302108 51708871189536411586879 := by
  unfold tailWord_302108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509391994760893391873489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7345855993014524522497985 5509391994760893391873489)
  ·
    refine ⟨4132043996070670043905117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5509391994760893391873489 4132043996070670043905117)
    ·
      refine ⟨1549516498526501266464419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4132043996070670043905117 1549516498526501266464419)
      ·
        refine ⟨2324274747789751899696629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549516498526501266464419 2324274747789751899696629)
        ·
          refine ⟨217900757605289240596559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2324274747789751899696629 217900757605289240596559)
          ·
            refine ⟨326851136407933860894839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217900757605289240596559 326851136407933860894839)
            ·
              refine ⟨490276704611900791342259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326851136407933860894839 490276704611900791342259)
              ·
                refine ⟨735415056917851187013389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490276704611900791342259 735415056917851187013389)
                ·
                  refine ⟨275780646344194195130021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735415056917851187013389 275780646344194195130021)
                  ·
                    refine ⟨51708871189536411586879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 275780646344194195130021 51708871189536411586879)
                    ·
                      rfl

theorem cell23_302108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_302108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302108 prefixEnd_302108 := by exact prefixLift 302108
  have htrace : WordTrace (prefixWord ++ tailWord_302108) baseStart_302108 baseEnd_302108 := by
    simpa [prefixWord, tailWord_302108, baseEnd_302108] using wordTrace_append hprefix tailTrace_302108
  have hstable : (prefixWord ++ tailWord_302108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302108).length < 2 ^ (prefixWord ++ tailWord_302108).sum := by decide
  have hdescent : baseEnd_302108 < baseStart_302108 := by decide
  rcases family_descends (prefixWord ++ tailWord_302108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302117 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_302117 : Nat := 118140960795 + 302117 * 2 ^ 59
def prefixEnd_302117 : Nat := 4983230072969 + 3 ^ 40 * 302117 * 2
def baseEnd_302117 : Nat := 51710411631499899849365

theorem tailTrace_302117 : CollatzResearch.WordTrace tailWord_302117 prefixEnd_302117 51710411631499899849365 := by
  unfold tailWord_302117
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019112246489181320824605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7346074830992787547216403 11019112246489181320824605)
  ·
    refine ⟨4132167092433442995309227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11019112246489181320824605 4132167092433442995309227)
    ·
      refine ⟨6198250638650164492963841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132167092433442995309227 6198250638650164492963841)
      ·
        refine ⟨4648687978987623369722881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6198250638650164492963841 4648687978987623369722881)
        ·
          refine ⟨3486515984240717527292161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4648687978987623369722881 3486515984240717527292161)
          ·
            refine ⟨2614886988180538145469121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3486515984240717527292161 2614886988180538145469121)
            ·
              refine ⟨1961165241135403609101841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614886988180538145469121 1961165241135403609101841)
              ·
                refine ⟨1470873930851552706826381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961165241135403609101841 1470873930851552706826381)
                ·
                  refine ⟨551577724069332265059893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1470873930851552706826381 551577724069332265059893)
                  ·
                    refine ⟨51710411631499899849365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 551577724069332265059893 51710411631499899849365)
                    ·
                      rfl

theorem cell23_302117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_302117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302117 prefixEnd_302117 := by exact prefixLift 302117
  have htrace : WordTrace (prefixWord ++ tailWord_302117) baseStart_302117 baseEnd_302117 := by
    simpa [prefixWord, tailWord_302117, baseEnd_302117] using wordTrace_append hprefix tailTrace_302117
  have hstable : (prefixWord ++ tailWord_302117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302117).length < 2 ^ (prefixWord ++ tailWord_302117).sum := by decide
  have hdescent : baseEnd_302117 < baseStart_302117 := by decide
  rcases family_descends (prefixWord ++ tailWord_302117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302124 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 4, 3, 2]
def baseStart_302124 : Nat := 118140960795 + 302124 * 2 ^ 59
def prefixEnd_302124 : Nat := 4983230072969 + 3 ^ 40 * 302124 * 2
def baseEnd_302124 : Nat := 155134829259081172160563

theorem tailTrace_302124 : CollatzResearch.WordTrace tailWord_302124 prefixEnd_302124 155134829259081172160563 := by
  unfold tailWord_302124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509683778731910758164713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7346245038309214344219617 5509683778731910758164713)
  ·
    refine ⟨4132262834048933068623535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5509683778731910758164713 4132262834048933068623535)
    ·
      refine ⟨6198394251073399602935303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132262834048933068623535 6198394251073399602935303)
      ·
        refine ⟨9297591376610099404402955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198394251073399602935303 9297591376610099404402955)
        ·
          refine ⟨13946387064915149106604433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9297591376610099404402955 13946387064915149106604433)
          ·
            refine ⟨10459790298686361829953325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13946387064915149106604433 10459790298686361829953325)
            ·
              refine ⟨3922421362007385686232497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10459790298686361829953325 3922421362007385686232497)
              ·
                refine ⟨2941816021505539264674373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3922421362007385686232497 2941816021505539264674373)
                ·
                  refine ⟨551590504032288612126445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2941816021505539264674373 551590504032288612126445)
                  ·
                    refine ⟨206846439012108229547417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551590504032288612126445 206846439012108229547417)
                    ·
                      refine ⟨155134829259081172160563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206846439012108229547417 155134829259081172160563)
                      ·
                        rfl

theorem cell23_302124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_302124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302124 prefixEnd_302124 := by exact prefixLift 302124
  have htrace : WordTrace (prefixWord ++ tailWord_302124) baseStart_302124 baseEnd_302124 := by
    simpa [prefixWord, tailWord_302124, baseEnd_302124] using wordTrace_append hprefix tailTrace_302124
  have hstable : (prefixWord ++ tailWord_302124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302124).length < 2 ^ (prefixWord ++ tailWord_302124).sum := by decide
  have hdescent : baseEnd_302124 < baseStart_302124 := by decide
  rcases family_descends (prefixWord ++ tailWord_302124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302141 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_302141 : Nat := 118140960795 + 302141 * 2 ^ 59
def prefixEnd_302141 : Nat := 4983230072969 + 3 ^ 40 * 302141 * 2
def baseEnd_302141 : Nat := 155143558430207605647985

theorem tailTrace_302141 : CollatzResearch.WordTrace tailWord_302141 prefixEnd_302141 155143558430207605647985 := by
  unfold tailWord_302141
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019987598402233419698277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7346658398934822279798851 11019987598402233419698277)
  ·
    refine ⟨2066247674700418766193427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11019987598402233419698277 2066247674700418766193427)
    ·
      refine ⟨3099371512050628149290141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066247674700418766193427 3099371512050628149290141)
      ·
        refine ⟨1162264317018985555983803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3099371512050628149290141 1162264317018985555983803)
        ·
          refine ⟨1743396475528478333975705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162264317018985555983803 1743396475528478333975705)
          ·
            refine ⟨1307547356646358750481779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743396475528478333975705 1307547356646358750481779)
            ·
              refine ⟨1961321034969538125722669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307547356646358750481779 1961321034969538125722669)
              ·
                refine ⟨735495388113576797146001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1961321034969538125722669 735495388113576797146001)
                ·
                  refine ⟨551621541085182597859501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 735495388113576797146001 551621541085182597859501)
                  ·
                    refine ⟨206858077906943474197313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551621541085182597859501 206858077906943474197313)
                    ·
                      refine ⟨155143558430207605647985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206858077906943474197313 155143558430207605647985)
                      ·
                        rfl

theorem cell23_302141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_302141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302141 prefixEnd_302141 := by exact prefixLift 302141
  have htrace : WordTrace (prefixWord ++ tailWord_302141) baseStart_302141 baseEnd_302141 := by
    simpa [prefixWord, tailWord_302141, baseEnd_302141] using wordTrace_append hprefix tailTrace_302141
  have hstable : (prefixWord ++ tailWord_302141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302141).length < 2 ^ (prefixWord ++ tailWord_302141).sum := by decide
  have hdescent : baseEnd_302141 < baseStart_302141 := by decide
  rcases family_descends (prefixWord ++ tailWord_302141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302147 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 1, 6]
def baseStart_302147 : Nat := 118140960795 + 302147 * 2 ^ 59
def prefixEnd_302147 : Nat := 4983230072969 + 3 ^ 40 * 302147 * 2
def baseEnd_302147 : Nat := 51715546438044860724319

theorem tailTrace_302147 : CollatzResearch.WordTrace tailWord_302147 prefixEnd_302147 51715546438044860724319 := by
  unfold tailWord_302147
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020206436380496444416695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7346804290920330962944463 11020206436380496444416695)
  ·
    refine ⟨16530309654570744666625043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11020206436380496444416695 16530309654570744666625043)
    ·
      refine ⟨24795464481856116999937565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16530309654570744666625043 24795464481856116999937565)
      ·
        refine ⟨9298299180696043874976587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24795464481856116999937565 9298299180696043874976587)
        ·
          refine ⟨13947448771044065812464881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9298299180696043874976587 13947448771044065812464881)
          ·
            refine ⟨10460586578283049359348661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13947448771044065812464881 10460586578283049359348661)
            ·
              refine ⟨980679991714035877438937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10460586578283049359348661 980679991714035877438937)
              ·
                refine ⟨735509993785526908079203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980679991714035877438937 735509993785526908079203)
                ·
                  refine ⟨1103264990678290362118805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735509993785526908079203 1103264990678290362118805)
                  ·
                    refine ⟨51715546438044860724319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1103264990678290362118805 51715546438044860724319)
                    ·
                      rfl

theorem cell23_302147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 6].length) (baseStart_302147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302147 prefixEnd_302147 := by exact prefixLift 302147
  have htrace : WordTrace (prefixWord ++ tailWord_302147) baseStart_302147 baseEnd_302147 := by
    simpa [prefixWord, tailWord_302147, baseEnd_302147] using wordTrace_append hprefix tailTrace_302147
  have hstable : (prefixWord ++ tailWord_302147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302147).length < 2 ^ (prefixWord ++ tailWord_302147).sum := by decide
  have hdescent : baseEnd_302147 < baseStart_302147 := by decide
  rcases family_descends (prefixWord ++ tailWord_302147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302151 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 1, 5]
def baseStart_302151 : Nat := 118140960795 + 302151 * 2 ^ 59
def prefixEnd_302151 : Nat := 4983230072969 + 3 ^ 40 * 302151 * 2
def baseEnd_302151 : Nat := 51716231078917522174313

theorem tailTrace_302151 : CollatzResearch.WordTrace tailWord_302151 prefixEnd_302151 51716231078917522174313 := by
  unfold tailWord_302151
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020352328366005127562307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7346901552244003418374871 11020352328366005127562307)
  ·
    refine ⟨16530528492549007691343461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11020352328366005127562307 16530528492549007691343461)
    ·
      refine ⟨3099474092352938942126899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16530528492549007691343461 3099474092352938942126899)
      ·
        refine ⟨4649211138529408413190349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099474092352938942126899 4649211138529408413190349)
        ·
          refine ⟨1743454176948528154946381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4649211138529408413190349 1743454176948528154946381)
          ·
            refine ⟨653795316355698058104893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1743454176948528154946381 653795316355698058104893)
            ·
              refine ⟨245173243633386771789335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653795316355698058104893 245173243633386771789335)
              ·
                refine ⟨367759865450080157684003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245173243633386771789335 367759865450080157684003)
                ·
                  refine ⟨551639798175120236526005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367759865450080157684003 551639798175120236526005)
                  ·
                    refine ⟨51716231078917522174313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 551639798175120236526005 51716231078917522174313)
                    ·
                      rfl

theorem cell23_302151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_302151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302151 prefixEnd_302151 := by exact prefixLift 302151
  have htrace : WordTrace (prefixWord ++ tailWord_302151) baseStart_302151 baseEnd_302151 := by
    simpa [prefixWord, tailWord_302151, baseEnd_302151] using wordTrace_append hprefix tailTrace_302151
  have hstable : (prefixWord ++ tailWord_302151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302151).length < 2 ^ (prefixWord ++ tailWord_302151).sum := by decide
  have hdescent : baseEnd_302151 < baseStart_302151 := by decide
  rcases family_descends (prefixWord ++ tailWord_302151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302154 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_302154 : Nat := 118140960795 + 302154 * 2 ^ 59
def prefixEnd_302154 : Nat := 4983230072969 + 3 ^ 40 * 302154 * 2
def baseEnd_302154 : Nat := 155150233678716054785425

theorem tailTrace_302154 : CollatzResearch.WordTrace tailWord_302154 prefixEnd_302154 155150233678716054785425 := by
  unfold tailWord_302154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755115436838784159980379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7346974498236757759947677 2755115436838784159980379)
  ·
    refine ⟨4132673155258176239970569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755115436838784159980379 4132673155258176239970569)
    ·
      refine ⟨3099504866443632179977927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4132673155258176239970569 3099504866443632179977927)
      ·
        refine ⟨4649257299665448269966891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099504866443632179977927 4649257299665448269966891)
        ·
          refine ⟨6973885949498172404950337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649257299665448269966891 6973885949498172404950337)
          ·
            refine ⟨5230414462123629303712753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6973885949498172404950337 5230414462123629303712753)
            ·
              refine ⟨3922810846592721977784565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230414462123629303712753 3922810846592721977784565)
              ·
                refine ⟨367763516868067685417303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3922810846592721977784565 367763516868067685417303)
                ·
                  refine ⟨551645275302101528125955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367763516868067685417303 551645275302101528125955)
                  ·
                    refine ⟨827467912953152292188933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551645275302101528125955 827467912953152292188933)
                    ·
                      refine ⟨155150233678716054785425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 827467912953152292188933 155150233678716054785425)
                      ·
                        rfl

theorem cell23_302154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_302154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302154 prefixEnd_302154 := by exact prefixLift 302154
  have htrace : WordTrace (prefixWord ++ tailWord_302154) baseStart_302154 baseEnd_302154 := by
    simpa [prefixWord, tailWord_302154, baseEnd_302154] using wordTrace_append hprefix tailTrace_302154
  have hstable : (prefixWord ++ tailWord_302154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302154).length < 2 ^ (prefixWord ++ tailWord_302154).sum := by decide
  have hdescent : baseEnd_302154 < baseStart_302154 := by decide
  rcases family_descends (prefixWord ++ tailWord_302154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302164 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_302164 : Nat := 118140960795 + 302164 * 2 ^ 59
def prefixEnd_302164 : Nat := 4983230072969 + 3 ^ 40 * 302164 * 2
def baseEnd_302164 : Nat := 51718456161753671886793

theorem tailTrace_302164 : CollatzResearch.WordTrace tailWord_302164 prefixEnd_302164 51718456161753671886793 := by
  unfold tailWord_302164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510413238659454173892773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7347217651545938898523697 5510413238659454173892773)
  ·
    refine ⟨1033202482248647657604895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5510413238659454173892773 1033202482248647657604895)
    ·
      refine ⟨1549803723372971486407343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033202482248647657604895 1549803723372971486407343)
      ·
        refine ⟨2324705585059457229611015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549803723372971486407343 2324705585059457229611015)
        ·
          refine ⟨3487058377589185844416523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324705585059457229611015 3487058377589185844416523)
          ·
            refine ⟨5230587566383778766624785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487058377589185844416523 5230587566383778766624785)
            ·
              refine ⟨3922940674787834074968589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230587566383778766624785 3922940674787834074968589)
              ·
                refine ⟨1471102753045437778113221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3922940674787834074968589 1471102753045437778113221)
                ·
                  refine ⟨275831766196019583396229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1471102753045437778113221 275831766196019583396229)
                  ·
                    refine ⟨51718456161753671886793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 275831766196019583396229 51718456161753671886793)
                    ·
                      rfl

theorem cell23_302164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_302164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302164 prefixEnd_302164 := by exact prefixLift 302164
  have htrace : WordTrace (prefixWord ++ tailWord_302164) baseStart_302164 baseEnd_302164 := by
    simpa [prefixWord, tailWord_302164, baseEnd_302164] using wordTrace_append hprefix tailTrace_302164
  have hstable : (prefixWord ++ tailWord_302164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302164).length < 2 ^ (prefixWord ++ tailWord_302164).sum := by decide
  have hdescent : baseEnd_302164 < baseStart_302164 := by decide
  rcases family_descends (prefixWord ++ tailWord_302164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302167 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_302167 : Nat := 118140960795 + 302167 * 2 ^ 59
def prefixEnd_302167 : Nat := 4983230072969 + 3 ^ 40 * 302167 * 2
def baseEnd_302167 : Nat := 155156908927224503922865

theorem tailTrace_302167 : CollatzResearch.WordTrace tailWord_302167 prefixEnd_302167 155156908927224503922865 := by
  unfold tailWord_302167
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020935896308039860144755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7347290597538693240096503 11020935896308039860144755)
  ·
    refine ⟨16531403844462059790217133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11020935896308039860144755 16531403844462059790217133)
    ·
      refine ⟨6199276441673272421331425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16531403844462059790217133 6199276441673272421331425)
      ·
        refine ⟨4649457331254954315998569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6199276441673272421331425 4649457331254954315998569)
        ·
          refine ⟨3487092998441215736998927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4649457331254954315998569 3487092998441215736998927)
          ·
            refine ⟨5230639497661823605498391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487092998441215736998927 5230639497661823605498391)
            ·
              refine ⟨7845959246492735408247587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230639497661823605498391 7845959246492735408247587)
              ·
                refine ⟨11768938869739103112371381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7845959246492735408247587 11768938869739103112371381)
                ·
                  refine ⟨1103338019038040916784817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11768938869739103112371381 1103338019038040916784817)
                  ·
                    refine ⟨827503514278530687588613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1103338019038040916784817 827503514278530687588613)
                    ·
                      refine ⟨155156908927224503922865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 827503514278530687588613 155156908927224503922865)
                      ·
                        rfl

theorem cell23_302167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_302167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302167 prefixEnd_302167 := by exact prefixLift 302167
  have htrace : WordTrace (prefixWord ++ tailWord_302167) baseStart_302167 baseEnd_302167 := by
    simpa [prefixWord, tailWord_302167, baseEnd_302167] using wordTrace_append hprefix tailTrace_302167
  have hstable : (prefixWord ++ tailWord_302167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302167).length < 2 ^ (prefixWord ++ tailWord_302167).sum := by decide
  have hdescent : baseEnd_302167 < baseStart_302167 := by decide
  rcases family_descends (prefixWord ++ tailWord_302167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302177 : List Nat := [1, 2, 3, 1, 1, 2, 5, 8]
def baseStart_302177 : Nat := 118140960795 + 302177 * 2 ^ 59
def prefixEnd_302177 : Nat := 4983230072969 + 3 ^ 40 * 302177 * 2
def baseEnd_302177 : Nat := 5746742360509980177697

theorem tailTrace_302177 : CollatzResearch.WordTrace tailWord_302177 prefixEnd_302177 5746742360509980177697 := by
  unfold tailWord_302177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021300626271811568008785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7347533750847874378672523 11021300626271811568008785)
  ·
    refine ⟨8265975469703858676006589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11021300626271811568008785 8265975469703858676006589)
    ·
      refine ⟨3099740801138947003502471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8265975469703858676006589 3099740801138947003502471)
      ·
        refine ⟨4649611201708420505253707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099740801138947003502471 4649611201708420505253707)
        ·
          refine ⟨6974416802562630757880561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649611201708420505253707 6974416802562630757880561)
          ·
            refine ⟨5230812601921973068410421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6974416802562630757880561 5230812601921973068410421)
            ·
              refine ⟨490388681430184975163477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5230812601921973068410421 490388681430184975163477)
              ·
                refine ⟨5746742360509980177697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 490388681430184975163477 5746742360509980177697)
                ·
                  rfl

theorem cell23_302177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 8].length) (baseStart_302177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302177 prefixEnd_302177 := by exact prefixLift 302177
  have htrace : WordTrace (prefixWord ++ tailWord_302177) baseStart_302177 baseEnd_302177 := by
    simpa [prefixWord, tailWord_302177, baseEnd_302177] using wordTrace_append hprefix tailTrace_302177
  have hstable : (prefixWord ++ tailWord_302177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302177).length < 2 ^ (prefixWord ++ tailWord_302177).sum := by decide
  have hdescent : baseEnd_302177 < baseStart_302177 := by decide
  rcases family_descends (prefixWord ++ tailWord_302177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302194 : List Nat := [3, 2, 1, 2, 2, 1, 5, 7]
def baseStart_302194 : Nat := 118140960795 + 302194 * 2 ^ 59
def prefixEnd_302194 : Nat := 4983230072969 + 3 ^ 40 * 302194 * 2
def baseEnd_302194 : Nat := 5747065663144292529083

theorem tailTrace_302194 : CollatzResearch.WordTrace tailWord_302194 prefixEnd_302194 5747065663144292529083 := by
  unfold tailWord_302194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755480166802555867844409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7347947111473482314251757 2755480166802555867844409)
  ·
    refine ⟨2066610125101916900883307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2755480166802555867844409 2066610125101916900883307)
    ·
      refine ⟨3099915187652875351324961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066610125101916900883307 3099915187652875351324961)
      ·
        refine ⟨2324936390739656513493721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3099915187652875351324961 2324936390739656513493721)
        ·
          refine ⟨1743702293054742385120291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324936390739656513493721 1743702293054742385120291)
          ·
            refine ⟨2615553439582113577680437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743702293054742385120291 2615553439582113577680437)
            ·
              refine ⟨245208134960823147907541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2615553439582113577680437 245208134960823147907541)
              ·
                refine ⟨5747065663144292529083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 245208134960823147907541 5747065663144292529083)
                ·
                  rfl

theorem cell23_302194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_302194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302194 prefixEnd_302194 := by exact prefixLift 302194
  have htrace : WordTrace (prefixWord ++ tailWord_302194) baseStart_302194 baseEnd_302194 := by
    simpa [prefixWord, tailWord_302194, baseEnd_302194] using wordTrace_append hprefix tailTrace_302194
  have hstable : (prefixWord ++ tailWord_302194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302194).length < 2 ^ (prefixWord ++ tailWord_302194).sum := by decide
  have hdescent : baseEnd_302194 < baseStart_302194 := by decide
  rcases family_descends (prefixWord ++ tailWord_302194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302204 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_302204 : Nat := 118140960795 + 302204 * 2 ^ 59
def prefixEnd_302204 : Nat := 4983230072969 + 3 ^ 40 * 302204 * 2
def baseEnd_302204 : Nat := 155175907711440859160195

theorem tailTrace_302204 : CollatzResearch.WordTrace tailWord_302204 prefixEnd_302204 155175907711440859160195 := by
  unfold tailWord_302204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511142698586997589620833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7348190264782663452827777 5511142698586997589620833)
  ·
    refine ⟨4133357023940248192215625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5511142698586997589620833 4133357023940248192215625)
    ·
      refine ⟨3100017767955186144161719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4133357023940248192215625 3100017767955186144161719)
      ·
        refine ⟨4650026651932779216242579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100017767955186144161719 4650026651932779216242579)
        ·
          refine ⟨6975039977899168824363869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4650026651932779216242579 6975039977899168824363869)
          ·
            refine ⟨2615639991712188309136451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6975039977899168824363869 2615639991712188309136451)
            ·
              refine ⟨3923459987568282463704677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615639991712188309136451 3923459987568282463704677)
              ·
                refine ⟨735648747669052961944627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3923459987568282463704677 735648747669052961944627)
                ·
                  refine ⟨1103473121503579442916941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735648747669052961944627 1103473121503579442916941)
                  ·
                    refine ⟨413802420563842291093853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103473121503579442916941 413802420563842291093853)
                    ·
                      refine ⟨155175907711440859160195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 413802420563842291093853 155175907711440859160195)
                      ·
                        rfl

theorem cell23_302204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_302204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302204 prefixEnd_302204 := by exact prefixLift 302204
  have htrace : WordTrace (prefixWord ++ tailWord_302204) baseStart_302204 baseEnd_302204 := by
    simpa [prefixWord, tailWord_302204, baseEnd_302204] using wordTrace_append hprefix tailTrace_302204
  have hstable : (prefixWord ++ tailWord_302204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302204).length < 2 ^ (prefixWord ++ tailWord_302204).sum := by decide
  have hdescent : baseEnd_302204 < baseStart_302204 := by decide
  rcases family_descends (prefixWord ++ tailWord_302204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302205 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_302205 : Nat := 118140960795 + 302205 * 2 ^ 59
def prefixEnd_302205 : Nat := 4983230072969 + 3 ^ 40 * 302205 * 2
def baseEnd_302205 : Nat := 155176421192095355247691

theorem tailTrace_302205 : CollatzResearch.WordTrace tailWord_302205 prefixEnd_302205 155176421192095355247691 := by
  unfold tailWord_302205
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022321870170372350028069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7348214580113581566685379 11022321870170372350028069)
  ·
    refine ⟨2066685350656944815630263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11022321870170372350028069 2066685350656944815630263)
    ·
      refine ⟨3100028025985417223445395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066685350656944815630263 3100028025985417223445395)
      ·
        refine ⟨4650042038978125835168093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100028025985417223445395 4650042038978125835168093)
        ·
          refine ⟨1743765764616797188188035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4650042038978125835168093 1743765764616797188188035)
          ·
            refine ⟨2615648646925195782282053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743765764616797188188035 2615648646925195782282053)
            ·
              refine ⟨490434121298474209177885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2615648646925195782282053 490434121298474209177885)
              ·
                refine ⟨183912795486927828441707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 490434121298474209177885 183912795486927828441707)
                ·
                  refine ⟨275869193230391742662561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183912795486927828441707 275869193230391742662561)
                  ·
                    refine ⟨206901894922793806996921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 275869193230391742662561 206901894922793806996921)
                    ·
                      refine ⟨155176421192095355247691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206901894922793806996921 155176421192095355247691)
                      ·
                        rfl

theorem cell23_302205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_302205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302205 prefixEnd_302205 := by exact prefixLift 302205
  have htrace : WordTrace (prefixWord ++ tailWord_302205) baseStart_302205 baseEnd_302205 := by
    simpa [prefixWord, tailWord_302205, baseEnd_302205] using wordTrace_append hprefix tailTrace_302205
  have hstable : (prefixWord ++ tailWord_302205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302205).length < 2 ^ (prefixWord ++ tailWord_302205).sum := by decide
  have hdescent : baseEnd_302205 < baseStart_302205 := by decide
  rcases family_descends (prefixWord ++ tailWord_302205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302227 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4]
def baseStart_302227 : Nat := 118140960795 + 302227 * 2 ^ 59
def prefixEnd_302227 : Nat := 4983230072969 + 3 ^ 40 * 302227 * 2
def baseEnd_302227 : Nat := 155187717766494269172589

theorem tailTrace_302227 : CollatzResearch.WordTrace tailWord_302227 prefixEnd_302227 155187717766494269172589 := by
  unfold tailWord_302227
  simp only [CollatzResearch.WordTrace]
  refine ⟨11023124276090670107328935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7348749517393780071552623 11023124276090670107328935)
  ·
    refine ⟨16534686414136005160993403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11023124276090670107328935 16534686414136005160993403)
    ·
      refine ⟨24802029621204007741490105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16534686414136005160993403 24802029621204007741490105)
      ·
        refine ⟨18601522215903005806117579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24802029621204007741490105 18601522215903005806117579)
        ·
          refine ⟨27902283323854508709176369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18601522215903005806117579 27902283323854508709176369)
          ·
            refine ⟨20926712492890881531882277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27902283323854508709176369 20926712492890881531882277)
            ·
              refine ⟨3923758592417040287227927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20926712492890881531882277 3923758592417040287227927)
              ·
                refine ⟨5885637888625560430841891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923758592417040287227927 5885637888625560430841891)
                ·
                  refine ⟨8828456832938340646262837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885637888625560430841891 8828456832938340646262837)
                  ·
                    refine ⟨827667828087969435587141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8828456832938340646262837 827667828087969435587141)
                    ·
                      refine ⟨155187717766494269172589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 827667828087969435587141 155187717766494269172589)
                      ·
                        rfl

theorem cell23_302227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_302227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302227 prefixEnd_302227 := by exact prefixLift 302227
  have htrace : WordTrace (prefixWord ++ tailWord_302227) baseStart_302227 baseEnd_302227 := by
    simpa [prefixWord, tailWord_302227, baseEnd_302227] using wordTrace_append hprefix tailTrace_302227
  have hstable : (prefixWord ++ tailWord_302227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302227).length < 2 ^ (prefixWord ++ tailWord_302227).sum := by decide
  have hdescent : baseEnd_302227 < baseStart_302227 := by decide
  rcases family_descends (prefixWord ++ tailWord_302227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302238 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_302238 : Nat := 118140960795 + 302238 * 2 ^ 59
def prefixEnd_302238 : Nat := 4983230072969 + 3 ^ 40 * 302238 * 2
def baseEnd_302238 : Nat := 155193366053693726135039

theorem tailTrace_302238 : CollatzResearch.WordTrace tailWord_302238 prefixEnd_302238 155193366053693726135039 := by
  unfold tailWord_302238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377940684881352373247421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7349016986033879323986245 1377940684881352373247421)
  ·
    refine ⟨516727756830507139967783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1377940684881352373247421 516727756830507139967783)
    ·
      refine ⟨775091635245760709951675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516727756830507139967783 775091635245760709951675)
      ·
        refine ⟨1162637452868641064927513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775091635245760709951675 1162637452868641064927513)
        ·
          refine ⟨871978089651480798695635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162637452868641064927513 871978089651480798695635)
          ·
            refine ⟨1307967134477221198043453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871978089651480798695635 1307967134477221198043453)
            ·
              refine ⟨490487675428957949266295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1307967134477221198043453 490487675428957949266295)
              ·
                refine ⟨735731513143436923899443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490487675428957949266295 735731513143436923899443)
                ·
                  refine ⟨1103597269715155385849165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735731513143436923899443 1103597269715155385849165)
                  ·
                    refine ⟨413848976143183269693437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1103597269715155385849165 413848976143183269693437)
                    ·
                      refine ⟨155193366053693726135039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 413848976143183269693437 155193366053693726135039)
                      ·
                        rfl

theorem cell23_302238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_302238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302238 prefixEnd_302238 := by exact prefixLift 302238
  have htrace : WordTrace (prefixWord ++ tailWord_302238) baseStart_302238 baseEnd_302238 := by
    simpa [prefixWord, tailWord_302238, baseEnd_302238] using wordTrace_append hprefix tailTrace_302238
  have hstable : (prefixWord ++ tailWord_302238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302238).length < 2 ^ (prefixWord ++ tailWord_302238).sum := by decide
  have hdescent : baseEnd_302238 < baseStart_302238 := by decide
  rcases family_descends (prefixWord ++ tailWord_302238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302277 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_302277 : Nat := 118140960795 + 302277 * 2 ^ 59
def prefixEnd_302277 : Nat := 4983230072969 + 3 ^ 40 * 302277 * 2
def baseEnd_302277 : Nat := 155213391799219073547359

theorem tailTrace_302277 : CollatzResearch.WordTrace tailWord_302277 prefixEnd_302277 155213391799219073547359 := by
  unfold tailWord_302277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11024947925909528646649085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7349965283939685764432723 11024947925909528646649085)
  ·
    refine ⟨4134355472216073242493407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11024947925909528646649085 4134355472216073242493407)
    ·
      refine ⟨6201533208324109863740111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134355472216073242493407 6201533208324109863740111)
      ·
        refine ⟨9302299812486164795610167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201533208324109863740111 9302299812486164795610167)
        ·
          refine ⟨13953449718729247193415251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9302299812486164795610167 13953449718729247193415251)
          ·
            refine ⟨20930174578093870790122877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13953449718729247193415251 20930174578093870790122877)
            ·
              refine ⟨7848815466785201546296079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20930174578093870790122877 7848815466785201546296079)
              ·
                refine ⟨11773223200177802319444119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848815466785201546296079 11773223200177802319444119)
                ·
                  refine ⟨17659834800266703479166179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11773223200177802319444119 17659834800266703479166179)
                  ·
                    refine ⟨26489752200400055218749269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17659834800266703479166179 26489752200400055218749269)
                    ·
                      refine ⟨155213391799219073547359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 26489752200400055218749269 155213391799219073547359)
                      ·
                        rfl

theorem cell23_302277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_302277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302277 prefixEnd_302277 := by exact prefixLift 302277
  have htrace : WordTrace (prefixWord ++ tailWord_302277) baseStart_302277 baseEnd_302277 := by
    simpa [prefixWord, tailWord_302277, baseEnd_302277] using wordTrace_append hprefix tailTrace_302277
  have hstable : (prefixWord ++ tailWord_302277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302277).length < 2 ^ (prefixWord ++ tailWord_302277).sum := by decide
  have hdescent : baseEnd_302277 < baseStart_302277 := by decide
  rcases family_descends (prefixWord ++ tailWord_302277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302287 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_302287 : Nat := 118140960795 + 302287 * 2 ^ 59
def prefixEnd_302287 : Nat := 4983230072969 + 3 ^ 40 * 302287 * 2
def baseEnd_302287 : Nat := 155218526605764034422313

theorem tailTrace_302287 : CollatzResearch.WordTrace tailWord_302287 prefixEnd_302287 155218526605764034422313 := by
  unfold tailWord_302287
  simp only [CollatzResearch.WordTrace]
  refine ⟨11025312655873300354513115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7350208437248866903008743 11025312655873300354513115)
  ·
    refine ⟨16537968983809950531769673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11025312655873300354513115 16537968983809950531769673)
    ·
      refine ⟨12403476737857462898827255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16537968983809950531769673 12403476737857462898827255)
      ·
        refine ⟨18605215106786194348240883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12403476737857462898827255 18605215106786194348240883)
        ·
          refine ⟨27907822660179291522361325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18605215106786194348240883 27907822660179291522361325)
          ·
            refine ⟨10465433497567234320885497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27907822660179291522361325 10465433497567234320885497)
            ·
              refine ⟨7849075123175425740664123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10465433497567234320885497 7849075123175425740664123)
              ·
                refine ⟨11773612684763138610996185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849075123175425740664123 11773612684763138610996185)
                ·
                  refine ⟨8830209513572353958247139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11773612684763138610996185 8830209513572353958247139)
                  ·
                    refine ⟨13245314270358530937370709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8830209513572353958247139 13245314270358530937370709)
                    ·
                      refine ⟨155218526605764034422313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 13245314270358530937370709 155218526605764034422313)
                      ·
                        rfl

theorem cell23_302287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_302287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302287 prefixEnd_302287 := by exact prefixLift 302287
  have htrace : WordTrace (prefixWord ++ tailWord_302287) baseStart_302287 baseEnd_302287 := by
    simpa [prefixWord, tailWord_302287, baseEnd_302287] using wordTrace_append hprefix tailTrace_302287
  have hstable : (prefixWord ++ tailWord_302287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302287).length < 2 ^ (prefixWord ++ tailWord_302287).sum := by decide
  have hdescent : baseEnd_302287 < baseStart_302287 := by decide
  rcases family_descends (prefixWord ++ tailWord_302287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302295 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 2, 2, 2]
def baseStart_302295 : Nat := 118140960795 + 302295 * 2 ^ 59
def prefixEnd_302295 : Nat := 4983230072969 + 3 ^ 40 * 302295 * 2
def baseEnd_302295 : Nat := 155222634451000003122277

theorem tailTrace_302295 : CollatzResearch.WordTrace tailWord_302295 prefixEnd_302295 155222634451000003122277 := by
  unfold tailWord_302295
  simp only [CollatzResearch.WordTrace]
  refine ⟨11025604439844317720804339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7350402959896211813869559 11025604439844317720804339)
  ·
    refine ⟨16538406659766476581206509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11025604439844317720804339 16538406659766476581206509)
    ·
      refine ⟨6201902497412428717952441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16538406659766476581206509 6201902497412428717952441)
      ·
        refine ⟨4651426873059321538464331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6201902497412428717952441 4651426873059321538464331)
        ·
          refine ⟨6977140309588982307696497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651426873059321538464331 6977140309588982307696497)
          ·
            refine ⟨5232855232191736730772373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6977140309588982307696497 5232855232191736730772373)
            ·
              refine ⟨245290089008987659254955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5232855232191736730772373 245290089008987659254955)
              ·
                refine ⟨367935133513481488882433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245290089008987659254955 367935133513481488882433)
                ·
                  refine ⟨275951350135111116661825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367935133513481488882433 275951350135111116661825)
                  ·
                    refine ⟨206963512601333337496369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 275951350135111116661825 206963512601333337496369)
                    ·
                      refine ⟨155222634451000003122277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206963512601333337496369 155222634451000003122277)
                      ·
                        rfl

theorem cell23_302295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_302295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302295 prefixEnd_302295 := by exact prefixLift 302295
  have htrace : WordTrace (prefixWord ++ tailWord_302295) baseStart_302295 baseEnd_302295 := by
    simpa [prefixWord, tailWord_302295, baseEnd_302295] using wordTrace_append hprefix tailTrace_302295
  have hstable : (prefixWord ++ tailWord_302295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302295).length < 2 ^ (prefixWord ++ tailWord_302295).sum := by decide
  have hdescent : baseEnd_302295 < baseStart_302295 := by decide
  rcases family_descends (prefixWord ++ tailWord_302295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302371 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 3]
def baseStart_302371 : Nat := 118140960795 + 302371 * 2 ^ 59
def prefixEnd_302371 : Nat := 4983230072969 + 3 ^ 40 * 302371 * 2
def baseEnd_302371 : Nat := 155261658980741705771927

theorem tailTrace_302371 : CollatzResearch.WordTrace tailWord_302371 prefixEnd_302371 155261658980741705771927 := by
  unfold tailWord_302371
  simp only [CollatzResearch.WordTrace]
  refine ⟨11028376387568982700570967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7352250925045988467047311 11028376387568982700570967)
  ·
    refine ⟨16542564581353474050856451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11028376387568982700570967 16542564581353474050856451)
    ·
      refine ⟨24813846872030211076284677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16542564581353474050856451 24813846872030211076284677)
      ·
        refine ⟨4652596288505664576803377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24813846872030211076284677 4652596288505664576803377)
        ·
          refine ⟨3489447216379248432602533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4652596288505664576803377 3489447216379248432602533)
          ·
            refine ⟨654271353071109081112975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3489447216379248432602533 654271353071109081112975)
            ·
              refine ⟨981407029606663621669463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654271353071109081112975 981407029606663621669463)
              ·
                refine ⟨1472110544409995432504195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981407029606663621669463 1472110544409995432504195)
                ·
                  refine ⟨2208165816614993148756293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472110544409995432504195 2208165816614993148756293)
                  ·
                    refine ⟨414031090615311215391805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208165816614993148756293 414031090615311215391805)
                    ·
                      refine ⟨155261658980741705771927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414031090615311215391805 155261658980741705771927)
                      ·
                        rfl

theorem cell23_302371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_302371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302371 prefixEnd_302371 := by exact prefixLift 302371
  have htrace : WordTrace (prefixWord ++ tailWord_302371) baseStart_302371 baseEnd_302371 := by
    simpa [prefixWord, tailWord_302371, baseEnd_302371] using wordTrace_append hprefix tailTrace_302371
  have hstable : (prefixWord ++ tailWord_302371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302371).length < 2 ^ (prefixWord ++ tailWord_302371).sum := by decide
  have hdescent : baseEnd_302371 < baseStart_302371 := by decide
  rcases family_descends (prefixWord ++ tailWord_302371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302388 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_302388 : Nat := 118140960795 + 302388 * 2 ^ 59
def prefixEnd_302388 : Nat := 4983230072969 + 3 ^ 40 * 302388 * 2
def baseEnd_302388 : Nat := 155270388151868139259349

theorem tailTrace_302388 : CollatzResearch.WordTrace tailWord_302388 prefixEnd_302388 155270388151868139259349 := by
  unfold tailWord_302388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514498214253697301969909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7352664285671596402626545 5514498214253697301969909)
  ·
    refine ⟨516984207586284122059679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5514498214253697301969909 516984207586284122059679)
    ·
      refine ⟨775476311379426183089519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516984207586284122059679 775476311379426183089519)
      ·
        refine ⟨1163214467069139274634279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775476311379426183089519 1163214467069139274634279)
        ·
          refine ⟨1744821700603708911951419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163214467069139274634279 1744821700603708911951419)
          ·
            refine ⟨2617232550905563367927129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744821700603708911951419 2617232550905563367927129)
            ·
              refine ⟨1962924413179172525945347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2617232550905563367927129 1962924413179172525945347)
              ·
                refine ⟨2944386619768758788918021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962924413179172525945347 2944386619768758788918021)
                ·
                  refine ⟨552072491206642272922129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2944386619768758788918021 552072491206642272922129)
                  ·
                    refine ⟨414054368404981704691597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 552072491206642272922129 414054368404981704691597)
                    ·
                      refine ⟨155270388151868139259349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414054368404981704691597 155270388151868139259349)
                      ·
                        rfl

theorem cell23_302388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_302388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302388 prefixEnd_302388 := by exact prefixLift 302388
  have htrace : WordTrace (prefixWord ++ tailWord_302388) baseStart_302388 baseEnd_302388 := by
    simpa [prefixWord, tailWord_302388, baseEnd_302388] using wordTrace_append hprefix tailTrace_302388
  have hstable : (prefixWord ++ tailWord_302388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302388).length < 2 ^ (prefixWord ++ tailWord_302388).sum := by decide
  have hdescent : baseEnd_302388 < baseStart_302388 := by decide
  rcases family_descends (prefixWord ++ tailWord_302388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302394 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_302394 : Nat := 118140960795 + 302394 * 2 ^ 59
def prefixEnd_302394 : Nat := 4983230072969 + 3 ^ 40 * 302394 * 2
def baseEnd_302394 : Nat := 155273469035795115784321

theorem tailTrace_302394 : CollatzResearch.WordTrace tailWord_302394 prefixEnd_302394 155273469035795115784321 := by
  unfold tailWord_302394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757303816621414407164559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7352810177657105085772157 2757303816621414407164559)
  ·
    refine ⟨4135955724932121610746839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2757303816621414407164559 4135955724932121610746839)
    ·
      refine ⟨6203933587398182416120259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4135955724932121610746839 6203933587398182416120259)
      ·
        refine ⟨9305900381097273624180389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203933587398182416120259 9305900381097273624180389)
        ·
          refine ⟨1744856321455738804533823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9305900381097273624180389 1744856321455738804533823)
          ·
            refine ⟨2617284482183608206800735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744856321455738804533823 2617284482183608206800735)
            ·
              refine ⟨3925926723275412310201103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617284482183608206800735 3925926723275412310201103)
              ·
                refine ⟨5888890084913118465301655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925926723275412310201103 5888890084913118465301655)
                ·
                  refine ⟨8833335127369677697952483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888890084913118465301655 8833335127369677697952483)
                  ·
                    refine ⟨13250002691054516546928725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8833335127369677697952483 13250002691054516546928725)
                    ·
                      refine ⟨155273469035795115784321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 13250002691054516546928725 155273469035795115784321)
                      ·
                        rfl

theorem cell23_302394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_302394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302394 prefixEnd_302394 := by exact prefixLift 302394
  have htrace : WordTrace (prefixWord ++ tailWord_302394) baseStart_302394 baseEnd_302394 := by
    simpa [prefixWord, tailWord_302394, baseEnd_302394] using wordTrace_append hprefix tailTrace_302394
  have hstable : (prefixWord ++ tailWord_302394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302394).length < 2 ^ (prefixWord ++ tailWord_302394).sum := by decide
  have hdescent : baseEnd_302394 < baseStart_302394 := by decide
  rcases family_descends (prefixWord ++ tailWord_302394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302445 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_302445 : Nat := 118140960795 + 302445 * 2 ^ 59
def prefixEnd_302445 : Nat := 4983230072969 + 3 ^ 40 * 302445 * 2
def baseEnd_302445 : Nat := 155299656549174416246587

theorem tailTrace_302445 : CollatzResearch.WordTrace tailWord_302445 prefixEnd_302445 155299656549174416246587 := by
  unfold tailWord_302445
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031075389300893338764789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7354050259533928892509859 11031075389300893338764789)
  ·
    refine ⟨1034163317746958750509199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11031075389300893338764789 1034163317746958750509199)
    ·
      refine ⟨1551244976620438125763799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034163317746958750509199 1551244976620438125763799)
      ·
        refine ⟨2326867464930657188645699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551244976620438125763799 2326867464930657188645699)
        ·
          refine ⟨3490301197395985782968549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326867464930657188645699 3490301197395985782968549)
          ·
            refine ⟨654431474511747334306603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3490301197395985782968549 654431474511747334306603)
            ·
              refine ⟨981647211767621001459905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654431474511747334306603 981647211767621001459905)
              ·
                refine ⟨736235408825715751094929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 981647211767621001459905 736235408825715751094929)
                ·
                  refine ⟨552176556619286813321197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 736235408825715751094929 552176556619286813321197)
                  ·
                    refine ⟨207066208732232554995449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552176556619286813321197 207066208732232554995449)
                    ·
                      refine ⟨155299656549174416246587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207066208732232554995449 155299656549174416246587)
                      ·
                        rfl

theorem cell23_302445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_302445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302445 prefixEnd_302445 := by exact prefixLift 302445
  have htrace : WordTrace (prefixWord ++ tailWord_302445) baseStart_302445 baseEnd_302445 := by
    simpa [prefixWord, tailWord_302445, baseEnd_302445] using wordTrace_append hprefix tailTrace_302445
  have hstable : (prefixWord ++ tailWord_302445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302445).length < 2 ^ (prefixWord ++ tailWord_302445).sum := by decide
  have hdescent : baseEnd_302445 < baseStart_302445 := by decide
  rcases family_descends (prefixWord ++ tailWord_302445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302461 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_302461 : Nat := 118140960795 + 302461 * 2 ^ 59
def prefixEnd_302461 : Nat := 4983230072969 + 3 ^ 40 * 302461 * 2
def baseEnd_302461 : Nat := 155307872239646353646513

theorem tailTrace_302461 : CollatzResearch.WordTrace tailWord_302461 prefixEnd_302461 155307872239646353646513 := by
  unfold tailWord_302461
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031658957242928071347237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7354439304828618714231491 11031658957242928071347237)
  ·
    refine ⟨2068436054483049013377607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11031658957242928071347237 2068436054483049013377607)
    ·
      refine ⟨3102654081724573520066411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068436054483049013377607 3102654081724573520066411)
      ·
        refine ⟨4653981122586860280099617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102654081724573520066411 4653981122586860280099617)
        ·
          refine ⟨3490485841940145210074713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4653981122586860280099617 3490485841940145210074713)
          ·
            refine ⟨2617864381455108907556035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490485841940145210074713 2617864381455108907556035)
            ·
              refine ⟨3926796572182663361334053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617864381455108907556035 3926796572182663361334053)
              ·
                refine ⟨736274357284249380250135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3926796572182663361334053 736274357284249380250135)
                ·
                  refine ⟨1104411535926374070375203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736274357284249380250135 1104411535926374070375203)
                  ·
                    refine ⟨1656617303889561105562805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1104411535926374070375203 1656617303889561105562805)
                    ·
                      refine ⟨155307872239646353646513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1656617303889561105562805 155307872239646353646513)
                      ·
                        rfl

theorem cell23_302461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_302461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302461 prefixEnd_302461 := by exact prefixLift 302461
  have htrace : WordTrace (prefixWord ++ tailWord_302461) baseStart_302461 baseEnd_302461 := by
    simpa [prefixWord, tailWord_302461, baseEnd_302461] using wordTrace_append hprefix tailTrace_302461
  have hstable : (prefixWord ++ tailWord_302461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302461).length < 2 ^ (prefixWord ++ tailWord_302461).sum := by decide
  have hdescent : baseEnd_302461 < baseStart_302461 := by decide
  rcases family_descends (prefixWord ++ tailWord_302461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302471 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_302471 : Nat := 118140960795 + 302471 * 2 ^ 59
def prefixEnd_302471 : Nat := 4983230072969 + 3 ^ 40 * 302471 * 2
def baseEnd_302471 : Nat := 155313007046191314521467

theorem tailTrace_302471 : CollatzResearch.WordTrace tailWord_302471 prefixEnd_302471 155313007046191314521467 := by
  unfold tailWord_302471
  simp only [CollatzResearch.WordTrace]
  refine ⟨11032023687206699779211267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7354682458137799852807511 11032023687206699779211267)
  ·
    refine ⟨16548035530810049668816901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11032023687206699779211267 16548035530810049668816901)
    ·
      refine ⟨3102756662026884312903169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16548035530810049668816901 3102756662026884312903169)
      ·
        refine ⟨2327067496520163234677377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3102756662026884312903169 2327067496520163234677377)
        ·
          refine ⟨1745300622390122426008033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2327067496520163234677377 1745300622390122426008033)
          ·
            refine ⟨1308975466792591819506025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1745300622390122426008033 1308975466792591819506025)
            ·
              refine ⟨981731600094443864629519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308975466792591819506025 981731600094443864629519)
              ·
                refine ⟨1472597400141665796944279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981731600094443864629519 1472597400141665796944279)
                ·
                  refine ⟨2208896100212498695416419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472597400141665796944279 2208896100212498695416419)
                  ·
                    refine ⟨3313344150318748043124629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2208896100212498695416419 3313344150318748043124629)
                    ·
                      refine ⟨155313007046191314521467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3313344150318748043124629 155313007046191314521467)
                      ·
                        rfl

theorem cell23_302471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_302471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302471 prefixEnd_302471 := by exact prefixLift 302471
  have htrace : WordTrace (prefixWord ++ tailWord_302471) baseStart_302471 baseEnd_302471 := by
    simpa [prefixWord, tailWord_302471, baseEnd_302471] using wordTrace_append hprefix tailTrace_302471
  have hstable : (prefixWord ++ tailWord_302471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302471).length < 2 ^ (prefixWord ++ tailWord_302471).sum := by decide
  have hdescent : baseEnd_302471 < baseStart_302471 := by decide
  rcases family_descends (prefixWord ++ tailWord_302471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302508 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_302508 : Nat := 118140960795 + 302508 * 2 ^ 59
def prefixEnd_302508 : Nat := 4983230072969 + 3 ^ 40 * 302508 * 2
def baseEnd_302508 : Nat := 155332005830407669758797

theorem tailTrace_302508 : CollatzResearch.WordTrace tailWord_302508 prefixEnd_302508 155332005830407669758797 := by
  unfold tailWord_302508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5516686594036327549154089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7355582125381770065538785 5516686594036327549154089)
  ·
    refine ⟨4137514945527245661865567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5516686594036327549154089 4137514945527245661865567)
    ·
      refine ⟨6206272418290868492798351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4137514945527245661865567 6206272418290868492798351)
      ·
        refine ⟨9309408627436302739197527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206272418290868492798351 9309408627436302739197527)
        ·
          refine ⟨13964112941154454108796291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309408627436302739197527 13964112941154454108796291)
          ·
            refine ⟨20946169411731681163194437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13964112941154454108796291 20946169411731681163194437)
            ·
              refine ⟨3927406764699690218098957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20946169411731681163194437 3927406764699690218098957)
              ·
                refine ⟨1472777536762383831787109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3927406764699690218098957 1472777536762383831787109)
                ·
                  refine ⟨276145788142946968460083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472777536762383831787109 276145788142946968460083)
                  ·
                    refine ⟨414218682214420452690125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276145788142946968460083 414218682214420452690125)
                    ·
                      refine ⟨155332005830407669758797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414218682214420452690125 155332005830407669758797)
                      ·
                        rfl

theorem cell23_302508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_302508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302508 prefixEnd_302508 := by exact prefixLift 302508
  have htrace : WordTrace (prefixWord ++ tailWord_302508) baseStart_302508 baseEnd_302508 := by
    simpa [prefixWord, tailWord_302508, baseEnd_302508] using wordTrace_append hprefix tailTrace_302508
  have hstable : (prefixWord ++ tailWord_302508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302508).length < 2 ^ (prefixWord ++ tailWord_302508).sum := by decide
  have hdescent : baseEnd_302508 < baseStart_302508 := by decide
  rcases family_descends (prefixWord ++ tailWord_302508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302525 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_302525 : Nat := 118140960795 + 302525 * 2 ^ 59
def prefixEnd_302525 : Nat := 4983230072969 + 3 ^ 40 * 302525 * 2
def baseEnd_302525 : Nat := 155340735001534103246219

theorem tailTrace_302525 : CollatzResearch.WordTrace tailWord_302525 prefixEnd_302525 155340735001534103246219 := by
  unfold tailWord_302525
  simp only [CollatzResearch.WordTrace]
  refine ⟨11033993229011067001677029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7355995486007378001118019 11033993229011067001677029)
  ·
    refine ⟨2068873730439575062814443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11033993229011067001677029 2068873730439575062814443)
    ·
      refine ⟨3103310595659362594221665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068873730439575062814443 3103310595659362594221665)
      ·
        refine ⟨2327482946744521945666249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3103310595659362594221665 2327482946744521945666249)
        ·
          refine ⟨1745612210058391459249687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2327482946744521945666249 1745612210058391459249687)
          ·
            refine ⟨2618418315087587188874531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745612210058391459249687 2618418315087587188874531)
            ·
              refine ⟨3927627472631380783311797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618418315087587188874531 3927627472631380783311797)
              ·
                refine ⟨368215075559191948435481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3927627472631380783311797 368215075559191948435481)
                ·
                  refine ⟨276161306669393961326611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368215075559191948435481 276161306669393961326611)
                  ·
                    refine ⟨414241960004090941989917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276161306669393961326611 414241960004090941989917)
                    ·
                      refine ⟨155340735001534103246219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414241960004090941989917 155340735001534103246219)
                      ·
                        rfl

theorem cell23_302525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_302525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302525 prefixEnd_302525 := by exact prefixLift 302525
  have htrace : WordTrace (prefixWord ++ tailWord_302525) baseStart_302525 baseEnd_302525 := by
    simpa [prefixWord, tailWord_302525, baseEnd_302525] using wordTrace_append hprefix tailTrace_302525
  have hstable : (prefixWord ++ tailWord_302525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302525).length < 2 ^ (prefixWord ++ tailWord_302525).sum := by decide
  have hdescent : baseEnd_302525 < baseStart_302525 := by decide
  rcases family_descends (prefixWord ++ tailWord_302525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302530 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_302530 : Nat := 118140960795 + 302530 * 2 ^ 59
def prefixEnd_302530 : Nat := 4983230072969 + 3 ^ 40 * 302530 * 2
def baseEnd_302530 : Nat := 155343302404806583683697

theorem tailTrace_302530 : CollatzResearch.WordTrace tailWord_302530 prefixEnd_302530 155343302404806583683697 := by
  unfold tailWord_302530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2758543898498238213902261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7356117062661968570406029 2758543898498238213902261)
  ·
    refine ⟨258613490484209832553337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2758543898498238213902261 258613490484209832553337)
    ·
      refine ⟨193960117863157374415003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258613490484209832553337 193960117863157374415003)
      ·
        refine ⟨290940176794736061622505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193960117863157374415003 290940176794736061622505)
        ·
          refine ⟨218205132596052046216879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290940176794736061622505 218205132596052046216879)
          ·
            refine ⟨327307698894078069325319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218205132596052046216879 327307698894078069325319)
            ·
              refine ⟨490961548341117103987979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327307698894078069325319 490961548341117103987979)
              ·
                refine ⟨736442322511675655981969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490961548341117103987979 736442322511675655981969)
                ·
                  refine ⟨552331741883756741986477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 736442322511675655981969 552331741883756741986477)
                  ·
                    refine ⟨207124403206408778244929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552331741883756741986477 207124403206408778244929)
                    ·
                      refine ⟨155343302404806583683697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207124403206408778244929 155343302404806583683697)
                      ·
                        rfl

theorem cell23_302530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_302530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302530 prefixEnd_302530 := by exact prefixLift 302530
  have htrace : WordTrace (prefixWord ++ tailWord_302530) baseStart_302530 baseEnd_302530 := by
    simpa [prefixWord, tailWord_302530, baseEnd_302530] using wordTrace_append hprefix tailTrace_302530
  have hstable : (prefixWord ++ tailWord_302530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302530).length < 2 ^ (prefixWord ++ tailWord_302530).sum := by decide
  have hdescent : baseEnd_302530 < baseStart_302530 := by decide
  rcases family_descends (prefixWord ++ tailWord_302530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302535 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_302535 : Nat := 118140960795 + 302535 * 2 ^ 59
def prefixEnd_302535 : Nat := 4983230072969 + 3 ^ 40 * 302535 * 2
def baseEnd_302535 : Nat := 155345869808079064121173

theorem tailTrace_302535 : CollatzResearch.WordTrace tailWord_302535 prefixEnd_302535 155345869808079064121173 := by
  unfold tailWord_302535
  simp only [CollatzResearch.WordTrace]
  refine ⟨11034357958974838709541059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7356238639316559139694039 11034357958974838709541059)
  ·
    refine ⟨16551536938462258064311589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11034357958974838709541059 16551536938462258064311589)
    ·
      refine ⟨3103413175961673387058423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16551536938462258064311589 3103413175961673387058423)
      ·
        refine ⟨4655119763942510080587635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103413175961673387058423 4655119763942510080587635)
        ·
          refine ⟨6982679645913765120881453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655119763942510080587635 6982679645913765120881453)
          ·
            refine ⟨2618504867217661920330545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6982679645913765120881453 2618504867217661920330545)
            ·
              refine ⟨1963878650413246440247909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2618504867217661920330545 1963878650413246440247909)
              ·
                refine ⟨368227246952483707546483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1963878650413246440247909 368227246952483707546483)
                ·
                  refine ⟨552340870428725561319725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368227246952483707546483 552340870428725561319725)
                  ·
                    refine ⟨207127826410772085494897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552340870428725561319725 207127826410772085494897)
                    ·
                      refine ⟨155345869808079064121173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207127826410772085494897 155345869808079064121173)
                      ·
                        rfl

theorem cell23_302535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_302535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302535 prefixEnd_302535 := by exact prefixLift 302535
  have htrace : WordTrace (prefixWord ++ tailWord_302535) baseStart_302535 baseEnd_302535 := by
    simpa [prefixWord, tailWord_302535, baseEnd_302535] using wordTrace_append hprefix tailTrace_302535
  have hstable : (prefixWord ++ tailWord_302535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302535).length < 2 ^ (prefixWord ++ tailWord_302535).sum := by decide
  have hdescent : baseEnd_302535 < baseStart_302535 := by decide
  rcases family_descends (prefixWord ++ tailWord_302535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302551 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_302551 : Nat := 118140960795 + 302551 * 2 ^ 59
def prefixEnd_302551 : Nat := 4983230072969 + 3 ^ 40 * 302551 * 2
def baseEnd_302551 : Nat := 155354085498551001521099

theorem tailTrace_302551 : CollatzResearch.WordTrace tailWord_302551 prefixEnd_302551 155354085498551001521099 := by
  unfold tailWord_302551
  simp only [CollatzResearch.WordTrace]
  refine ⟨11034941526916873442123507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7356627684611248961415671 11034941526916873442123507)
  ·
    refine ⟨16552412290375310163185261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11034941526916873442123507 16552412290375310163185261)
    ·
      refine ⟨6207154608890741311194473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16552412290375310163185261 6207154608890741311194473)
      ·
        refine ⟨4655365956668055983395855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6207154608890741311194473 4655365956668055983395855)
        ·
          refine ⟨6983048935002083975093783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655365956668055983395855 6983048935002083975093783)
          ·
            refine ⟨10474573402503125962640675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6983048935002083975093783 10474573402503125962640675)
            ·
              refine ⟨15711860103754688943961013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10474573402503125962640675 15711860103754688943961013)
              ·
                refine ⟨1472986884727002088496345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15711860103754688943961013 1472986884727002088496345)
                ·
                  refine ⟨1104740163545251566372259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472986884727002088496345 1104740163545251566372259)
                  ·
                    refine ⟨1657110245317877349558389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1104740163545251566372259 1657110245317877349558389)
                    ·
                      refine ⟨155354085498551001521099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1657110245317877349558389 155354085498551001521099)
                      ·
                        rfl

theorem cell23_302551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_302551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302551 prefixEnd_302551 := by exact prefixLift 302551
  have htrace : WordTrace (prefixWord ++ tailWord_302551) baseStart_302551 baseEnd_302551 := by
    simpa [prefixWord, tailWord_302551, baseEnd_302551] using wordTrace_append hprefix tailTrace_302551
  have hstable : (prefixWord ++ tailWord_302551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302551).length < 2 ^ (prefixWord ++ tailWord_302551).sum := by decide
  have hdescent : baseEnd_302551 < baseStart_302551 := by decide
  rcases family_descends (prefixWord ++ tailWord_302551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302552 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 1, 3, 2]
def baseStart_302552 : Nat := 118140960795 + 302552 * 2 ^ 59
def prefixEnd_302552 : Nat := 4983230072969 + 3 ^ 40 * 302552 * 2
def baseEnd_302552 : Nat := 155354598979205497608595

theorem tailTrace_302552 : CollatzResearch.WordTrace tailWord_302552 prefixEnd_302552 155354598979205497608595 := by
  unfold tailWord_302552
  simp only [CollatzResearch.WordTrace]
  refine ⟨5517488999956625306454955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7356651999942167075273273 5517488999956625306454955)
  ·
    refine ⟨8276233499934937959682433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5517488999956625306454955 8276233499934937959682433)
    ·
      refine ⟨6207175124951203469761825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8276233499934937959682433 6207175124951203469761825)
      ·
        refine ⟨4655381343713402602321369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6207175124951203469761825 4655381343713402602321369)
        ·
          refine ⟨3491536007785051951741027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4655381343713402602321369 3491536007785051951741027)
          ·
            refine ⟨5237304011677577927611541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3491536007785051951741027 5237304011677577927611541)
            ·
              refine ⟨245498625547386465356791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5237304011677577927611541 245498625547386465356791)
              ·
                refine ⟨368247938321079698035187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245498625547386465356791 368247938321079698035187)
                ·
                  refine ⟨552371907481619547052781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368247938321079698035187 552371907481619547052781)
                  ·
                    refine ⟨207139465305607330144793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552371907481619547052781 207139465305607330144793)
                    ·
                      refine ⟨155354598979205497608595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207139465305607330144793 155354598979205497608595)
                      ·
                        rfl

theorem cell23_302552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_302552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302552 prefixEnd_302552 := by exact prefixLift 302552
  have htrace : WordTrace (prefixWord ++ tailWord_302552) baseStart_302552 baseEnd_302552 := by
    simpa [prefixWord, tailWord_302552, baseEnd_302552] using wordTrace_append hprefix tailTrace_302552
  have hstable : (prefixWord ++ tailWord_302552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302552).length < 2 ^ (prefixWord ++ tailWord_302552).sum := by decide
  have hdescent : baseEnd_302552 < baseStart_302552 := by decide
  rcases family_descends (prefixWord ++ tailWord_302552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302582 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_302582 : Nat := 118140960795 + 302582 * 2 ^ 59
def prefixEnd_302582 : Nat := 4983230072969 + 3 ^ 40 * 302582 * 2
def baseEnd_302582 : Nat := 155370003398840380233457

theorem tailTrace_302582 : CollatzResearch.WordTrace tailWord_302582 prefixEnd_302582 155370003398840380233457 := by
  unfold tailWord_302582
  simp only [CollatzResearch.WordTrace]
  refine ⟨689754511862785358531375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7357381459869710491001333 689754511862785358531375)
  ·
    refine ⟨1034631767794178037797063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 689754511862785358531375 1034631767794178037797063)
    ·
      refine ⟨1551947651691267056695595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034631767794178037797063 1551947651691267056695595)
      ·
        refine ⟨2327921477536900585043393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551947651691267056695595 2327921477536900585043393)
        ·
          refine ⟨1745941108152675438782545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2327921477536900585043393 1745941108152675438782545)
          ·
            refine ⟨1309455831114506579086909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1745941108152675438782545 1309455831114506579086909)
            ·
              refine ⟨491045936667939967157591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309455831114506579086909 491045936667939967157591)
              ·
                refine ⟨736568905001909950736387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491045936667939967157591 736568905001909950736387)
                ·
                  refine ⟨1104853357502864926104581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736568905001909950736387 1104853357502864926104581)
                  ·
                    refine ⟨207160004531787173644609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104853357502864926104581 207160004531787173644609)
                    ·
                      refine ⟨155370003398840380233457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207160004531787173644609 155370003398840380233457)
                      ·
                        rfl

theorem cell23_302582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_302582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302582 prefixEnd_302582 := by exact prefixLift 302582
  have htrace : WordTrace (prefixWord ++ tailWord_302582) baseStart_302582 baseEnd_302582 := by
    simpa [prefixWord, tailWord_302582, baseEnd_302582] using wordTrace_append hprefix tailTrace_302582
  have hstable : (prefixWord ++ tailWord_302582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302582).length < 2 ^ (prefixWord ++ tailWord_302582).sum := by decide
  have hdescent : baseEnd_302582 < baseStart_302582 := by decide
  rcases family_descends (prefixWord ++ tailWord_302582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302601 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_302601 : Nat := 118140960795 + 302601 * 2 ^ 59
def prefixEnd_302601 : Nat := 4983230072969 + 3 ^ 40 * 302601 * 2
def baseEnd_302601 : Nat := 51793253177091935298623

theorem tailTrace_302601 : CollatzResearch.WordTrace tailWord_302601 prefixEnd_302601 51793253177091935298623 := by
  unfold tailWord_302601
  simp only [CollatzResearch.WordTrace]
  refine ⟨11036765176735731981443657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7357843451157154654295771 11036765176735731981443657)
  ·
    refine ⟨8277573882551798986082743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11036765176735731981443657 8277573882551798986082743)
    ·
      refine ⟨12416360823827698479124115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8277573882551798986082743 12416360823827698479124115)
      ·
        refine ⟨18624541235741547718686173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12416360823827698479124115 18624541235741547718686173)
        ·
          refine ⟨6984202963403080394507315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18624541235741547718686173 6984202963403080394507315)
          ·
            refine ⟨10476304445104620591760973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984202963403080394507315 10476304445104620591760973)
            ·
              refine ⟨3928614166914232721910365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10476304445104620591760973 3928614166914232721910365)
              ·
                refine ⟨1473230312592837270716387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928614166914232721910365 1473230312592837270716387)
                ·
                  refine ⟨2209845468889255906074581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473230312592837270716387 2209845468889255906074581)
                  ·
                    refine ⟨51793253177091935298623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2209845468889255906074581 51793253177091935298623)
                    ·
                      rfl

theorem cell23_302601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_302601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302601 prefixEnd_302601 := by exact prefixLift 302601
  have htrace : WordTrace (prefixWord ++ tailWord_302601) baseStart_302601 baseEnd_302601 := by
    simpa [prefixWord, tailWord_302601, baseEnd_302601] using wordTrace_append hprefix tailTrace_302601
  have hstable : (prefixWord ++ tailWord_302601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302601).length < 2 ^ (prefixWord ++ tailWord_302601).sum := by decide
  have hdescent : baseEnd_302601 < baseStart_302601 := by decide
  rcases family_descends (prefixWord ++ tailWord_302601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302655 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_302655 : Nat := 118140960795 + 302655 * 2 ^ 59
def prefixEnd_302655 : Nat := 4983230072969 + 3 ^ 40 * 302655 * 2
def baseEnd_302655 : Nat := 155407487486618594620621

theorem tailTrace_302655 : CollatzResearch.WordTrace tailWord_302655 prefixEnd_302655 155407487486618594620621 := by
  unfold tailWord_302655
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038734718540099203909419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7359156479026732802606279 11038734718540099203909419)
  ·
    refine ⟨16558102077810148805864129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11038734718540099203909419 16558102077810148805864129)
    ·
      refine ⟨12418576558357611604398097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16558102077810148805864129 12418576558357611604398097)
      ·
        refine ⟨9313932418768208703298573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12418576558357611604398097 9313932418768208703298573)
        ·
          refine ⟨3492724657038078263736965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9313932418768208703298573 3492724657038078263736965)
          ·
            refine ⟨654885873194639674450681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3492724657038078263736965 654885873194639674450681)
            ·
              refine ⟨491164404895979755838011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654885873194639674450681 491164404895979755838011)
              ·
                refine ⟨736746607343969633757017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491164404895979755838011 736746607343969633757017)
                ·
                  refine ⟨552559955507977225317763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 736746607343969633757017 552559955507977225317763)
                  ·
                    refine ⟨828839933261965837976645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 552559955507977225317763 828839933261965837976645)
                    ·
                      refine ⟨155407487486618594620621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 828839933261965837976645 155407487486618594620621)
                      ·
                        rfl

theorem cell23_302655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_302655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302655 prefixEnd_302655 := by exact prefixLift 302655
  have htrace : WordTrace (prefixWord ++ tailWord_302655) baseStart_302655 baseEnd_302655 := by
    simpa [prefixWord, tailWord_302655, baseEnd_302655] using wordTrace_append hprefix tailTrace_302655
  have hstable : (prefixWord ++ tailWord_302655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302655).length < 2 ^ (prefixWord ++ tailWord_302655).sum := by decide
  have hdescent : baseEnd_302655 < baseStart_302655 := by decide
  rcases family_descends (prefixWord ++ tailWord_302655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302688 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_302688 : Nat := 118140960795 + 302688 * 2 ^ 59
def prefixEnd_302688 : Nat := 4983230072969 + 3 ^ 40 * 302688 * 2
def baseEnd_302688 : Nat := 155424432348216965507969

theorem tailTrace_302688 : CollatzResearch.WordTrace tailWord_302688 prefixEnd_302688 155424432348216965507969 := by
  unfold tailWord_302688
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519969163710272919930359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7359958884947030559907145 5519969163710272919930359)
  ·
    refine ⟨8279953745565409379895539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5519969163710272919930359 8279953745565409379895539)
    ·
      refine ⟨12419930618348114069843309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8279953745565409379895539 12419930618348114069843309)
      ·
        refine ⟨4657473981880542776191241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12419930618348114069843309 4657473981880542776191241)
        ·
          refine ⟨3493105486410407082143431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657473981880542776191241 3493105486410407082143431)
          ·
            refine ⟨5239658229615610623215147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493105486410407082143431 5239658229615610623215147)
            ·
              refine ⟨7859487344423415934822721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239658229615610623215147 7859487344423415934822721)
              ·
                refine ⟨5894615508317561951117041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7859487344423415934822721 5894615508317561951117041)
                ·
                  refine ⟨4420961631238171463337781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5894615508317561951117041 4420961631238171463337781)
                  ·
                    refine ⟨414465152928578574687917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4420961631238171463337781 414465152928578574687917)
                    ·
                      refine ⟨155424432348216965507969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414465152928578574687917 155424432348216965507969)
                      ·
                        rfl

theorem cell23_302688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_302688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302688 prefixEnd_302688 := by exact prefixLift 302688
  have htrace : WordTrace (prefixWord ++ tailWord_302688) baseStart_302688 baseEnd_302688 := by
    simpa [prefixWord, tailWord_302688, baseEnd_302688] using wordTrace_append hprefix tailTrace_302688
  have hstable : (prefixWord ++ tailWord_302688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302688).length < 2 ^ (prefixWord ++ tailWord_302688).sum := by decide
  have hdescent : baseEnd_302688 < baseStart_302688 := by decide
  rcases family_descends (prefixWord ++ tailWord_302688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302709 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_302709 : Nat := 118140960795 + 302709 * 2 ^ 59
def prefixEnd_302709 : Nat := 4983230072969 + 3 ^ 40 * 302709 * 2
def baseEnd_302709 : Nat := 155435215441961383345373

theorem tailTrace_302709 : CollatzResearch.WordTrace tailWord_302709 prefixEnd_302709 155435215441961383345373 := by
  unfold tailWord_302709
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040704260344466426375181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7360469506896310950916787 11040704260344466426375181)
  ·
    refine ⟨4140264097629174909890693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11040704260344466426375181 4140264097629174909890693)
    ·
      refine ⟨776299518305470295604505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4140264097629174909890693 776299518305470295604505)
      ·
        refine ⟨582224638729102721703379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 776299518305470295604505 582224638729102721703379)
        ·
          refine ⟨873336958093654082555069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582224638729102721703379 873336958093654082555069)
          ·
            refine ⟨327501359285120280958151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 873336958093654082555069 327501359285120280958151)
            ·
              refine ⟨491252038927680421437227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327501359285120280958151 491252038927680421437227)
              ·
                refine ⟨736878058391520632155841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491252038927680421437227 736878058391520632155841)
                ·
                  refine ⟨552658543793640474116881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 736878058391520632155841 552658543793640474116881)
                  ·
                    refine ⟨414493907845230355587661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 552658543793640474116881 414493907845230355587661)
                    ·
                      refine ⟨155435215441961383345373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414493907845230355587661 155435215441961383345373)
                      ·
                        rfl

theorem cell23_302709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_302709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302709 prefixEnd_302709 := by exact prefixLift 302709
  have htrace : WordTrace (prefixWord ++ tailWord_302709) baseStart_302709 baseEnd_302709 := by
    simpa [prefixWord, tailWord_302709, baseEnd_302709] using wordTrace_append hprefix tailTrace_302709
  have hstable : (prefixWord ++ tailWord_302709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302709).length < 2 ^ (prefixWord ++ tailWord_302709).sum := by decide
  have hdescent : baseEnd_302709 < baseStart_302709 := by decide
  rcases family_descends (prefixWord ++ tailWord_302709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302715 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 1, 5, 2]
def baseStart_302715 : Nat := 118140960795 + 302715 * 2 ^ 59
def prefixEnd_302715 : Nat := 4983230072969 + 3 ^ 40 * 302715 * 2
def baseEnd_302715 : Nat := 155438296325888359870345

theorem tailTrace_302715 : CollatzResearch.WordTrace tailWord_302715 prefixEnd_302715 155438296325888359870345 := by
  unfold tailWord_302715
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040923098322729451093599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7360615398881819634062399 11040923098322729451093599)
  ·
    refine ⟨16561384647484094176640399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11040923098322729451093599 16561384647484094176640399)
    ·
      refine ⟨24842076971226141264960599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16561384647484094176640399 24842076971226141264960599)
      ·
        refine ⟨37263115456839211897440899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24842076971226141264960599 37263115456839211897440899)
        ·
          refine ⟨55894673185258817846161349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37263115456839211897440899 55894673185258817846161349)
          ·
            refine ⟨10480251222236028346155253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55894673185258817846161349 10480251222236028346155253)
            ·
              refine ⟨982523552084627657452055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10480251222236028346155253 982523552084627657452055)
              ·
                refine ⟨1473785328126941486178083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982523552084627657452055 1473785328126941486178083)
                ·
                  refine ⟨2210677992190412229267125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473785328126941486178083 2210677992190412229267125)
                  ·
                    refine ⟨207251061767851146493793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2210677992190412229267125 207251061767851146493793)
                    ·
                      refine ⟨155438296325888359870345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207251061767851146493793 155438296325888359870345)
                      ·
                        rfl

theorem cell23_302715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5, 2].length) (baseStart_302715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302715 prefixEnd_302715 := by exact prefixLift 302715
  have htrace : WordTrace (prefixWord ++ tailWord_302715) baseStart_302715 baseEnd_302715 := by
    simpa [prefixWord, tailWord_302715, baseEnd_302715] using wordTrace_append hprefix tailTrace_302715
  have hstable : (prefixWord ++ tailWord_302715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302715).length < 2 ^ (prefixWord ++ tailWord_302715).sum := by decide
  have hdescent : baseEnd_302715 < baseStart_302715 := by decide
  rcases family_descends (prefixWord ++ tailWord_302715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302725 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_302725 : Nat := 118140960795 + 302725 * 2 ^ 59
def prefixEnd_302725 : Nat := 4983230072969 + 3 ^ 40 * 302725 * 2
def baseEnd_302725 : Nat := 51814477044144440248433

theorem tailTrace_302725 : CollatzResearch.WordTrace tailWord_302725 prefixEnd_302725 51814477044144440248433 := by
  unfold tailWord_302725
  simp only [CollatzResearch.WordTrace]
  refine ⟨11041287828286501158957629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7360858552191000772638419 11041287828286501158957629)
  ·
    refine ⟨4140482935607437934609111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11041287828286501158957629 4140482935607437934609111)
    ·
      refine ⟨6210724403411156901913667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140482935607437934609111 6210724403411156901913667)
      ·
        refine ⟨9316086605116735352870501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6210724403411156901913667 9316086605116735352870501)
        ·
          refine ⟨1746766238459387878663219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9316086605116735352870501 1746766238459387878663219)
          ·
            refine ⟨2620149357689081817994829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746766238459387878663219 2620149357689081817994829)
            ·
              refine ⟨982556009133405681748061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2620149357689081817994829 982556009133405681748061)
              ·
                refine ⟨368458503425027130655523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 982556009133405681748061 368458503425027130655523)
                ·
                  refine ⟨552687755137540695983285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368458503425027130655523 552687755137540695983285)
                  ·
                    refine ⟨51814477044144440248433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 552687755137540695983285 51814477044144440248433)
                    ·
                      rfl

theorem cell23_302725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_302725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302725 prefixEnd_302725 := by exact prefixLift 302725
  have htrace : WordTrace (prefixWord ++ tailWord_302725) baseStart_302725 baseEnd_302725 := by
    simpa [prefixWord, tailWord_302725, baseEnd_302725] using wordTrace_append hprefix tailTrace_302725
  have hstable : (prefixWord ++ tailWord_302725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302725).length < 2 ^ (prefixWord ++ tailWord_302725).sum := by decide
  have hdescent : baseEnd_302725 < baseStart_302725 := by decide
  rcases family_descends (prefixWord ++ tailWord_302725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302765 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_302765 : Nat := 118140960795 + 302765 * 2 ^ 59
def prefixEnd_302765 : Nat := 4983230072969 + 3 ^ 40 * 302765 * 2
def baseEnd_302765 : Nat := 155463970358613164245115

theorem tailTrace_302765 : CollatzResearch.WordTrace tailWord_302765 prefixEnd_302765 155463970358613164245115 := by
  unfold tailWord_302765
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042746748141587990413749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7361831165427725326942499 11042746748141587990413749)
  ·
    refine ⟨1035257507638273874101289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11042746748141587990413749 1035257507638273874101289)
    ·
      refine ⟨776443130728705405575967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035257507638273874101289 776443130728705405575967)
      ·
        refine ⟨1164664696093058108363951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776443130728705405575967 1164664696093058108363951)
        ·
          refine ⟨1746997044139587162545927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164664696093058108363951 1746997044139587162545927)
          ·
            refine ⟨2620495566209380743818891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746997044139587162545927 2620495566209380743818891)
            ·
              refine ⟨3930743349314071115728337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620495566209380743818891 3930743349314071115728337)
              ·
                refine ⟨2948057511985553336796253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930743349314071115728337 2948057511985553336796253)
                ·
                  refine ⟨1105521566994582501298595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2948057511985553336796253 1105521566994582501298595)
                  ·
                    refine ⟨1658282350491873751947893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105521566994582501298595 1658282350491873751947893)
                    ·
                      refine ⟨155463970358613164245115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1658282350491873751947893 155463970358613164245115)
                      ·
                        rfl

theorem cell23_302765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_302765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302765 prefixEnd_302765 := by exact prefixLift 302765
  have htrace : WordTrace (prefixWord ++ tailWord_302765) baseStart_302765 baseEnd_302765 := by
    simpa [prefixWord, tailWord_302765, baseEnd_302765] using wordTrace_append hprefix tailTrace_302765
  have hstable : (prefixWord ++ tailWord_302765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302765).length < 2 ^ (prefixWord ++ tailWord_302765).sum := by decide
  have hdescent : baseEnd_302765 < baseStart_302765 := by decide
  rcases family_descends (prefixWord ++ tailWord_302765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302773 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_302773 : Nat := 118140960795 + 302773 * 2 ^ 59
def prefixEnd_302773 : Nat := 4983230072969 + 3 ^ 40 * 302773 * 2
def baseEnd_302773 : Nat := 155468078203849132945079

theorem tailTrace_302773 : CollatzResearch.WordTrace tailWord_302773 prefixEnd_302773 155468078203849132945079 := by
  unfold tailWord_302773
  simp only [CollatzResearch.WordTrace]
  refine ⟨11043038532112605356704973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7362025688075070237803315 11043038532112605356704973)
  ·
    refine ⟨4141139449542227008764365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11043038532112605356704973 4141139449542227008764365)
    ·
      refine ⟨1552927293578335128286637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4141139449542227008764365 1552927293578335128286637)
      ·
        refine ⟨582347735091875673107489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1552927293578335128286637 582347735091875673107489)
        ·
          refine ⟨436760801318906754830617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582347735091875673107489 436760801318906754830617)
          ·
            refine ⟨327570600989180066122963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436760801318906754830617 327570600989180066122963)
            ·
              refine ⟨491355901483770099184445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327570600989180066122963 491355901483770099184445)
              ·
                refine ⟨184258463056413787194167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491355901483770099184445 184258463056413787194167)
                ·
                  refine ⟨276387694584620680791251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184258463056413787194167 276387694584620680791251)
                  ·
                    refine ⟨414581541876931021186877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276387694584620680791251 414581541876931021186877)
                    ·
                      refine ⟨155468078203849132945079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414581541876931021186877 155468078203849132945079)
                      ·
                        rfl

theorem cell23_302773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_302773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302773 prefixEnd_302773 := by exact prefixLift 302773
  have htrace : WordTrace (prefixWord ++ tailWord_302773) baseStart_302773 baseEnd_302773 := by
    simpa [prefixWord, tailWord_302773, baseEnd_302773] using wordTrace_append hprefix tailTrace_302773
  have hstable : (prefixWord ++ tailWord_302773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302773).length < 2 ^ (prefixWord ++ tailWord_302773).sum := by decide
  have hdescent : baseEnd_302773 < baseStart_302773 := by decide
  rcases family_descends (prefixWord ++ tailWord_302773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302782 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_302782 : Nat := 118140960795 + 302782 * 2 ^ 59
def prefixEnd_302782 : Nat := 4983230072969 + 3 ^ 40 * 302782 * 2
def baseEnd_302782 : Nat := 155472699529739597732537

theorem tailTrace_302782 : CollatzResearch.WordTrace tailWord_302782 prefixEnd_302782 155472699529739597732537 := by
  unfold tailWord_302782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380420848634999986722825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7362244526053333262521733 1380420848634999986722825)
  ·
    refine ⟨1035315636476249990042119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380420848634999986722825 1035315636476249990042119)
    ·
      refine ⟨1552973454714374985063179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035315636476249990042119 1552973454714374985063179)
      ·
        refine ⟨2329460182071562477594769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552973454714374985063179 2329460182071562477594769)
        ·
          refine ⟨1747095136553671858196077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2329460182071562477594769 1747095136553671858196077)
          ·
            refine ⟨655160676207626946823529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1747095136553671858196077 655160676207626946823529)
            ·
              refine ⟨491370507155720210117647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655160676207626946823529 491370507155720210117647)
              ·
                refine ⟨737055760733580315176471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491370507155720210117647 737055760733580315176471)
                ·
                  refine ⟨1105583641100370472764707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737055760733580315176471 1105583641100370472764707)
                  ·
                    refine ⟨1658375461650555709147061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105583641100370472764707 1658375461650555709147061)
                    ·
                      refine ⟨155472699529739597732537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1658375461650555709147061 155472699529739597732537)
                      ·
                        rfl

theorem cell23_302782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_302782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302782 prefixEnd_302782 := by exact prefixLift 302782
  have htrace : WordTrace (prefixWord ++ tailWord_302782) baseStart_302782 baseEnd_302782 := by
    simpa [prefixWord, tailWord_302782, baseEnd_302782] using wordTrace_append hprefix tailTrace_302782
  have hstable : (prefixWord ++ tailWord_302782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302782).length < 2 ^ (prefixWord ++ tailWord_302782).sum := by decide
  have hdescent : baseEnd_302782 < baseStart_302782 := by decide
  rcases family_descends (prefixWord ++ tailWord_302782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302813 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_302813 : Nat := 118140960795 + 302813 * 2 ^ 59
def prefixEnd_302813 : Nat := 4983230072969 + 3 ^ 40 * 302813 * 2
def baseEnd_302813 : Nat := 155488617430028976444895

theorem tailTrace_302813 : CollatzResearch.WordTrace tailWord_302813 prefixEnd_302813 155488617430028976444895 := by
  unfold tailWord_302813
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044497451967692188161093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7362998301311794792107395 11044497451967692188161093)
  ·
    refine ⟨2070843272243942285280205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11044497451967692188161093 2070843272243942285280205)
    ·
      refine ⟨776566227091478356980077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2070843272243942285280205 776566227091478356980077)
      ·
        refine ⟨291212335159304383867529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 776566227091478356980077 291212335159304383867529)
        ·
          refine ⟨218409251369478287900647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291212335159304383867529 218409251369478287900647)
          ·
            refine ⟨327613877054217431850971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218409251369478287900647 327613877054217431850971)
            ·
              refine ⟨491420815581326147776457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327613877054217431850971 491420815581326147776457)
              ·
                refine ⟨368565611685994610832343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491420815581326147776457 368565611685994610832343)
                ·
                  refine ⟨552848417528991916248515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368565611685994610832343 552848417528991916248515)
                  ·
                    refine ⟨829272626293487874372773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 552848417528991916248515 829272626293487874372773)
                    ·
                      refine ⟨155488617430028976444895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 829272626293487874372773 155488617430028976444895)
                      ·
                        rfl

theorem cell23_302813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_302813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302813 prefixEnd_302813 := by exact prefixLift 302813
  have htrace : WordTrace (prefixWord ++ tailWord_302813) baseStart_302813 baseEnd_302813 := by
    simpa [prefixWord, tailWord_302813, baseEnd_302813] using wordTrace_append hprefix tailTrace_302813
  have hstable : (prefixWord ++ tailWord_302813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302813).length < 2 ^ (prefixWord ++ tailWord_302813).sum := by decide
  have hdescent : baseEnd_302813 < baseStart_302813 := by decide
  rcases family_descends (prefixWord ++ tailWord_302813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302869 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_302869 : Nat := 118140960795 + 302869 * 2 ^ 59
def prefixEnd_302869 : Nat := 4983230072969 + 3 ^ 40 * 302869 * 2
def baseEnd_302869 : Nat := 155517372346680757344637

theorem tailTrace_302869 : CollatzResearch.WordTrace tailWord_302869 prefixEnd_302869 155517372346680757344637 := by
  unfold tailWord_302869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11046539939764813752199661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7364359959843209168133107 11046539939764813752199661)
  ·
    refine ⟨4142452477411805157074873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11046539939764813752199661 4142452477411805157074873)
    ·
      refine ⟨3106839358058853867806155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4142452477411805157074873 3106839358058853867806155)
      ·
        refine ⟨4660259037088280801709233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106839358058853867806155 4660259037088280801709233)
        ·
          refine ⟨3495194277816210601281925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4660259037088280801709233 3495194277816210601281925)
          ·
            refine ⟨655348927090539487740361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3495194277816210601281925 655348927090539487740361)
            ·
              refine ⟨491511695317904615805271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655348927090539487740361 491511695317904615805271)
              ·
                refine ⟨737267542976856923707907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491511695317904615805271 737267542976856923707907)
                ·
                  refine ⟨1105901314465285385561861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737267542976856923707907 1105901314465285385561861)
                  ·
                    refine ⟨207356496462241009792849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105901314465285385561861 207356496462241009792849)
                    ·
                      refine ⟨155517372346680757344637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207356496462241009792849 155517372346680757344637)
                      ·
                        rfl

theorem cell23_302869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_302869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302869 prefixEnd_302869 := by exact prefixLift 302869
  have htrace : WordTrace (prefixWord ++ tailWord_302869) baseStart_302869 baseEnd_302869 := by
    simpa [prefixWord, tailWord_302869, baseEnd_302869] using wordTrace_append hprefix tailTrace_302869
  have hstable : (prefixWord ++ tailWord_302869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302869).length < 2 ^ (prefixWord ++ tailWord_302869).sum := by decide
  have hdescent : baseEnd_302869 < baseStart_302869 := by decide
  rcases family_descends (prefixWord ++ tailWord_302869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302892 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 5]
def baseStart_302892 : Nat := 118140960795 + 302892 * 2 ^ 59
def prefixEnd_302892 : Nat := 4983230072969 + 3 ^ 40 * 302892 * 2
def baseEnd_302892 : Nat := 17281020266859351928559

theorem tailTrace_302892 : CollatzResearch.WordTrace tailWord_302892 prefixEnd_302892 17281020266859351928559 := by
  unfold tailWord_302892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523689409340744340143465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7364919212454325786857953 5523689409340744340143465)
  ·
    refine ⟨4142767057005558255107599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5523689409340744340143465 4142767057005558255107599)
    ·
      refine ⟨6214150585508337382661399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142767057005558255107599 6214150585508337382661399)
      ·
        refine ⟨9321225878262506073992099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6214150585508337382661399 9321225878262506073992099)
        ·
          refine ⟨13981838817393759110988149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9321225878262506073992099 13981838817393759110988149)
          ·
            refine ⟨1310797389130664916655139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13981838817393759110988149 1310797389130664916655139)
            ·
              refine ⟨1966196083695997374982709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310797389130664916655139 1966196083695997374982709)
              ·
                refine ⟨184330882846499753904629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1966196083695997374982709 184330882846499753904629)
                ·
                  refine ⟨17281020266859351928559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184330882846499753904629 17281020266859351928559)
                  ·
                    rfl

theorem cell23_302892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_302892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302892 prefixEnd_302892 := by exact prefixLift 302892
  have htrace : WordTrace (prefixWord ++ tailWord_302892) baseStart_302892 baseEnd_302892 := by
    simpa [prefixWord, tailWord_302892, baseEnd_302892] using wordTrace_append hprefix tailTrace_302892
  have hstable : (prefixWord ++ tailWord_302892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302892).length < 2 ^ (prefixWord ++ tailWord_302892).sum := by decide
  have hdescent : baseEnd_302892 < baseStart_302892 := by decide
  rcases family_descends (prefixWord ++ tailWord_302892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302909 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 5]
def baseStart_302909 : Nat := 118140960795 + 302909 * 2 ^ 59
def prefixEnd_302909 : Nat := 4983230072969 + 3 ^ 40 * 302909 * 2
def baseEnd_302909 : Nat := 17281990174762288982717

theorem tailTrace_302909 : CollatzResearch.WordTrace tailWord_302909 prefixEnd_302909 17281990174762288982717 := by
  unfold tailWord_302909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047998859619900583655781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7365332573079933722437187 11047998859619900583655781)
  ·
    refine ⟨2071499786178731359435459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11047998859619900583655781 2071499786178731359435459)
    ·
      refine ⟨3107249679268097039153189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071499786178731359435459 3107249679268097039153189)
      ·
        refine ⟨582609314862768194841223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3107249679268097039153189 582609314862768194841223)
        ·
          refine ⟨873913972294152292261835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582609314862768194841223 873913972294152292261835)
          ·
            refine ⟨1310870958441228438392753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873913972294152292261835 1310870958441228438392753)
            ·
              refine ⟨983153218830921328794565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310870958441228438392753 983153218830921328794565)
              ·
                refine ⟨184341228530797749148981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 983153218830921328794565 184341228530797749148981)
                ·
                  refine ⟨17281990174762288982717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184341228530797749148981 17281990174762288982717)
                  ·
                    rfl

theorem cell23_302909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_302909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302909 prefixEnd_302909 := by exact prefixLift 302909
  have htrace : WordTrace (prefixWord ++ tailWord_302909) baseStart_302909 baseEnd_302909 := by
    simpa [prefixWord, tailWord_302909, baseEnd_302909] using wordTrace_append hprefix tailTrace_302909
  have hstable : (prefixWord ++ tailWord_302909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302909).length < 2 ^ (prefixWord ++ tailWord_302909).sum := by decide
  have hdescent : baseEnd_302909 < baseStart_302909 := by decide
  rcases family_descends (prefixWord ++ tailWord_302909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302996 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_302996 : Nat := 118140960795 + 302996 * 2 ^ 59
def prefixEnd_302996 : Nat := 4983230072969 + 3 ^ 40 * 302996 * 2
def baseEnd_302996 : Nat := 155582584389801760456553

theorem tailTrace_302996 : CollatzResearch.WordTrace tailWord_302996 prefixEnd_302996 155582584389801760456553 := by
  unfold tailWord_302996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525586005152357221036421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7367448006869809628048561 5525586005152357221036421)
  ·
    refine ⟨1036047375966066978944329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5525586005152357221036421 1036047375966066978944329)
    ·
      refine ⟨777035531974550234208247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1036047375966066978944329 777035531974550234208247)
      ·
        refine ⟨1165553297961825351312371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777035531974550234208247 1165553297961825351312371)
        ·
          refine ⟨1748329946942738026968557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165553297961825351312371 1748329946942738026968557)
          ·
            refine ⟨655623730103526760113209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1748329946942738026968557 655623730103526760113209)
            ·
              refine ⟨491717797577645070084907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655623730103526760113209 491717797577645070084907)
              ·
                refine ⟨737576696366467605127361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491717797577645070084907 737576696366467605127361)
                ·
                  refine ⟨553182522274850703845521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 737576696366467605127361 553182522274850703845521)
                  ·
                    refine ⟨414886891706138027884141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 553182522274850703845521 414886891706138027884141)
                    ·
                      refine ⟨155582584389801760456553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 414886891706138027884141 155582584389801760456553)
                      ·
                        rfl

theorem cell23_302996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_302996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_302996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_302996 prefixEnd_302996 := by exact prefixLift 302996
  have htrace : WordTrace (prefixWord ++ tailWord_302996) baseStart_302996 baseEnd_302996 := by
    simpa [prefixWord, tailWord_302996, baseEnd_302996] using wordTrace_append hprefix tailTrace_302996
  have hstable : (prefixWord ++ tailWord_302996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302996).length < 2 ^ (prefixWord ++ tailWord_302996).sum := by decide
  have hdescent : baseEnd_302996 < baseStart_302996 := by decide
  rcases family_descends (prefixWord ++ tailWord_302996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303032 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_303032 : Nat := 118140960795 + 303032 * 2 ^ 59
def prefixEnd_303032 : Nat := 4983230072969 + 3 ^ 40 * 303032 * 2
def baseEnd_303032 : Nat := 155601069693363619606387

theorem tailTrace_303032 : CollatzResearch.WordTrace tailWord_303032 prefixEnd_303032 155601069693363619606387 := by
  unfold tailWord_303032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526242519087146295191675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7368323358782861726922233 5526242519087146295191675)
  ·
    refine ⟨8289363778630719442787513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5526242519087146295191675 8289363778630719442787513)
    ·
      refine ⟨6217022833973039582090635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8289363778630719442787513 6217022833973039582090635)
      ·
        refine ⟨9325534250959559373135953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6217022833973039582090635 9325534250959559373135953)
        ·
          refine ⟨6994150688219669529851965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9325534250959559373135953 6994150688219669529851965)
          ·
            refine ⟨2622806508082376073694487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6994150688219669529851965 2622806508082376073694487)
            ·
              refine ⟨3934209762123564110541731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622806508082376073694487 3934209762123564110541731)
              ·
                refine ⟨5901314643185346165812597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934209762123564110541731 5901314643185346165812597)
                ·
                  refine ⟨553248247798626203044931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5901314643185346165812597 553248247798626203044931)
                  ·
                    refine ⟨829872371697939304567397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553248247798626203044931 829872371697939304567397)
                    ·
                      refine ⟨155601069693363619606387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 829872371697939304567397 155601069693363619606387)
                      ·
                        rfl

theorem cell23_303032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_303032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303032 prefixEnd_303032 := by exact prefixLift 303032
  have htrace : WordTrace (prefixWord ++ tailWord_303032) baseStart_303032 baseEnd_303032 := by
    simpa [prefixWord, tailWord_303032, baseEnd_303032] using wordTrace_append hprefix tailTrace_303032
  have hstable : (prefixWord ++ tailWord_303032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303032).length < 2 ^ (prefixWord ++ tailWord_303032).sum := by decide
  have hdescent : baseEnd_303032 < baseStart_303032 := by decide
  rcases family_descends (prefixWord ++ tailWord_303032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303066 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_303066 : Nat := 118140960795 + 303066 * 2 ^ 59
def prefixEnd_303066 : Nat := 4983230072969 + 3 ^ 40 * 303066 * 2
def baseEnd_303066 : Nat := 155618528035616486581231

theorem tailTrace_303066 : CollatzResearch.WordTrace tailWord_303066 prefixEnd_303066 155618528035616486581231 := by
  unfold tailWord_303066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763431280012779099280263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7369150080034077598080701 2763431280012779099280263)
  ·
    refine ⟨4145146920019168648920395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2763431280012779099280263 4145146920019168648920395)
    ·
      refine ⟨6217720380028752973380593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4145146920019168648920395 6217720380028752973380593)
      ·
        refine ⟨4663290285021564730035445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6217720380028752973380593 4663290285021564730035445)
        ·
          refine ⟨437183464220771693440823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4663290285021564730035445 437183464220771693440823)
          ·
            refine ⟨655775196331157540161235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437183464220771693440823 655775196331157540161235)
            ·
              refine ⟨983662794496736310241853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655775196331157540161235 983662794496736310241853)
              ·
                refine ⟨368873547936276116340695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 983662794496736310241853 368873547936276116340695)
                ·
                  refine ⟨553310321904414174511043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368873547936276116340695 553310321904414174511043)
                  ·
                    refine ⟨829965482856621261766565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553310321904414174511043 829965482856621261766565)
                    ·
                      refine ⟨155618528035616486581231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 829965482856621261766565 155618528035616486581231)
                      ·
                        rfl

theorem cell23_303066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_303066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303066 prefixEnd_303066 := by exact prefixLift 303066
  have htrace : WordTrace (prefixWord ++ tailWord_303066) baseStart_303066 baseEnd_303066 := by
    simpa [prefixWord, tailWord_303066, baseEnd_303066] using wordTrace_append hprefix tailTrace_303066
  have hstable : (prefixWord ++ tailWord_303066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303066).length < 2 ^ (prefixWord ++ tailWord_303066).sum := by decide
  have hdescent : baseEnd_303066 < baseStart_303066 := by decide
  rcases family_descends (prefixWord ++ tailWord_303066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303099 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 3]
def baseStart_303099 : Nat := 118140960795 + 303099 * 2 ^ 59
def prefixEnd_303099 : Nat := 4983230072969 + 3 ^ 40 * 303099 * 2
def baseEnd_303099 : Nat := 155635472897214857468579

theorem tailTrace_303099 : CollatzResearch.WordTrace tailWord_303099 prefixEnd_303099 155635472897214857468579 := by
  unfold tailWord_303099
  simp only [CollatzResearch.WordTrace]
  refine ⟨11054928728931563033072351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7369952485954375355381567 11054928728931563033072351)
  ·
    refine ⟨16582393093397344549608527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11054928728931563033072351 16582393093397344549608527)
    ·
      refine ⟨24873589640096016824412791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16582393093397344549608527 24873589640096016824412791)
      ·
        refine ⟨37310384460144025236619187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24873589640096016824412791 37310384460144025236619187)
        ·
          refine ⟨55965576690216037854928781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37310384460144025236619187 55965576690216037854928781)
          ·
            refine ⟨20987091258831014195598293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55965576690216037854928781 20987091258831014195598293)
            ·
              refine ⟨491884951378851895209335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20987091258831014195598293 491884951378851895209335)
              ·
                refine ⟨737827427068277842814003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491884951378851895209335 737827427068277842814003)
                ·
                  refine ⟨1106741140602416764221005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737827427068277842814003 1106741140602416764221005)
                  ·
                    refine ⟨415027927725906286582877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1106741140602416764221005 415027927725906286582877)
                    ·
                      refine ⟨155635472897214857468579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415027927725906286582877 155635472897214857468579)
                      ·
                        rfl

theorem cell23_303099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 3].length) (baseStart_303099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303099 prefixEnd_303099 := by exact prefixLift 303099
  have htrace : WordTrace (prefixWord ++ tailWord_303099) baseStart_303099 baseEnd_303099 := by
    simpa [prefixWord, tailWord_303099, baseEnd_303099] using wordTrace_append hprefix tailTrace_303099
  have hstable : (prefixWord ++ tailWord_303099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303099).length < 2 ^ (prefixWord ++ tailWord_303099).sum := by decide
  have hdescent : baseEnd_303099 < baseStart_303099 := by decide
  rcases family_descends (prefixWord ++ tailWord_303099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303112 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_303112 : Nat := 118140960795 + 303112 * 2 ^ 59
def prefixEnd_303112 : Nat := 4983230072969 + 3 ^ 40 * 303112 * 2
def baseEnd_303112 : Nat := 155642148145723306606019

theorem tailTrace_303112 : CollatzResearch.WordTrace tailWord_303112 prefixEnd_303112 155642148145723306606019 := by
  unfold tailWord_303112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527701438942233126647795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7370268585256310835530393 5527701438942233126647795)
  ·
    refine ⟨8291552158413349689971693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5527701438942233126647795 8291552158413349689971693)
    ·
      refine ⟨3109332059405006133739385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8291552158413349689971693 3109332059405006133739385)
      ·
        refine ⟨2331999044553754600304539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3109332059405006133739385 2331999044553754600304539)
        ·
          refine ⟨3497998566830631900456809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331999044553754600304539 3497998566830631900456809)
          ·
            refine ⟨2623498925122973925342607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3497998566830631900456809 2623498925122973925342607)
            ·
              refine ⟨3935248387684460888013911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623498925122973925342607 3935248387684460888013911)
              ·
                refine ⟨5902872581526691332020867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935248387684460888013911 5902872581526691332020867)
                ·
                  refine ⟨8854308872290036998031301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5902872581526691332020867 8854308872290036998031301)
                  ·
                    refine ⟨1660182913554381937130869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8854308872290036998031301 1660182913554381937130869)
                    ·
                      refine ⟨155642148145723306606019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1660182913554381937130869 155642148145723306606019)
                      ·
                        rfl

theorem cell23_303112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_303112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303112 prefixEnd_303112 := by exact prefixLift 303112
  have htrace : WordTrace (prefixWord ++ tailWord_303112) baseStart_303112 baseEnd_303112 := by
    simpa [prefixWord, tailWord_303112, baseEnd_303112] using wordTrace_append hprefix tailTrace_303112
  have hstable : (prefixWord ++ tailWord_303112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303112).length < 2 ^ (prefixWord ++ tailWord_303112).sum := by decide
  have hdescent : baseEnd_303112 < baseStart_303112 := by decide
  rcases family_descends (prefixWord ++ tailWord_303112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303150 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_303150 : Nat := 118140960795 + 303150 * 2 ^ 59
def prefixEnd_303150 : Nat := 4983230072969 + 3 ^ 40 * 303150 * 2
def baseEnd_303150 : Nat := 155661660410594157930845

theorem tailTrace_303150 : CollatzResearch.WordTrace tailWord_303150 prefixEnd_303150 155661660410594157930845 := by
  unfold tailWord_303150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382098606468349842897363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7371192567831199162119269 1382098606468349842897363)
  ·
    refine ⟨2073147909702524764346045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1382098606468349842897363 2073147909702524764346045)
    ·
      refine ⟨777430466138446786629767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2073147909702524764346045 777430466138446786629767)
      ·
        refine ⟨1166145699207670179944651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777430466138446786629767 1166145699207670179944651)
        ·
          refine ⟨1749218548811505269916977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166145699207670179944651 1749218548811505269916977)
          ·
            refine ⟨1311913911608628952437733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1749218548811505269916977 1311913911608628952437733)
            ·
              refine ⟨245983858426617928582075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1311913911608628952437733 245983858426617928582075)
              ·
                refine ⟨368975787639926892873113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245983858426617928582075 368975787639926892873113)
                ·
                  refine ⟨276731840729945169654835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368975787639926892873113 276731840729945169654835)
                  ·
                    refine ⟨415097761094917754482253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276731840729945169654835 415097761094917754482253)
                    ·
                      refine ⟨155661660410594157930845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415097761094917754482253 155661660410594157930845)
                      ·
                        rfl

theorem cell23_303150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_303150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303150 prefixEnd_303150 := by exact prefixLift 303150
  have htrace : WordTrace (prefixWord ++ tailWord_303150) baseStart_303150 baseEnd_303150 := by
    simpa [prefixWord, tailWord_303150, baseEnd_303150] using wordTrace_append hprefix tailTrace_303150
  have hstable : (prefixWord ++ tailWord_303150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303150).length < 2 ^ (prefixWord ++ tailWord_303150).sum := by decide
  have hdescent : baseEnd_303150 < baseStart_303150 := by decide
  rcases family_descends (prefixWord ++ tailWord_303150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303160 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 1, 3, 2]
def baseStart_303160 : Nat := 118140960795 + 303160 * 2 ^ 59
def prefixEnd_303160 : Nat := 4983230072969 + 3 ^ 40 * 303160 * 2
def baseEnd_303160 : Nat := 155666795217139118805799

theorem tailTrace_303160 : CollatzResearch.WordTrace tailWord_303160 prefixEnd_303160 155666795217139118805799 := by
  unfold tailWord_303160
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528576790855285225521467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7371435721140380300695289 5528576790855285225521467)
  ·
    refine ⟨8292865186282927838282201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528576790855285225521467 8292865186282927838282201)
    ·
      refine ⟨6219648889712195878711651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8292865186282927838282201 6219648889712195878711651)
      ·
        refine ⟨9329473334568293818067477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6219648889712195878711651 9329473334568293818067477)
        ·
          refine ⟨437319062557888772721913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9329473334568293818067477 437319062557888772721913)
          ·
            refine ⟨327989296918416579541435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437319062557888772721913 327989296918416579541435)
            ·
              refine ⟨491983945377624869312153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327989296918416579541435 491983945377624869312153)
              ·
                refine ⟨368987959033218651984115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491983945377624869312153 368987959033218651984115)
                ·
                  refine ⟨553481938549827977976173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368987959033218651984115 553481938549827977976173)
                  ·
                    refine ⟨207555726956185491741065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553481938549827977976173 207555726956185491741065)
                    ·
                      refine ⟨155666795217139118805799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207555726956185491741065 155666795217139118805799)
                      ·
                        rfl

theorem cell23_303160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_303160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303160 prefixEnd_303160 := by exact prefixLift 303160
  have htrace : WordTrace (prefixWord ++ tailWord_303160) baseStart_303160 baseEnd_303160 := by
    simpa [prefixWord, tailWord_303160, baseEnd_303160] using wordTrace_append hprefix tailTrace_303160
  have hstable : (prefixWord ++ tailWord_303160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303160).length < 2 ^ (prefixWord ++ tailWord_303160).sum := by decide
  have hdescent : baseEnd_303160 < baseStart_303160 := by decide
  rcases family_descends (prefixWord ++ tailWord_303160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303162 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_303162 : Nat := 118140960795 + 303162 * 2 ^ 59
def prefixEnd_303162 : Nat := 4983230072969 + 3 ^ 40 * 303162 * 2
def baseEnd_303162 : Nat := 17296424686494234553421

theorem tailTrace_303162 : CollatzResearch.WordTrace tailWord_303162 prefixEnd_303162 17296424686494234553421 := by
  unfold tailWord_303162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764306631925831198153935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7371484351802216528410493 2764306631925831198153935)
  ·
    refine ⟨4146459947888746797230903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2764306631925831198153935 4146459947888746797230903)
    ·
      refine ⟨6219689921833120195846355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4146459947888746797230903 6219689921833120195846355)
      ·
        refine ⟨9329534882749680293769533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6219689921833120195846355 9329534882749680293769533)
        ·
          refine ⟨3498575581031130110163575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9329534882749680293769533 3498575581031130110163575)
          ·
            refine ⟨5247863371546695165245363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498575581031130110163575 5247863371546695165245363)
            ·
              refine ⟨7871795057320042747868045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5247863371546695165245363 7871795057320042747868045)
              ·
                refine ⟨2951923146495016030450517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7871795057320042747868045 2951923146495016030450517)
                ·
                  refine ⟨17296424686494234553421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2951923146495016030450517 17296424686494234553421)
                  ·
                    rfl

theorem cell23_303162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_303162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303162 prefixEnd_303162 := by exact prefixLift 303162
  have htrace : WordTrace (prefixWord ++ tailWord_303162) baseStart_303162 baseEnd_303162 := by
    simpa [prefixWord, tailWord_303162, baseEnd_303162] using wordTrace_append hprefix tailTrace_303162
  have hstable : (prefixWord ++ tailWord_303162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303162).length < 2 ^ (prefixWord ++ tailWord_303162).sum := by decide
  have hdescent : baseEnd_303162 < baseStart_303162 := by decide
  rcases family_descends (prefixWord ++ tailWord_303162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303263 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 2, 4, 2]
def baseStart_303263 : Nat := 118140960795 + 303263 * 2 ^ 59
def prefixEnd_303263 : Nat := 4983230072969 + 3 ^ 40 * 303263 * 2
def baseEnd_303263 : Nat := 155719683724552215817825

theorem tailTrace_303263 : CollatzResearch.WordTrace tailWord_303263 prefixEnd_303263 155719683724552215817825 := by
  unfold tailWord_303263
  simp only [CollatzResearch.WordTrace]
  refine ⟨11060910300337419042042443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7373940200224946028028295 11060910300337419042042443)
  ·
    refine ⟨16591365450506128563063665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11060910300337419042042443 16591365450506128563063665)
    ·
      refine ⟨12443524087879596422297749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16591365450506128563063665 12443524087879596422297749)
      ·
        refine ⟨583290191619356082295207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12443524087879596422297749 583290191619356082295207)
        ·
          refine ⟨874935287429034123442811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583290191619356082295207 874935287429034123442811)
          ·
            refine ⟨1312402931143551185164217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874935287429034123442811 1312402931143551185164217)
            ·
              refine ⟨984302198357663388873163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312402931143551185164217 984302198357663388873163)
              ·
                refine ⟨1476453297536495083309745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984302198357663388873163 1476453297536495083309745)
                ·
                  refine ⟨1107339973152371312482309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476453297536495083309745 1107339973152371312482309)
                  ·
                    refine ⟨207626244966069621090433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107339973152371312482309 207626244966069621090433)
                    ·
                      refine ⟨155719683724552215817825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207626244966069621090433 155719683724552215817825)
                      ·
                        rfl

theorem cell23_303263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_303263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303263 prefixEnd_303263 := by exact prefixLift 303263
  have htrace : WordTrace (prefixWord ++ tailWord_303263) baseStart_303263 baseEnd_303263 := by
    simpa [prefixWord, tailWord_303263, baseEnd_303263] using wordTrace_append hprefix tailTrace_303263
  have hstable : (prefixWord ++ tailWord_303263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303263).length < 2 ^ (prefixWord ++ tailWord_303263).sum := by decide
  have hdescent : baseEnd_303263 < baseStart_303263 := by decide
  rcases family_descends (prefixWord ++ tailWord_303263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303279 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_303279 : Nat := 118140960795 + 303279 * 2 ^ 59
def prefixEnd_303279 : Nat := 4983230072969 + 3 ^ 40 * 303279 * 2
def baseEnd_303279 : Nat := 155727899415024153217751

theorem tailTrace_303279 : CollatzResearch.WordTrace tailWord_303279 prefixEnd_303279 155727899415024153217751 := by
  unfold tailWord_303279
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061493868279453774624891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7374329245519635849749927 11061493868279453774624891)
  ·
    refine ⟨16592240802419180661937337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11061493868279453774624891 16592240802419180661937337)
    ·
      refine ⟨12444180601814385496453003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16592240802419180661937337 12444180601814385496453003)
      ·
        refine ⟨18666270902721578244679505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12444180601814385496453003 18666270902721578244679505)
        ·
          refine ⟨13999703177041183683509629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18666270902721578244679505 13999703177041183683509629)
          ·
            refine ⟨5249888691390443881316111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13999703177041183683509629 5249888691390443881316111)
            ·
              refine ⟨7874833037085665821974167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5249888691390443881316111 7874833037085665821974167)
              ·
                refine ⟨11812249555628498732961251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7874833037085665821974167 11812249555628498732961251)
                ·
                  refine ⟨17718374333442748099441877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11812249555628498732961251 17718374333442748099441877)
                  ·
                    refine ⟨415274398440064408580669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17718374333442748099441877 415274398440064408580669)
                    ·
                      refine ⟨155727899415024153217751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415274398440064408580669 155727899415024153217751)
                      ·
                        rfl

theorem cell23_303279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_303279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303279 prefixEnd_303279 := by exact prefixLift 303279
  have htrace : WordTrace (prefixWord ++ tailWord_303279) baseStart_303279 baseEnd_303279 := by
    simpa [prefixWord, tailWord_303279, baseEnd_303279] using wordTrace_append hprefix tailTrace_303279
  have hstable : (prefixWord ++ tailWord_303279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303279).length < 2 ^ (prefixWord ++ tailWord_303279).sum := by decide
  have hdescent : baseEnd_303279 < baseStart_303279 := by decide
  rcases family_descends (prefixWord ++ tailWord_303279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303313 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_303313 : Nat := 118140960795 + 303313 * 2 ^ 59
def prefixEnd_303313 : Nat := 4983230072969 + 3 ^ 40 * 303313 * 2
def baseEnd_303313 : Nat := 155745357757277020192595

theorem tailTrace_303313 : CollatzResearch.WordTrace tailWord_303313 prefixEnd_303313 155745357757277020192595 := by
  unfold tailWord_303313
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062733950156277581362593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7375155966770851720908395 11062733950156277581362593)
  ·
    refine ⟨8297050462617208186021945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11062733950156277581362593 8297050462617208186021945)
    ·
      refine ⟨6222787846962906139516459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8297050462617208186021945 6222787846962906139516459)
      ·
        refine ⟨9334181770444359209274689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6222787846962906139516459 9334181770444359209274689)
        ·
          refine ⟨7000636327833269406956017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9334181770444359209274689 7000636327833269406956017)
          ·
            refine ⟨5250477245874952055217013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7000636327833269406956017 5250477245874952055217013)
            ·
              refine ⟨492232241800776755176595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5250477245874952055217013 492232241800776755176595)
              ·
                refine ⟨738348362701165132764893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492232241800776755176595 738348362701165132764893)
                ·
                  refine ⟨276880636012936924786835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738348362701165132764893 276880636012936924786835)
                  ·
                    refine ⟨415320954019405387180253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276880636012936924786835 415320954019405387180253)
                    ·
                      refine ⟨155745357757277020192595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415320954019405387180253 155745357757277020192595)
                      ·
                        rfl

theorem cell23_303313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_303313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303313 prefixEnd_303313 := by exact prefixLift 303313
  have htrace : WordTrace (prefixWord ++ tailWord_303313) baseStart_303313 baseEnd_303313 := by
    simpa [prefixWord, tailWord_303313, baseEnd_303313] using wordTrace_append hprefix tailTrace_303313
  have hstable : (prefixWord ++ tailWord_303313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303313).length < 2 ^ (prefixWord ++ tailWord_303313).sum := by decide
  have hdescent : baseEnd_303313 < baseStart_303313 := by decide
  rcases family_descends (prefixWord ++ tailWord_303313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303319 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_303319 : Nat := 118140960795 + 303319 * 2 ^ 59
def prefixEnd_303319 : Nat := 4983230072969 + 3 ^ 40 * 303319 * 2
def baseEnd_303319 : Nat := 155748438641203996717567

theorem tailTrace_303319 : CollatzResearch.WordTrace tailWord_303319 prefixEnd_303319 155748438641203996717567 := by
  unfold tailWord_303319
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062952788134540606081011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7375301858756360404054007 11062952788134540606081011)
  ·
    refine ⟨16594429182201810909121517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11062952788134540606081011 16594429182201810909121517)
    ·
      refine ⟨6222910943325679090920569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16594429182201810909121517 6222910943325679090920569)
      ·
        refine ⟨4667183207494259318190427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6222910943325679090920569 4667183207494259318190427)
        ·
          refine ⟨7000774811241388977285641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667183207494259318190427 7000774811241388977285641)
          ·
            refine ⟨5250581108431041732964231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7000774811241388977285641 5250581108431041732964231)
            ·
              refine ⟨7875871662646562599446347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250581108431041732964231 7875871662646562599446347)
              ·
                refine ⟨11813807493969843899169521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875871662646562599446347 11813807493969843899169521)
                ·
                  refine ⟨8860355620477382924377141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11813807493969843899169521 8860355620477382924377141)
                  ·
                    refine ⟨830658339419754649160357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8860355620477382924377141 830658339419754649160357)
                    ·
                      refine ⟨155748438641203996717567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 830658339419754649160357 155748438641203996717567)
                      ·
                        rfl

theorem cell23_303319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_303319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303319 prefixEnd_303319 := by exact prefixLift 303319
  have htrace : WordTrace (prefixWord ++ tailWord_303319) baseStart_303319 baseEnd_303319 := by
    simpa [prefixWord, tailWord_303319, baseEnd_303319] using wordTrace_append hprefix tailTrace_303319
  have hstable : (prefixWord ++ tailWord_303319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303319).length < 2 ^ (prefixWord ++ tailWord_303319).sum := by decide
  have hdescent : baseEnd_303319 < baseStart_303319 := by decide
  rcases family_descends (prefixWord ++ tailWord_303319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303333 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_303333 : Nat := 118140960795 + 303333 * 2 ^ 59
def prefixEnd_303333 : Nat := 4983230072969 + 3 ^ 40 * 303333 * 2
def baseEnd_303333 : Nat := 51918542456788980647501

theorem tailTrace_303333 : CollatzResearch.WordTrace tailWord_303333 prefixEnd_303333 51918542456788980647501 := by
  unfold tailWord_303333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11063463410083820997090653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7375642273389213998060435 11063463410083820997090653)
  ·
    refine ⟨4148798778781432873908995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11063463410083820997090653 4148798778781432873908995)
    ·
      refine ⟨6223198168172149310863493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148798778781432873908995 6223198168172149310863493)
      ·
        refine ⟨1166849656532277995786905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6223198168172149310863493 1166849656532277995786905)
        ·
          refine ⟨875137242399208496840179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166849656532277995786905 875137242399208496840179)
          ·
            refine ⟨1312705863598812745260269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875137242399208496840179 1312705863598812745260269)
            ·
              refine ⟨492264698849554779472601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1312705863598812745260269 492264698849554779472601)
              ·
                refine ⟨369198524137166084604451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492264698849554779472601 369198524137166084604451)
                ·
                  refine ⟨553797786205749126906677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369198524137166084604451 553797786205749126906677)
                  ·
                    refine ⟨51918542456788980647501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 553797786205749126906677 51918542456788980647501)
                    ·
                      rfl

theorem cell23_303333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_303333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303333 prefixEnd_303333 := by exact prefixLift 303333
  have htrace : WordTrace (prefixWord ++ tailWord_303333) baseStart_303333 baseEnd_303333 := by
    simpa [prefixWord, tailWord_303333, baseEnd_303333] using wordTrace_append hprefix tailTrace_303333
  have hstable : (prefixWord ++ tailWord_303333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303333).length < 2 ^ (prefixWord ++ tailWord_303333).sum := by decide
  have hdescent : baseEnd_303333 < baseStart_303333 := by decide
  rcases family_descends (prefixWord ++ tailWord_303333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303346 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_303346 : Nat := 118140960795 + 303346 * 2 ^ 59
def prefixEnd_303346 : Nat := 4983230072969 + 3 ^ 40 * 303346 * 2
def baseEnd_303346 : Nat := 51920767539625130359981

theorem tailTrace_303346 : CollatzResearch.WordTrace tailWord_303346 prefixEnd_303346 51920767539625130359981 := by
  unfold tailWord_303346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765984389759181054328473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7375958372691149478209261 2765984389759181054328473)
  ·
    refine ⟨2074488292319385790746355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2765984389759181054328473 2074488292319385790746355)
    ·
      refine ⟨3111732438479078686119533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074488292319385790746355 3111732438479078686119533)
      ·
        refine ⟨1166899664429654507294825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3111732438479078686119533 1166899664429654507294825)
        ·
          refine ⟨875174748322240880471119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166899664429654507294825 875174748322240880471119)
          ·
            refine ⟨1312762122483361320706679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875174748322240880471119 1312762122483361320706679)
            ·
              refine ⟨1969143183725041981060019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312762122483361320706679 1969143183725041981060019)
              ·
                refine ⟨2953714775587562971590029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969143183725041981060019 2953714775587562971590029)
                ·
                  refine ⟨1107643040845336114346261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2953714775587562971590029 1107643040845336114346261)
                  ·
                    refine ⟨51920767539625130359981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1107643040845336114346261 51920767539625130359981)
                    ·
                      rfl

theorem cell23_303346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_303346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303346 prefixEnd_303346 := by exact prefixLift 303346
  have htrace : WordTrace (prefixWord ++ tailWord_303346) baseStart_303346 baseEnd_303346 := by
    simpa [prefixWord, tailWord_303346, baseEnd_303346] using wordTrace_append hprefix tailTrace_303346
  have hstable : (prefixWord ++ tailWord_303346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303346).length < 2 ^ (prefixWord ++ tailWord_303346).sum := by decide
  have hdescent : baseEnd_303346 < baseStart_303346 := by decide
  rcases family_descends (prefixWord ++ tailWord_303346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303353 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 7, 2, 2]
def baseStart_303353 : Nat := 118140960795 + 303353 * 2 ^ 59
def prefixEnd_303353 : Nat := 4983230072969 + 3 ^ 40 * 303353 * 2
def baseEnd_303353 : Nat := 155765896983456863692411

theorem tailTrace_303353 : CollatzResearch.WordTrace tailWord_303353 prefixEnd_303353 155765896983456863692411 := by
  unfold tailWord_303353
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064192870011364412818713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7376128580007576275212475 11064192870011364412818713)
  ·
    refine ⟨8298144652508523309614035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11064192870011364412818713 8298144652508523309614035)
    ·
      refine ⟨12447216978762784964421053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8298144652508523309614035 12447216978762784964421053)
      ·
        refine ⟨4667706367036044361657895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12447216978762784964421053 4667706367036044361657895)
        ·
          refine ⟨7001559550554066542486843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667706367036044361657895 7001559550554066542486843)
          ·
            refine ⟨10502339325831099813730265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7001559550554066542486843 10502339325831099813730265)
            ·
              refine ⟨7876754494373324860297699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10502339325831099813730265 7876754494373324860297699)
              ·
                refine ⟨11815131741559987290446549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7876754494373324860297699 11815131741559987290446549)
                ·
                  refine ⟨276917150192812202119841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11815131741559987290446549 276917150192812202119841)
                  ·
                    refine ⟨207687862644609151589881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 276917150192812202119841 207687862644609151589881)
                    ·
                      refine ⟨155765896983456863692411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207687862644609151589881 155765896983456863692411)
                      ·
                        rfl

theorem cell23_303353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_303353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303353 prefixEnd_303353 := by exact prefixLift 303353
  have htrace : WordTrace (prefixWord ++ tailWord_303353) baseStart_303353 baseEnd_303353 := by
    simpa [prefixWord, tailWord_303353, baseEnd_303353] using wordTrace_append hprefix tailTrace_303353
  have hstable : (prefixWord ++ tailWord_303353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303353).length < 2 ^ (prefixWord ++ tailWord_303353).sum := by decide
  have hdescent : baseEnd_303353 < baseStart_303353 := by decide
  rcases family_descends (prefixWord ++ tailWord_303353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303363 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 2, 4]
def baseStart_303363 : Nat := 118140960795 + 303363 * 2 ^ 59
def prefixEnd_303363 : Nat := 4983230072969 + 3 ^ 40 * 303363 * 2
def baseEnd_303363 : Nat := 51923677263333941522455

theorem tailTrace_303363 : CollatzResearch.WordTrace tailWord_303363 prefixEnd_303363 51923677263333941522455 := by
  unfold tailWord_303363
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064557599975136120682743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7376371733316757413788495 11064557599975136120682743)
  ·
    refine ⟨16596836399962704181024115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11064557599975136120682743 16596836399962704181024115)
    ·
      refine ⟨24895254599944056271536173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16596836399962704181024115 24895254599944056271536173)
      ·
        refine ⟨9335720474979021101826065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24895254599944056271536173 9335720474979021101826065)
        ·
          refine ⟨7001790356234265826369549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9335720474979021101826065 7001790356234265826369549)
          ·
            refine ⟨2625671383587849684888581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7001790356234265826369549 2625671383587849684888581)
            ·
              refine ⟨492313384422721815916609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2625671383587849684888581 492313384422721815916609)
              ·
                refine ⟨369235038317041361937457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492313384422721815916609 369235038317041361937457)
                ·
                  refine ⟨276926278737781021453093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369235038317041361937457 276926278737781021453093)
                  ·
                    refine ⟨51923677263333941522455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 276926278737781021453093 51923677263333941522455)
                    ·
                      rfl

theorem cell23_303363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 4].length) (baseStart_303363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303363 prefixEnd_303363 := by exact prefixLift 303363
  have htrace : WordTrace (prefixWord ++ tailWord_303363) baseStart_303363 baseEnd_303363 := by
    simpa [prefixWord, tailWord_303363, baseEnd_303363] using wordTrace_append hprefix tailTrace_303363
  have hstable : (prefixWord ++ tailWord_303363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303363).length < 2 ^ (prefixWord ++ tailWord_303363).sum := by decide
  have hdescent : baseEnd_303363 < baseStart_303363 := by decide
  rcases family_descends (prefixWord ++ tailWord_303363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303379 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_303379 : Nat := 118140960795 + 303379 * 2 ^ 59
def prefixEnd_303379 : Nat := 4983230072969 + 3 ^ 40 * 303379 * 2
def baseEnd_303379 : Nat := 155779247480473761967291

theorem tailTrace_303379 : CollatzResearch.WordTrace tailWord_303379 prefixEnd_303379 155779247480473761967291 := by
  unfold tailWord_303379
  simp only [CollatzResearch.WordTrace]
  refine ⟨11065141167917170853265191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7376760778611447235510127 11065141167917170853265191)
  ·
    refine ⟨16597711751875756279897787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11065141167917170853265191 16597711751875756279897787)
    ·
      refine ⟨24896567627813634419846681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16597711751875756279897787 24896567627813634419846681)
      ·
        refine ⟨18672425720860225814885011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24896567627813634419846681 18672425720860225814885011)
        ·
          refine ⟨28008638581290338722327517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18672425720860225814885011 28008638581290338722327517)
          ·
            refine ⟨10503239467983877020872819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28008638581290338722327517 10503239467983877020872819)
            ·
              refine ⟨15754859201975815531309229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10503239467983877020872819 15754859201975815531309229)
              ·
                refine ⟨5908072200740930824240961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15754859201975815531309229 5908072200740930824240961)
                ·
                  refine ⟨4431054150555698118180721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908072200740930824240961 4431054150555698118180721)
                  ·
                    refine ⟨3323290612916773588635541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431054150555698118180721 3323290612916773588635541)
                    ·
                      refine ⟨155779247480473761967291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3323290612916773588635541 155779247480473761967291)
                      ·
                        rfl

theorem cell23_303379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_303379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303379 prefixEnd_303379 := by exact prefixLift 303379
  have htrace : WordTrace (prefixWord ++ tailWord_303379) baseStart_303379 baseEnd_303379 := by
    simpa [prefixWord, tailWord_303379, baseEnd_303379] using wordTrace_append hprefix tailTrace_303379
  have hstable : (prefixWord ++ tailWord_303379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303379).length < 2 ^ (prefixWord ++ tailWord_303379).sum := by decide
  have hdescent : baseEnd_303379 < baseStart_303379 := by decide
  rcases family_descends (prefixWord ++ tailWord_303379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303383 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_303383 : Nat := 118140960795 + 303383 * 2 ^ 59
def prefixEnd_303383 : Nat := 4983230072969 + 3 ^ 40 * 303383 * 2
def baseEnd_303383 : Nat := 155781301403091746317273

theorem tailTrace_303383 : CollatzResearch.WordTrace tailWord_303383 prefixEnd_303383 155781301403091746317273 := by
  unfold tailWord_303383
  simp only [CollatzResearch.WordTrace]
  refine ⟨11065287059902679536410803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7376858039935119690940535 11065287059902679536410803)
  ·
    refine ⟨16597930589854019304616205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11065287059902679536410803 16597930589854019304616205)
    ·
      refine ⟨6224223971195257239231077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16597930589854019304616205 6224223971195257239231077)
      ·
        refine ⟨1167041994599110732355827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6224223971195257239231077 1167041994599110732355827)
        ·
          refine ⟨1750562991898666098533741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167041994599110732355827 1750562991898666098533741)
          ·
            refine ⟨656461121961999786950153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1750562991898666098533741 656461121961999786950153)
            ·
              refine ⟨492345841471499840212615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656461121961999786950153 492345841471499840212615)
              ·
                refine ⟨738518762207249760318923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492345841471499840212615 738518762207249760318923)
                ·
                  refine ⟨1107778143310874640478385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738518762207249760318923 1107778143310874640478385)
                  ·
                    refine ⟨830833607483155980358789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1107778143310874640478385 830833607483155980358789)
                    ·
                      refine ⟨155781301403091746317273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 830833607483155980358789 155781301403091746317273)
                      ·
                        rfl

theorem cell23_303383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_303383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303383 prefixEnd_303383 := by exact prefixLift 303383
  have htrace : WordTrace (prefixWord ++ tailWord_303383) baseStart_303383 baseEnd_303383 := by
    simpa [prefixWord, tailWord_303383, baseEnd_303383] using wordTrace_append hprefix tailTrace_303383
  have hstable : (prefixWord ++ tailWord_303383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303383).length < 2 ^ (prefixWord ++ tailWord_303383).sum := by decide
  have hdescent : baseEnd_303383 < baseStart_303383 := by decide
  rcases family_descends (prefixWord ++ tailWord_303383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303419 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 12]
def baseStart_303419 : Nat := 118140960795 + 303419 * 2 ^ 59
def prefixEnd_303419 : Nat := 4983230072969 + 3 ^ 40 * 303419 * 2
def baseEnd_303419 : Nat := 51933262235551201822369

theorem tailTrace_303419 : CollatzResearch.WordTrace tailWord_303419 prefixEnd_303419 51933262235551201822369 := by
  unfold tailWord_303419
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066600087772257684721311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7377733391848171789814207 11066600087772257684721311)
  ·
    refine ⟨16599900131658386527081967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11066600087772257684721311 16599900131658386527081967)
    ·
      refine ⟨24899850197487579790622951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16599900131658386527081967 24899850197487579790622951)
      ·
        refine ⟨37349775296231369685934427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24899850197487579790622951 37349775296231369685934427)
        ·
          refine ⟨56024662944347054528901641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37349775296231369685934427 56024662944347054528901641)
          ·
            refine ⟨42018497208260290896676231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56024662944347054528901641 42018497208260290896676231)
            ·
              refine ⟨63027745812390436345014347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42018497208260290896676231 63027745812390436345014347)
              ·
                refine ⟨94541618718585654517521521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63027745812390436345014347 94541618718585654517521521)
                ·
                  refine ⟨70906214038939240888141141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94541618718585654517521521 70906214038939240888141141)
                  ·
                    refine ⟨51933262235551201822369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 70906214038939240888141141 51933262235551201822369)
                    ·
                      rfl

theorem cell23_303419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_303419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303419 prefixEnd_303419 := by exact prefixLift 303419
  have htrace : WordTrace (prefixWord ++ tailWord_303419) baseStart_303419 baseEnd_303419 := by
    simpa [prefixWord, tailWord_303419, baseEnd_303419] using wordTrace_append hprefix tailTrace_303419
  have hstable : (prefixWord ++ tailWord_303419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303419).length < 2 ^ (prefixWord ++ tailWord_303419).sum := by decide
  have hdescent : baseEnd_303419 < baseStart_303419 := by decide
  rcases family_descends (prefixWord ++ tailWord_303419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303436 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_303436 : Nat := 118140960795 + 303436 * 2 ^ 59
def prefixEnd_303436 : Nat := 4983230072969 + 3 ^ 40 * 303436 * 2
def baseEnd_303436 : Nat := 51936171959260012984843

theorem tailTrace_303436 : CollatzResearch.WordTrace tailWord_303436 prefixEnd_303436 51936171959260012984843 := by
  unfold tailWord_303436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5533610064355334794045081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7378146752473779725393441 5533610064355334794045081)
  ·
    refine ⟨4150207548266501095533811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5533610064355334794045081 4150207548266501095533811)
    ·
      refine ⟨6225311322399751643300717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4150207548266501095533811 6225311322399751643300717)
      ·
        refine ⟨2334491745899906866237769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6225311322399751643300717 2334491745899906866237769)
        ·
          refine ⟨1750868809424930149678327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334491745899906866237769 1750868809424930149678327)
          ·
            refine ⟨2626303214137395224517491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750868809424930149678327 2626303214137395224517491)
            ·
              refine ⟨3939454821206092836776237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626303214137395224517491 3939454821206092836776237)
              ·
                refine ⟨1477295557952284813791089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3939454821206092836776237 1477295557952284813791089)
                ·
                  refine ⟨1107971668464213610343317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1477295557952284813791089 1107971668464213610343317)
                  ·
                    refine ⟨51936171959260012984843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1107971668464213610343317 51936171959260012984843)
                    ·
                      rfl

theorem cell23_303436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_303436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303436 prefixEnd_303436 := by exact prefixLift 303436
  have htrace : WordTrace (prefixWord ++ tailWord_303436) baseStart_303436 baseEnd_303436 := by
    simpa [prefixWord, tailWord_303436, baseEnd_303436] using wordTrace_append hprefix tailTrace_303436
  have hstable : (prefixWord ++ tailWord_303436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303436).length < 2 ^ (prefixWord ++ tailWord_303436).sum := by decide
  have hdescent : baseEnd_303436 < baseStart_303436 := by decide
  rcases family_descends (prefixWord ++ tailWord_303436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303443 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 1, 4, 2]
def baseStart_303443 : Nat := 118140960795 + 303443 * 2 ^ 59
def prefixEnd_303443 : Nat := 4983230072969 + 3 ^ 40 * 303443 * 2
def baseEnd_303443 : Nat := 155812110242361511566997

theorem tailTrace_303443 : CollatzResearch.WordTrace tailWord_303443 prefixEnd_303443 155812110242361511566997 := by
  unfold tailWord_303443
  simp only [CollatzResearch.WordTrace]
  refine ⟨11067475439685309783594983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7378316959790206522396655 11067475439685309783594983)
  ·
    refine ⟨16601213159527964675392475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11067475439685309783594983 16601213159527964675392475)
    ·
      refine ⟨24901819739291947013088713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16601213159527964675392475 24901819739291947013088713)
      ·
        refine ⟨18676364804468960259816535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24901819739291947013088713 18676364804468960259816535)
        ·
          refine ⟨28014547206703440389724803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18676364804468960259816535 28014547206703440389724803)
          ·
            refine ⟨42021820810055160584587205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28014547206703440389724803 42021820810055160584587205)
            ·
              refine ⟨7879091401885342609610101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42021820810055160584587205 7879091401885342609610101)
              ·
                refine ⟨738664818926750869650947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7879091401885342609610101 738664818926750869650947)
                ·
                  refine ⟨1107997228390126304476421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738664818926750869650947 1107997228390126304476421)
                  ·
                    refine ⟨207749480323148682089329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107997228390126304476421 207749480323148682089329)
                    ·
                      refine ⟨155812110242361511566997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207749480323148682089329 155812110242361511566997)
                      ·
                        rfl

theorem cell23_303443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4, 2].length) (baseStart_303443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303443 prefixEnd_303443 := by exact prefixLift 303443
  have htrace : WordTrace (prefixWord ++ tailWord_303443) baseStart_303443 baseEnd_303443 := by
    simpa [prefixWord, tailWord_303443, baseEnd_303443] using wordTrace_append hprefix tailTrace_303443
  have hstable : (prefixWord ++ tailWord_303443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303443).length < 2 ^ (prefixWord ++ tailWord_303443).sum := by decide
  have hdescent : baseEnd_303443 < baseStart_303443 := by decide
  rcases family_descends (prefixWord ++ tailWord_303443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303460 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_303460 : Nat := 118140960795 + 303460 * 2 ^ 59
def prefixEnd_303460 : Nat := 4983230072969 + 3 ^ 40 * 303460 * 2
def baseEnd_303460 : Nat := 155820839413487945054419

theorem tailTrace_303460 : CollatzResearch.WordTrace tailWord_303460 prefixEnd_303460 155820839413487945054419 := by
  unfold tailWord_303460
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534047740311860843481917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7378730320415814457975889 5534047740311860843481917)
  ·
    refine ⟨2075267902616947816305719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5534047740311860843481917 2075267902616947816305719)
    ·
      refine ⟨3112901853925421724458579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075267902616947816305719 3112901853925421724458579)
      ·
        refine ⟨4669352780888132586687869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112901853925421724458579 4669352780888132586687869)
        ·
          refine ⟨1751007292833049720007951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4669352780888132586687869 1751007292833049720007951)
          ·
            refine ⟨2626510939249574580011927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751007292833049720007951 2626510939249574580011927)
            ·
              refine ⟨3939766408874361870017891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626510939249574580011927 3939766408874361870017891)
              ·
                refine ⟨5909649613311542805026837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939766408874361870017891 5909649613311542805026837)
                ·
                  refine ⟨277014825623978568985633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5909649613311542805026837 277014825623978568985633)
                  ·
                    refine ⟨207761119217983926739225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277014825623978568985633 207761119217983926739225)
                    ·
                      refine ⟨155820839413487945054419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207761119217983926739225 155820839413487945054419)
                      ·
                        rfl

theorem cell23_303460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_303460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303460 prefixEnd_303460 := by exact prefixLift 303460
  have htrace : WordTrace (prefixWord ++ tailWord_303460) baseStart_303460 baseEnd_303460 := by
    simpa [prefixWord, tailWord_303460, baseEnd_303460] using wordTrace_append hprefix tailTrace_303460
  have hstable : (prefixWord ++ tailWord_303460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303460).length < 2 ^ (prefixWord ++ tailWord_303460).sum := by decide
  have hdescent : baseEnd_303460 < baseStart_303460 := by decide
  rcases family_descends (prefixWord ++ tailWord_303460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303463 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_303463 : Nat := 118140960795 + 303463 * 2 ^ 59
def prefixEnd_303463 : Nat := 4983230072969 + 3 ^ 40 * 303463 * 2
def baseEnd_303463 : Nat := 155822379855451433316905

theorem tailTrace_303463 : CollatzResearch.WordTrace tailWord_303463 prefixEnd_303463 155822379855451433316905 := by
  unfold tailWord_303463
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068204899612853199323043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7378803266408568799548695 11068204899612853199323043)
  ·
    refine ⟨16602307349419279798984565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11068204899612853199323043 16602307349419279798984565)
    ·
      refine ⟨1556466314008057481154803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16602307349419279798984565 1556466314008057481154803)
      ·
        refine ⟨2334699471012086221732205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556466314008057481154803 2334699471012086221732205)
        ·
          refine ⟨875512301629532333149577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2334699471012086221732205 875512301629532333149577)
          ·
            refine ⟨656634226222149249862183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875512301629532333149577 656634226222149249862183)
            ·
              refine ⟨984951339333223874793275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656634226222149249862183 984951339333223874793275)
              ·
                refine ⟨1477427008999835812189913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984951339333223874793275 1477427008999835812189913)
                ·
                  refine ⟨1108070256749876859142435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1477427008999835812189913 1108070256749876859142435)
                  ·
                    refine ⟨1662105385124815288713653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108070256749876859142435 1662105385124815288713653)
                    ·
                      refine ⟨155822379855451433316905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1662105385124815288713653 155822379855451433316905)
                      ·
                        rfl

theorem cell23_303463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_303463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303463 prefixEnd_303463 := by exact prefixLift 303463
  have htrace : WordTrace (prefixWord ++ tailWord_303463) baseStart_303463 baseEnd_303463 := by
    simpa [prefixWord, tailWord_303463, baseEnd_303463] using wordTrace_append hprefix tailTrace_303463
  have hstable : (prefixWord ++ tailWord_303463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303463).length < 2 ^ (prefixWord ++ tailWord_303463).sum := by decide
  have hdescent : baseEnd_303463 < baseStart_303463 := by decide
  rcases family_descends (prefixWord ++ tailWord_303463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303477 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_303477 : Nat := 118140960795 + 303477 * 2 ^ 59
def prefixEnd_303477 : Nat := 4983230072969 + 3 ^ 40 * 303477 * 2
def baseEnd_303477 : Nat := 155829568584614378541841

theorem tailTrace_303477 : CollatzResearch.WordTrace tailWord_303477 prefixEnd_303477 155829568584614378541841 := by
  unfold tailWord_303477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068715521562133590332685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7379143681041422393555123 11068715521562133590332685)
  ·
    refine ⟨4150768320585800096374757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11068715521562133590332685 4150768320585800096374757)
    ·
      refine ⟨778269060109837518070267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4150768320585800096374757 778269060109837518070267)
      ·
        refine ⟨1167403590164756277105401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778269060109837518070267 1167403590164756277105401)
        ·
          refine ⟨875552692623567207829051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167403590164756277105401 875552692623567207829051)
          ·
            refine ⟨1313329038935350811743577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875552692623567207829051 1313329038935350811743577)
            ·
              refine ⟨984996779201513108807683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313329038935350811743577 984996779201513108807683)
              ·
                refine ⟨1477495168802269663211525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984996779201513108807683 1477495168802269663211525)
                ·
                  refine ⟨277030344150425561852161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1477495168802269663211525 277030344150425561852161)
                  ·
                    refine ⟨207772758112819171389121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277030344150425561852161 207772758112819171389121)
                    ·
                      refine ⟨155829568584614378541841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207772758112819171389121 155829568584614378541841)
                      ·
                        rfl

theorem cell23_303477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_303477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303477 prefixEnd_303477 := by exact prefixLift 303477
  have htrace : WordTrace (prefixWord ++ tailWord_303477) baseStart_303477 baseEnd_303477 := by
    simpa [prefixWord, tailWord_303477, baseEnd_303477] using wordTrace_append hprefix tailTrace_303477
  have hstable : (prefixWord ++ tailWord_303477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303477).length < 2 ^ (prefixWord ++ tailWord_303477).sum := by decide
  have hdescent : baseEnd_303477 < baseStart_303477 := by decide
  rcases family_descends (prefixWord ++ tailWord_303477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303483 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 7]
def baseStart_303483 : Nat := 118140960795 + 303483 * 2 ^ 59
def prefixEnd_303483 : Nat := 4983230072969 + 3 ^ 40 * 303483 * 2
def baseEnd_303483 : Nat := 17314738829837928340757

theorem tailTrace_303483 : CollatzResearch.WordTrace tailWord_303483 prefixEnd_303483 17314738829837928340757 := by
  unfold tailWord_303483
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068934359540396615051103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7379289573026931076700735 11068934359540396615051103)
  ·
    refine ⟨16603401539310594922576655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11068934359540396615051103 16603401539310594922576655)
    ·
      refine ⟨24905102308965892383864983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16603401539310594922576655 24905102308965892383864983)
      ·
        refine ⟨37357653463448838575797475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24905102308965892383864983 37357653463448838575797475)
        ·
          refine ⟨56036480195173257863696213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37357653463448838575797475 56036480195173257863696213)
          ·
            refine ⟨328338751143593307795095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 56036480195173257863696213 328338751143593307795095)
            ·
              refine ⟨492508126715389961692643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328338751143593307795095 492508126715389961692643)
              ·
                refine ⟨738762190073084942538965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492508126715389961692643 738762190073084942538965)
                ·
                  refine ⟨17314738829837928340757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 738762190073084942538965 17314738829837928340757)
                  ·
                    rfl

theorem cell23_303483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 7].length) (baseStart_303483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303483 prefixEnd_303483 := by exact prefixLift 303483
  have htrace : WordTrace (prefixWord ++ tailWord_303483) baseStart_303483 baseEnd_303483 := by
    simpa [prefixWord, tailWord_303483, baseEnd_303483] using wordTrace_append hprefix tailTrace_303483
  have hstable : (prefixWord ++ tailWord_303483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303483).length < 2 ^ (prefixWord ++ tailWord_303483).sum := by decide
  have hdescent : baseEnd_303483 < baseStart_303483 := by decide
  rcases family_descends (prefixWord ++ tailWord_303483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303513 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 2, 5]
def baseStart_303513 : Nat := 118140960795 + 303513 * 2 ^ 59
def prefixEnd_303513 : Nat := 4983230072969 + 3 ^ 40 * 303513 * 2
def baseEnd_303513 : Nat := 51949351296058745897225

theorem tailTrace_303513 : CollatzResearch.WordTrace tailWord_303513 prefixEnd_303513 51949351296058745897225 := by
  unfold tailWord_303513
  simp only [CollatzResearch.WordTrace]
  refine ⟨11070028549431711738643193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7380019032954474492428795 11070028549431711738643193)
  ·
    refine ⟨8302521412073783803982395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11070028549431711738643193 8302521412073783803982395)
    ·
      refine ⟨12453782118110675705973593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8302521412073783803982395 12453782118110675705973593)
      ·
        refine ⟨9340336588583006779480195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12453782118110675705973593 9340336588583006779480195)
        ·
          refine ⟨14010504882874510169220293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9340336588583006779480195 14010504882874510169220293)
          ·
            refine ⟨2626969665538970656728805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14010504882874510169220293 2626969665538970656728805)
            ·
              refine ⟨492556812288556998136651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2626969665538970656728805 492556812288556998136651)
              ·
                refine ⟨738835218432835497204977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492556812288556998136651 738835218432835497204977)
                ·
                  refine ⟨554126413824626622903733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 738835218432835497204977 554126413824626622903733)
                  ·
                    refine ⟨51949351296058745897225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 554126413824626622903733 51949351296058745897225)
                    ·
                      rfl

theorem cell23_303513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_303513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303513 prefixEnd_303513 := by exact prefixLift 303513
  have htrace : WordTrace (prefixWord ++ tailWord_303513) baseStart_303513 baseEnd_303513 := by
    simpa [prefixWord, tailWord_303513, baseEnd_303513] using wordTrace_append hprefix tailTrace_303513
  have hstable : (prefixWord ++ tailWord_303513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303513).length < 2 ^ (prefixWord ++ tailWord_303513).sum := by decide
  have hdescent : baseEnd_303513 < baseStart_303513 := by decide
  rcases family_descends (prefixWord ++ tailWord_303513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303550 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_303550 : Nat := 118140960795 + 303550 * 2 ^ 59
def prefixEnd_303550 : Nat := 4983230072969 + 3 ^ 40 * 303550 * 2
def baseEnd_303550 : Nat := 155867052672392592929005

theorem tailTrace_303550 : CollatzResearch.WordTrace tailWord_303550 prefixEnd_303550 155867052672392592929005 := by
  unfold tailWord_303550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383922256287208382217513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7380918700198444705160069 1383922256287208382217513)
  ·
    refine ⟨1037941692215406286663135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1383922256287208382217513 1037941692215406286663135)
    ·
      refine ⟨1556912538323109429994703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037941692215406286663135 1556912538323109429994703)
      ·
        refine ⟨2335368807484664144992055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556912538323109429994703 2335368807484664144992055)
        ·
          refine ⟨3503053211226996217488083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335368807484664144992055 3503053211226996217488083)
          ·
            refine ⟨5254579816840494326232125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503053211226996217488083 5254579816840494326232125)
            ·
              refine ⟨1970467431315185372337047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5254579816840494326232125 1970467431315185372337047)
              ·
                refine ⟨2955701146972778058505571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970467431315185372337047 2955701146972778058505571)
                ·
                  refine ⟨4433551720459167087758357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955701146972778058505571 4433551720459167087758357)
                  ·
                    refine ⟨207822736896523457238673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4433551720459167087758357 207822736896523457238673)
                    ·
                      refine ⟨155867052672392592929005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207822736896523457238673 155867052672392592929005)
                      ·
                        rfl

theorem cell23_303550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_303550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303550 prefixEnd_303550 := by exact prefixLift 303550
  have htrace : WordTrace (prefixWord ++ tailWord_303550) baseStart_303550 baseEnd_303550 := by
    simpa [prefixWord, tailWord_303550, baseEnd_303550] using wordTrace_append hprefix tailTrace_303550
  have hstable : (prefixWord ++ tailWord_303550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303550).length < 2 ^ (prefixWord ++ tailWord_303550).sum := by decide
  have hdescent : baseEnd_303550 < baseStart_303550 := by decide
  rcases family_descends (prefixWord ++ tailWord_303550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303560 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 3, 4]
def baseStart_303560 : Nat := 118140960795 + 303560 * 2 ^ 59
def prefixEnd_303560 : Nat := 4983230072969 + 3 ^ 40 * 303560 * 2
def baseEnd_303560 : Nat := 51957395826312517934653

theorem tailTrace_303560 : CollatzResearch.WordTrace tailWord_303560 prefixEnd_303560 51957395826312517934653 := by
  unfold tailWord_303560
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535871390130719382802067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7381161853507625843736089 5535871390130719382802067)
  ·
    refine ⟨8303807085196079074203101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5535871390130719382802067 8303807085196079074203101)
    ·
      refine ⟨3113927656948529652826163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8303807085196079074203101 3113927656948529652826163)
      ·
        refine ⟨4670891485422794479239245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113927656948529652826163 4670891485422794479239245)
        ·
          refine ⟨1751584307033547929714717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4670891485422794479239245 1751584307033547929714717)
          ·
            refine ⟨656844115137580473643019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1751584307033547929714717 656844115137580473643019)
            ·
              refine ⟨985266172706370710464529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656844115137580473643019 985266172706370710464529)
              ·
                refine ⟨738949629529778032848397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985266172706370710464529 738949629529778032848397)
                ·
                  refine ⟨277106111073666762318149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738949629529778032848397 277106111073666762318149)
                  ·
                    refine ⟨51957395826312517934653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277106111073666762318149 51957395826312517934653)
                    ·
                      rfl

theorem cell23_303560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_303560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303560 prefixEnd_303560 := by exact prefixLift 303560
  have htrace : WordTrace (prefixWord ++ tailWord_303560) baseStart_303560 baseEnd_303560 := by
    simpa [prefixWord, tailWord_303560, baseEnd_303560] using wordTrace_append hprefix tailTrace_303560
  have hstable : (prefixWord ++ tailWord_303560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303560).length < 2 ^ (prefixWord ++ tailWord_303560).sum := by decide
  have hdescent : baseEnd_303560 < baseStart_303560 := by decide
  rcases family_descends (prefixWord ++ tailWord_303560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303577 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 1, 4]
def baseStart_303577 : Nat := 118140960795 + 303577 * 2 ^ 59
def prefixEnd_303577 : Nat := 4983230072969 + 3 ^ 40 * 303577 * 2
def baseEnd_303577 : Nat := 51960305550021329097127

theorem tailTrace_303577 : CollatzResearch.WordTrace tailWord_303577 prefixEnd_303577 51960305550021329097127 := by
  unfold tailWord_303577
  simp only [CollatzResearch.WordTrace]
  refine ⟨11072362821199850668972985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7381575214133233779315323 11072362821199850668972985)
  ·
    refine ⟨8304272115899888001729739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11072362821199850668972985 8304272115899888001729739)
    ·
      refine ⟨12456408173849832002594609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8304272115899888001729739 12456408173849832002594609)
      ·
        refine ⟨9342306130387374001945957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12456408173849832002594609 9342306130387374001945957)
        ·
          refine ⟨1751682399447632625364867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9342306130387374001945957 1751682399447632625364867)
          ·
            refine ⟨2627523599171448938047301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751682399447632625364867 2627523599171448938047301)
            ·
              refine ⟨492660674844646675883869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2627523599171448938047301 492660674844646675883869)
              ·
                refine ⟨184747753066742503456451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 492660674844646675883869 184747753066742503456451)
                ·
                  refine ⟨277121629600113755184677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184747753066742503456451 277121629600113755184677)
                  ·
                    refine ⟨51960305550021329097127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277121629600113755184677 51960305550021329097127)
                    ·
                      rfl

theorem cell23_303577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 4].length) (baseStart_303577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303577 prefixEnd_303577 := by exact prefixLift 303577
  have htrace : WordTrace (prefixWord ++ tailWord_303577) baseStart_303577 baseEnd_303577 := by
    simpa [prefixWord, tailWord_303577, baseEnd_303577] using wordTrace_append hprefix tailTrace_303577
  have hstable : (prefixWord ++ tailWord_303577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303577).length < 2 ^ (prefixWord ++ tailWord_303577).sum := by decide
  have hdescent : baseEnd_303577 < baseStart_303577 := by decide
  rcases family_descends (prefixWord ++ tailWord_303577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303610 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2]
def baseStart_303610 : Nat := 118140960795 + 303610 * 2 ^ 59
def prefixEnd_303610 : Nat := 4983230072969 + 3 ^ 40 * 303610 * 2
def baseEnd_303610 : Nat := 155897861511662358178729

theorem tailTrace_303610 : CollatzResearch.WordTrace tailWord_303610 prefixEnd_303610 155897861511662358178729 := by
  unfold tailWord_303610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768391607520074326231071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7382377620053531536616189 2768391607520074326231071)
  ·
    refine ⟨4152587411280111489346607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2768391607520074326231071 4152587411280111489346607)
    ·
      refine ⟨6228881116920167234019911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152587411280111489346607 6228881116920167234019911)
      ·
        refine ⟨9343321675380250851029867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6228881116920167234019911 9343321675380250851029867)
        ·
          refine ⟨14014982513070376276544801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9343321675380250851029867 14014982513070376276544801)
          ·
            refine ⟨10511236884802782207408601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14014982513070376276544801 10511236884802782207408601)
            ·
              refine ⟨7883427663602086655556451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10511236884802782207408601 7883427663602086655556451)
              ·
                refine ⟨11825141495403129983334677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7883427663602086655556451 11825141495403129983334677)
                ·
                  refine ⟨554303507597021717968813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11825141495403129983334677 554303507597021717968813)
                  ·
                    refine ⟨207863815348883144238305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554303507597021717968813 207863815348883144238305)
                    ·
                      refine ⟨155897861511662358178729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207863815348883144238305 155897861511662358178729)
                      ·
                        rfl

theorem cell23_303610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_303610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303610 prefixEnd_303610 := by exact prefixLift 303610
  have htrace : WordTrace (prefixWord ++ tailWord_303610) baseStart_303610 baseEnd_303610 := by
    simpa [prefixWord, tailWord_303610, baseEnd_303610] using wordTrace_append hprefix tailTrace_303610
  have hstable : (prefixWord ++ tailWord_303610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303610).length < 2 ^ (prefixWord ++ tailWord_303610).sum := by decide
  have hdescent : baseEnd_303610 < baseStart_303610 := by decide
  rcases family_descends (prefixWord ++ tailWord_303610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303617 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_303617 : Nat := 118140960795 + 303617 * 2 ^ 59
def prefixEnd_303617 : Nat := 4983230072969 + 3 ^ 40 * 303617 * 2
def baseEnd_303617 : Nat := 155901455876243830791197

theorem tailTrace_303617 : CollatzResearch.WordTrace tailWord_303617 prefixEnd_303617 155901455876243830791197 := by
  unfold tailWord_303617
  simp only [CollatzResearch.WordTrace]
  refine ⟨11073821741054937500429105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7382547827369958333619403 11073821741054937500429105)
  ·
    refine ⟨8305366305791203125321829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11073821741054937500429105 8305366305791203125321829)
    ·
      refine ⟨1557256182335850585997843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8305366305791203125321829 1557256182335850585997843)
      ·
        refine ⟨2335884273503775878996765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557256182335850585997843 2335884273503775878996765)
        ·
          refine ⟨875956602563915954623787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2335884273503775878996765 875956602563915954623787)
          ·
            refine ⟨1313934903845873931935681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875956602563915954623787 1313934903845873931935681)
            ·
              refine ⟨985451177884405448951761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313934903845873931935681 985451177884405448951761)
              ·
                refine ⟨739088383413304086713821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985451177884405448951761 739088383413304086713821)
                ·
                  refine ⟨277158143779989032517683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739088383413304086713821 277158143779989032517683)
                  ·
                    refine ⟨415737215669983548776525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277158143779989032517683 415737215669983548776525)
                    ·
                      refine ⟨155901455876243830791197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415737215669983548776525 155901455876243830791197)
                      ·
                        rfl

theorem cell23_303617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_303617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303617 prefixEnd_303617 := by exact prefixLift 303617
  have htrace : WordTrace (prefixWord ++ tailWord_303617) baseStart_303617 baseEnd_303617 := by
    simpa [prefixWord, tailWord_303617, baseEnd_303617] using wordTrace_append hprefix tailTrace_303617
  have hstable : (prefixWord ++ tailWord_303617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303617).length < 2 ^ (prefixWord ++ tailWord_303617).sum := by decide
  have hdescent : baseEnd_303617 < baseStart_303617 := by decide
  rcases family_descends (prefixWord ++ tailWord_303617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303651 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 1, 1, 3]
def baseStart_303651 : Nat := 118140960795 + 303651 * 2 ^ 59
def prefixEnd_303651 : Nat := 4983230072969 + 3 ^ 40 * 303651 * 2
def baseEnd_303651 : Nat := 155918914218496697766041

theorem tailTrace_303651 : CollatzResearch.WordTrace tailWord_303651 prefixEnd_303651 155918914218496697766041 := by
  unfold tailWord_303651
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075061822931761307166807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7383374548621174204777871 11075061822931761307166807)
  ·
    refine ⟨16612592734397641960750211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11075061822931761307166807 16612592734397641960750211)
    ·
      refine ⟨24918889101596462941125317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16612592734397641960750211 24918889101596462941125317)
      ·
        refine ⟨4672291706549336801460997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24918889101596462941125317 4672291706549336801460997)
        ·
          refine ⟨876054694978000650273937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4672291706549336801460997 876054694978000650273937)
          ·
            refine ⟨657041021233500487705453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876054694978000650273937 657041021233500487705453)
            ·
              refine ⟨246390382962562682889545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 657041021233500487705453 246390382962562682889545)
              ·
                refine ⟨184792787221922012167159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246390382962562682889545 184792787221922012167159)
                ·
                  refine ⟨277189180832883018250739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184792787221922012167159 277189180832883018250739)
                  ·
                    refine ⟨415783771249324527376109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277189180832883018250739 415783771249324527376109)
                    ·
                      refine ⟨155918914218496697766041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415783771249324527376109 155918914218496697766041)
                      ·
                        rfl

theorem cell23_303651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_303651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303651 prefixEnd_303651 := by exact prefixLift 303651
  have htrace : WordTrace (prefixWord ++ tailWord_303651) baseStart_303651 baseEnd_303651 := by
    simpa [prefixWord, tailWord_303651, baseEnd_303651] using wordTrace_append hprefix tailTrace_303651
  have hstable : (prefixWord ++ tailWord_303651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303651).length < 2 ^ (prefixWord ++ tailWord_303651).sum := by decide
  have hdescent : baseEnd_303651 < baseStart_303651 := by decide
  rcases family_descends (prefixWord ++ tailWord_303651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303653 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_303653 : Nat := 118140960795 + 303653 * 2 ^ 59
def prefixEnd_303653 : Nat := 4983230072969 + 3 ^ 40 * 303653 * 2
def baseEnd_303653 : Nat := 155919941179805689941031

theorem tailTrace_303653 : CollatzResearch.WordTrace tailWord_303653 prefixEnd_303653 155919941179805689941031 := by
  unfold tailWord_303653
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075134768924515648739613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7383423179283010432493075 11075134768924515648739613)
  ·
    refine ⟨4153175538346693368277355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11075134768924515648739613 4153175538346693368277355)
    ·
      refine ⟨6229763307520040052416033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4153175538346693368277355 6229763307520040052416033)
      ·
        refine ⟨4672322480640030039312025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6229763307520040052416033 4672322480640030039312025)
        ·
          refine ⟨3504241860480022529484019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4672322480640030039312025 3504241860480022529484019)
          ·
            refine ⟨5256362790720033794226029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504241860480022529484019 5256362790720033794226029)
            ·
              refine ⟨1971136046520012672834761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5256362790720033794226029 1971136046520012672834761)
              ·
                refine ⟨1478352034890009504626071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971136046520012672834761 1478352034890009504626071)
                ·
                  refine ⟨2217528052335014256939107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478352034890009504626071 2217528052335014256939107)
                  ·
                    refine ⟨3326292078502521385408661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217528052335014256939107 3326292078502521385408661)
                    ·
                      refine ⟨155919941179805689941031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3326292078502521385408661 155919941179805689941031)
                      ·
                        rfl

theorem cell23_303653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_303653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303653 prefixEnd_303653 := by exact prefixLift 303653
  have htrace : WordTrace (prefixWord ++ tailWord_303653) baseStart_303653 baseEnd_303653 := by
    simpa [prefixWord, tailWord_303653, baseEnd_303653] using wordTrace_append hprefix tailTrace_303653
  have hstable : (prefixWord ++ tailWord_303653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303653).length < 2 ^ (prefixWord ++ tailWord_303653).sum := by decide
  have hdescent : baseEnd_303653 < baseStart_303653 := by decide
  rcases family_descends (prefixWord ++ tailWord_303653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303677 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_303677 : Nat := 118140960795 + 303677 * 2 ^ 59
def prefixEnd_303677 : Nat := 4983230072969 + 3 ^ 40 * 303677 * 2
def baseEnd_303677 : Nat := 155932264715513596040921

theorem tailTrace_303677 : CollatzResearch.WordTrace tailWord_303677 prefixEnd_303677 155932264715513596040921 := by
  unfold tailWord_303677
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076010120837567747613285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7384006747225045165075523 11076010120837567747613285)
  ·
    refine ⟨2076751897657043952677491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11076010120837567747613285 2076751897657043952677491)
    ·
      refine ⟨3115127846485565929016237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076751897657043952677491 3115127846485565929016237)
      ·
        refine ⟨1168172942432087223381089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3115127846485565929016237 1168172942432087223381089)
        ·
          refine ⟨876129706824065417535817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168172942432087223381089 876129706824065417535817)
          ·
            refine ⟨657097280118049063151863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876129706824065417535817 657097280118049063151863)
            ·
              refine ⟨985645920177073594727795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657097280118049063151863 985645920177073594727795)
              ·
                refine ⟨1478468880265610392091693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985645920177073594727795 1478468880265610392091693)
                ·
                  refine ⟨554425830099603897034385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1478468880265610392091693 554425830099603897034385)
                  ·
                    refine ⟨415819372574702922775789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 554425830099603897034385 415819372574702922775789)
                    ·
                      refine ⟨155932264715513596040921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415819372574702922775789 155932264715513596040921)
                      ·
                        rfl

theorem cell23_303677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_303677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303677 prefixEnd_303677 := by exact prefixLift 303677
  have htrace : WordTrace (prefixWord ++ tailWord_303677) baseStart_303677 baseEnd_303677 := by
    simpa [prefixWord, tailWord_303677, baseEnd_303677] using wordTrace_append hprefix tailTrace_303677
  have hstable : (prefixWord ++ tailWord_303677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303677).length < 2 ^ (prefixWord ++ tailWord_303677).sum := by decide
  have hdescent : baseEnd_303677 < baseStart_303677 := by decide
  rcases family_descends (prefixWord ++ tailWord_303677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303690 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_303690 : Nat := 118140960795 + 303690 * 2 ^ 59
def prefixEnd_303690 : Nat := 4983230072969 + 3 ^ 40 * 303690 * 2
def baseEnd_303690 : Nat := 155938939964022045178361

theorem tailTrace_303690 : CollatzResearch.WordTrace tailWord_303690 prefixEnd_303690 155938939964022045178361 := by
  unfold tailWord_303690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769121067447617741959131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7384322846526980645224349 2769121067447617741959131)
  ·
    refine ⟨4153681601171426612938697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2769121067447617741959131 4153681601171426612938697)
    ·
      refine ⟨3115261200878569959704023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4153681601171426612938697 3115261200878569959704023)
      ·
        refine ⟨4672891801317854939556035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115261200878569959704023 4672891801317854939556035)
        ·
          refine ⟨7009337701976782409334053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672891801317854939556035 7009337701976782409334053)
          ·
            refine ⟨1314250819120646701750135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7009337701976782409334053 1314250819120646701750135)
            ·
              refine ⟨1971376228680970052625203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314250819120646701750135 1971376228680970052625203)
              ·
                refine ⟨2957064343021455078937805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971376228680970052625203 2957064343021455078937805)
                ·
                  refine ⟨1108899128633045654601677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2957064343021455078937805 1108899128633045654601677)
                  ·
                    refine ⟨415837173237392120475629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108899128633045654601677 415837173237392120475629)
                    ·
                      refine ⟨155938939964022045178361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 415837173237392120475629 155938939964022045178361)
                      ·
                        rfl

theorem cell23_303690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_303690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303690 prefixEnd_303690 := by exact prefixLift 303690
  have htrace : WordTrace (prefixWord ++ tailWord_303690) baseStart_303690 baseEnd_303690 := by
    simpa [prefixWord, tailWord_303690, baseEnd_303690] using wordTrace_append hprefix tailTrace_303690
  have hstable : (prefixWord ++ tailWord_303690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303690).length < 2 ^ (prefixWord ++ tailWord_303690).sum := by decide
  have hdescent : baseEnd_303690 < baseStart_303690 := by decide
  rcases family_descends (prefixWord ++ tailWord_303690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303708 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_303708 : Nat := 118140960795 + 303708 * 2 ^ 59
def prefixEnd_303708 : Nat := 4983230072969 + 3 ^ 40 * 303708 * 2
def baseEnd_303708 : Nat := 155948182615802974753279

theorem tailTrace_303708 : CollatzResearch.WordTrace tailWord_303708 prefixEnd_303708 155948182615802974753279 := by
  unfold tailWord_303708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538570391862630020995889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7384760522483506694661185 5538570391862630020995889)
  ·
    refine ⟨4153927793896972515746917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5538570391862630020995889 4153927793896972515746917)
    ·
      refine ⟨778861461355682346702547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4153927793896972515746917 778861461355682346702547)
      ·
        refine ⟨1168292192033523520053821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778861461355682346702547 1168292192033523520053821)
        ·
          refine ⟨438109572012571320020183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1168292192033523520053821 438109572012571320020183)
          ·
            refine ⟨657164358018856980030275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438109572012571320020183 657164358018856980030275)
            ·
              refine ⟨985746537028285470045413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657164358018856980030275 985746537028285470045413)
              ·
                refine ⟨184827475692803525633515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 985746537028285470045413 184827475692803525633515)
                ·
                  refine ⟨277241213539205288450273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184827475692803525633515 277241213539205288450273)
                  ·
                    refine ⟨207930910154403966337705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277241213539205288450273 207930910154403966337705)
                    ·
                      refine ⟨155948182615802974753279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207930910154403966337705 155948182615802974753279)
                      ·
                        rfl

theorem cell23_303708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_303708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303708 prefixEnd_303708 := by exact prefixLift 303708
  have htrace : WordTrace (prefixWord ++ tailWord_303708) baseStart_303708 baseEnd_303708 := by
    simpa [prefixWord, tailWord_303708, baseEnd_303708] using wordTrace_append hprefix tailTrace_303708
  have hstable : (prefixWord ++ tailWord_303708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303708).length < 2 ^ (prefixWord ++ tailWord_303708).sum := by decide
  have hdescent : baseEnd_303708 < baseStart_303708 := by decide
  rcases family_descends (prefixWord ++ tailWord_303708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303714 : List Nat := [3, 3, 2, 3, 1, 2, 1, 8]
def baseStart_303714 : Nat := 118140960795 + 303714 * 2 ^ 59
def prefixEnd_303714 : Nat := 4983230072969 + 3 ^ 40 * 303714 * 2
def baseEnd_303714 : Nat := 5775972722212220417713

theorem tailTrace_303714 : CollatzResearch.WordTrace tailWord_303714 prefixEnd_303714 5775972722212220417713 := by
  unfold tailWord_303714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769339905425880766677549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7384906414469015377806797 2769339905425880766677549)
  ·
    refine ⟨1038502464534705287504081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2769339905425880766677549 1038502464534705287504081)
    ·
      refine ⟨778876848401028965628061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1038502464534705287504081 778876848401028965628061)
      ·
        refine ⟨292078818150385862110523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 778876848401028965628061 292078818150385862110523)
        ·
          refine ⟨438118227225578793165785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292078818150385862110523 438118227225578793165785)
          ·
            refine ⟨328588670419184094874339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438118227225578793165785 328588670419184094874339)
            ·
              refine ⟨492883005628776142311509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328588670419184094874339 492883005628776142311509)
              ·
                refine ⟨5775972722212220417713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 492883005628776142311509 5775972722212220417713)
                ·
                  rfl

theorem cell23_303714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_303714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303714 prefixEnd_303714 := by exact prefixLift 303714
  have htrace : WordTrace (prefixWord ++ tailWord_303714) baseStart_303714 baseEnd_303714 := by
    simpa [prefixWord, tailWord_303714, baseEnd_303714] using wordTrace_append hprefix tailTrace_303714
  have hstable : (prefixWord ++ tailWord_303714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303714).length < 2 ^ (prefixWord ++ tailWord_303714).sum := by decide
  have hdescent : baseEnd_303714 < baseStart_303714 := by decide
  rcases family_descends (prefixWord ++ tailWord_303714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303747 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 1, 4, 2]
def baseStart_303747 : Nat := 118140960795 + 303747 * 2 ^ 59
def prefixEnd_303747 : Nat := 4983230072969 + 3 ^ 40 * 303747 * 2
def baseEnd_303747 : Nat := 155968208361328322165599

theorem tailTrace_303747 : CollatzResearch.WordTrace tailWord_303747 prefixEnd_303747 155968208361328322165599 := by
  unfold tailWord_303747
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078563230583969702661495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7385708820389313135107663 11078563230583969702661495)
  ·
    refine ⟨16617844845875954553992243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11078563230583969702661495 16617844845875954553992243)
    ·
      refine ⟨24926767268813931830988365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16617844845875954553992243 24926767268813931830988365)
      ·
        refine ⟨9347537725805224436620637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24926767268813931830988365 9347537725805224436620637)
        ·
          refine ⟨3505326647176959163732739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9347537725805224436620637 3505326647176959163732739)
          ·
            refine ⟨5257989970765438745599109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505326647176959163732739 5257989970765438745599109)
            ·
              refine ⟨985873119518519764799833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5257989970765438745599109 985873119518519764799833)
              ·
                refine ⟨739404839638889823599875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985873119518519764799833 739404839638889823599875)
                ·
                  refine ⟨1109107259458334735399813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739404839638889823599875 1109107259458334735399813)
                  ·
                    refine ⟨207957611148437762887465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109107259458334735399813 207957611148437762887465)
                    ·
                      refine ⟨155968208361328322165599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 207957611148437762887465 155968208361328322165599)
                      ·
                        rfl

theorem cell23_303747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_303747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303747 prefixEnd_303747 := by exact prefixLift 303747
  have htrace : WordTrace (prefixWord ++ tailWord_303747) baseStart_303747 baseEnd_303747 := by
    simpa [prefixWord, tailWord_303747, baseEnd_303747] using wordTrace_append hprefix tailTrace_303747
  have hstable : (prefixWord ++ tailWord_303747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303747).length < 2 ^ (prefixWord ++ tailWord_303747).sum := by decide
  have hdescent : baseEnd_303747 < baseStart_303747 := by decide
  rcases family_descends (prefixWord ++ tailWord_303747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303753 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 11]
def baseStart_303753 : Nat := 118140960795 + 303753 * 2 ^ 59
def prefixEnd_303753 : Nat := 4983230072969 + 3 ^ 40 * 303753 * 2
def baseEnd_303753 : Nat := 17330143249472810965619

theorem tailTrace_303753 : CollatzResearch.WordTrace tailWord_303753 prefixEnd_303753 17330143249472810965619 := by
  unfold tailWord_303753
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078782068562232727379913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7385854712374821818253275 11078782068562232727379913)
  ·
    refine ⟨8309086551421674545534935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11078782068562232727379913 8309086551421674545534935)
    ·
      refine ⟨12463629827132511818302403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8309086551421674545534935 12463629827132511818302403)
      ·
        refine ⟨18695444740698767727453605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12463629827132511818302403 18695444740698767727453605)
        ·
          refine ⟨3505395888881018948897551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18695444740698767727453605 3505395888881018948897551)
          ·
            refine ⟨5258093833321528423346327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505395888881018948897551 5258093833321528423346327)
            ·
              refine ⟨7887140749982292635019491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5258093833321528423346327 7887140749982292635019491)
              ·
                refine ⟨11830711124973438952529237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7887140749982292635019491 11830711124973438952529237)
                ·
                  refine ⟨17330143249472810965619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 11830711124973438952529237 17330143249472810965619)
                  ·
                    rfl

theorem cell23_303753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_303753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303753 prefixEnd_303753 := by exact prefixLift 303753
  have htrace : WordTrace (prefixWord ++ tailWord_303753) baseStart_303753 baseEnd_303753 := by
    simpa [prefixWord, tailWord_303753, baseEnd_303753] using wordTrace_append hprefix tailTrace_303753
  have hstable : (prefixWord ++ tailWord_303753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303753).length < 2 ^ (prefixWord ++ tailWord_303753).sum := by decide
  have hdescent : baseEnd_303753 < baseStart_303753 := by decide
  rcases family_descends (prefixWord ++ tailWord_303753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303763 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_303763 : Nat := 118140960795 + 303763 * 2 ^ 59
def prefixEnd_303763 : Nat := 4983230072969 + 3 ^ 40 * 303763 * 2
def baseEnd_303763 : Nat := 155976424051800259565525

theorem tailTrace_303763 : CollatzResearch.WordTrace tailWord_303763 prefixEnd_303763 155976424051800259565525 := by
  unfold tailWord_303763
  simp only [CollatzResearch.WordTrace]
  refine ⟨11079146798526004435243943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7386097865684002956829295 11079146798526004435243943)
  ·
    refine ⟨16618720197789006652865915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11079146798526004435243943 16618720197789006652865915)
    ·
      refine ⟨24928080296683509979298873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16618720197789006652865915 24928080296683509979298873)
      ·
        refine ⟨18696060222512632484474155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24928080296683509979298873 18696060222512632484474155)
        ·
          refine ⟨28044090333768948726711233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18696060222512632484474155 28044090333768948726711233)
          ·
            refine ⟨21033067750326711545033425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28044090333768948726711233 21033067750326711545033425)
            ·
              refine ⟨15774800812745033658775069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21033067750326711545033425 15774800812745033658775069)
              ·
                refine ⟨5915550304779387622040651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15774800812745033658775069 5915550304779387622040651)
                ·
                  refine ⟨8873325457169081433060977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915550304779387622040651 8873325457169081433060977)
                  ·
                    refine ⟨6654994092876811074795733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8873325457169081433060977 6654994092876811074795733)
                    ·
                      refine ⟨155976424051800259565525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6654994092876811074795733 155976424051800259565525)
                      ·
                        rfl

theorem cell23_303763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_303763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303763 prefixEnd_303763 := by exact prefixLift 303763
  have htrace : WordTrace (prefixWord ++ tailWord_303763) baseStart_303763 baseEnd_303763 := by
    simpa [prefixWord, tailWord_303763, baseEnd_303763] using wordTrace_append hprefix tailTrace_303763
  have hstable : (prefixWord ++ tailWord_303763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303763).length < 2 ^ (prefixWord ++ tailWord_303763).sum := by decide
  have hdescent : baseEnd_303763 < baseStart_303763 := by decide
  rcases family_descends (prefixWord ++ tailWord_303763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303821 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 7]
def baseStart_303821 : Nat := 118140960795 + 303821 * 2 ^ 59
def prefixEnd_303821 : Nat := 4983230072969 + 3 ^ 40 * 303821 * 2
def baseEnd_303821 : Nat := 17334022881084559182251

theorem tailTrace_303821 : CollatzResearch.WordTrace tailWord_303821 prefixEnd_303821 17334022881084559182251 := by
  unfold tailWord_303821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081262232315880340855317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7387508154877253560570211 11081262232315880340855317)
  ·
    refine ⟨519434167139806890977593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11081262232315880340855317 519434167139806890977593)
    ·
      refine ⟨389575625354855168233195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 519434167139806890977593 389575625354855168233195)
      ·
        refine ⟨584363438032282752349793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389575625354855168233195 584363438032282752349793)
        ·
          refine ⟨438272578524212064262345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584363438032282752349793 438272578524212064262345)
          ·
            refine ⟨328704433893159048196759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438272578524212064262345 328704433893159048196759)
            ·
              refine ⟨493056650839738572295139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328704433893159048196759 493056650839738572295139)
              ·
                refine ⟨739584976259607858442709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493056650839738572295139 739584976259607858442709)
                ·
                  refine ⟨17334022881084559182251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 739584976259607858442709 17334022881084559182251)
                  ·
                    rfl

theorem cell23_303821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_303821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303821 prefixEnd_303821 := by exact prefixLift 303821
  have htrace : WordTrace (prefixWord ++ tailWord_303821) baseStart_303821 baseEnd_303821 := by
    simpa [prefixWord, tailWord_303821, baseEnd_303821] using wordTrace_append hprefix tailTrace_303821
  have hstable : (prefixWord ++ tailWord_303821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303821).length < 2 ^ (prefixWord ++ tailWord_303821).sum := by decide
  have hdescent : baseEnd_303821 < baseStart_303821 := by decide
  rcases family_descends (prefixWord ++ tailWord_303821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303850 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_303850 : Nat := 118140960795 + 303850 * 2 ^ 59
def prefixEnd_303850 : Nat := 4983230072969 + 3 ^ 40 * 303850 * 2
def baseEnd_303850 : Nat := 156021096868741419177625

theorem tailTrace_303850 : CollatzResearch.WordTrace tailWord_303850 prefixEnd_303850 156021096868741419177625 := by
  unfold tailWord_303850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770579987302704573415251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7388213299473878862440669 2770579987302704573415251)
  ·
    refine ⟨4155869980954056860122877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770579987302704573415251 4155869980954056860122877)
    ·
      refine ⟨1558451242857771322546079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4155869980954056860122877 1558451242857771322546079)
      ·
        refine ⟨2337676864286656983819119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558451242857771322546079 2337676864286656983819119)
        ·
          refine ⟨3506515296429985475728679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337676864286656983819119 3506515296429985475728679)
          ·
            refine ⟨5259772944644978213593019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506515296429985475728679 5259772944644978213593019)
            ·
              refine ⟨7889659416967467320389529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259772944644978213593019 7889659416967467320389529)
              ·
                refine ⟨5917244562725600490292147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7889659416967467320389529 5917244562725600490292147)
                ·
                  refine ⟨8875866844088400735438221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5917244562725600490292147 8875866844088400735438221)
                  ·
                    refine ⟨3328450066533150275789333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8875866844088400735438221 3328450066533150275789333)
                    ·
                      refine ⟨156021096868741419177625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3328450066533150275789333 156021096868741419177625)
                      ·
                        rfl

theorem cell23_303850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_303850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303850 prefixEnd_303850 := by exact prefixLift 303850
  have htrace : WordTrace (prefixWord ++ tailWord_303850) baseStart_303850 baseEnd_303850 := by
    simpa [prefixWord, tailWord_303850, baseEnd_303850] using wordTrace_append hprefix tailTrace_303850
  have hstable : (prefixWord ++ tailWord_303850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303850).length < 2 ^ (prefixWord ++ tailWord_303850).sum := by decide
  have hdescent : baseEnd_303850 < baseStart_303850 := by decide
  rcases family_descends (prefixWord ++ tailWord_303850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303854 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_303854 : Nat := 118140960795 + 303854 * 2 ^ 59
def prefixEnd_303854 : Nat := 4983230072969 + 3 ^ 40 * 303854 * 2
def baseEnd_303854 : Nat := 156023150791359403527607

theorem tailTrace_303854 : CollatzResearch.WordTrace tailWord_303854 prefixEnd_303854 156023150791359403527607 := by
  unfold tailWord_303854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385308230149540872100827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7388310560797551317871077 1385308230149540872100827)
  ·
    refine ⟨2077962345224311308151241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385308230149540872100827 2077962345224311308151241)
    ·
      refine ⟨1558471758918233481113431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2077962345224311308151241 1558471758918233481113431)
      ·
        refine ⟨2337707638377350221670147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558471758918233481113431 2337707638377350221670147)
        ·
          refine ⟨3506561457566025332505221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337707638377350221670147 3506561457566025332505221)
          ·
            refine ⟨657480273293629749844729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3506561457566025332505221 657480273293629749844729)
            ·
              refine ⟨493110204970222312383547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657480273293629749844729 493110204970222312383547)
              ·
                refine ⟨739665307455333468575321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493110204970222312383547 739665307455333468575321)
                ·
                  refine ⟨554748980591500101431491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 739665307455333468575321 554748980591500101431491)
                  ·
                    refine ⟨832123470887250152147237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 554748980591500101431491 832123470887250152147237)
                    ·
                      refine ⟨156023150791359403527607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 832123470887250152147237 156023150791359403527607)
                      ·
                        rfl

theorem cell23_303854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_303854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303854 prefixEnd_303854 := by exact prefixLift 303854
  have htrace : WordTrace (prefixWord ++ tailWord_303854) baseStart_303854 baseEnd_303854 := by
    simpa [prefixWord, tailWord_303854, baseEnd_303854] using wordTrace_append hprefix tailTrace_303854
  have hstable : (prefixWord ++ tailWord_303854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303854).length < 2 ^ (prefixWord ++ tailWord_303854).sum := by decide
  have hdescent : baseEnd_303854 < baseStart_303854 := by decide
  rcases family_descends (prefixWord ++ tailWord_303854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303864 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 1, 4]
def baseStart_303864 : Nat := 118140960795 + 303864 * 2 ^ 59
def prefixEnd_303864 : Nat := 4983230072969 + 3 ^ 40 * 303864 * 2
def baseEnd_303864 : Nat := 52009428532634788134187

theorem tailTrace_303864 : CollatzResearch.WordTrace tailWord_303864 prefixEnd_303864 52009428532634788134187 := by
  unfold tailWord_303864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541415285580049342335323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7388553714106732456447097 5541415285580049342335323)
  ·
    refine ⟨8312122928370074013502985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5541415285580049342335323 8312122928370074013502985)
    ·
      refine ⟨6234092196277555510127239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8312122928370074013502985 6234092196277555510127239)
      ·
        refine ⟨9351138294416333265190859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6234092196277555510127239 9351138294416333265190859)
        ·
          refine ⟨14026707441624499897786289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9351138294416333265190859 14026707441624499897786289)
          ·
            refine ⟨10520030581218374923339717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14026707441624499897786289 10520030581218374923339717)
            ·
              refine ⟨1972505733978445298126197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10520030581218374923339717 1972505733978445298126197)
              ·
                refine ⟨184922412560479246699331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1972505733978445298126197 184922412560479246699331)
                ·
                  refine ⟨277383618840718870048997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184922412560479246699331 277383618840718870048997)
                  ·
                    refine ⟨52009428532634788134187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277383618840718870048997 52009428532634788134187)
                    ·
                      rfl

theorem cell23_303864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_303864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303864 prefixEnd_303864 := by exact prefixLift 303864
  have htrace : WordTrace (prefixWord ++ tailWord_303864) baseStart_303864 baseEnd_303864 := by
    simpa [prefixWord, tailWord_303864, baseEnd_303864] using wordTrace_append hprefix tailTrace_303864
  have hstable : (prefixWord ++ tailWord_303864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303864).length < 2 ^ (prefixWord ++ tailWord_303864).sum := by decide
  have hdescent : baseEnd_303864 < baseStart_303864 := by decide
  rcases family_descends (prefixWord ++ tailWord_303864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303881 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 1, 4]
def baseStart_303881 : Nat := 118140960795 + 303881 * 2 ^ 59
def prefixEnd_303881 : Nat := 4983230072969 + 3 ^ 40 * 303881 * 2
def baseEnd_303881 : Nat := 52012338256343599296661

theorem tailTrace_303881 : CollatzResearch.WordTrace tailWord_303881 prefixEnd_303881 52012338256343599296661 := by
  unfold tailWord_303881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11083450612098510588039497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7388967074732340392026331 11083450612098510588039497)
  ·
    refine ⟨8312587959073882941029623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11083450612098510588039497 8312587959073882941029623)
    ·
      refine ⟨12468881938610824411544435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312587959073882941029623 12468881938610824411544435)
      ·
        refine ⟨18703322907916236617316653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12468881938610824411544435 18703322907916236617316653)
        ·
          refine ⟨7013746090468588731493745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18703322907916236617316653 7013746090468588731493745)
          ·
            refine ⟨5260309567851441548620309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7013746090468588731493745 5260309567851441548620309)
            ·
              refine ⟨246577010993036322591577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5260309567851441548620309 246577010993036322591577)
              ·
                refine ⟨184932758244777241943683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246577010993036322591577 184932758244777241943683)
                ·
                  refine ⟨277399137367165862915525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184932758244777241943683 277399137367165862915525)
                  ·
                    refine ⟨52012338256343599296661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277399137367165862915525 52012338256343599296661)
                    ·
                      rfl

theorem cell23_303881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 4].length) (baseStart_303881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303881 prefixEnd_303881 := by exact prefixLift 303881
  have htrace : WordTrace (prefixWord ++ tailWord_303881) baseStart_303881 baseEnd_303881 := by
    simpa [prefixWord, tailWord_303881, baseEnd_303881] using wordTrace_append hprefix tailTrace_303881
  have hstable : (prefixWord ++ tailWord_303881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303881).length < 2 ^ (prefixWord ++ tailWord_303881).sum := by decide
  have hdescent : baseEnd_303881 < baseStart_303881 := by decide
  rcases family_descends (prefixWord ++ tailWord_303881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303904 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 5, 1, 3]
def baseStart_303904 : Nat := 118140960795 + 303904 * 2 ^ 59
def prefixEnd_303904 : Nat := 4983230072969 + 3 ^ 40 * 303904 * 2
def baseEnd_303904 : Nat := 156048824824084207902377

theorem tailTrace_303904 : CollatzResearch.WordTrace tailWord_303904 prefixEnd_303904 156048824824084207902377 := by
  unfold tailWord_303904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542144745507592758063383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7389526327343457010751177 5542144745507592758063383)
  ·
    refine ⟨8313217118261389137095075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5542144745507592758063383 8313217118261389137095075)
    ·
      refine ⟨12469825677392083705642613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8313217118261389137095075 12469825677392083705642613)
      ·
        refine ⟨1169046157255507847403995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12469825677392083705642613 1169046157255507847403995)
        ·
          refine ⟨1753569235883261771105993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169046157255507847403995 1753569235883261771105993)
          ·
            refine ⟨1315176926912446328329495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753569235883261771105993 1315176926912446328329495)
            ·
              refine ⟨1972765390368669492494243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315176926912446328329495 1972765390368669492494243)
              ·
                refine ⟨2959148085553004238741365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972765390368669492494243 2959148085553004238741365)
                ·
                  refine ⟨277420133020594147382003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959148085553004238741365 277420133020594147382003)
                  ·
                    refine ⟨416130199530891221073005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277420133020594147382003 416130199530891221073005)
                    ·
                      refine ⟨156048824824084207902377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 416130199530891221073005 156048824824084207902377)
                      ·
                        rfl

theorem cell23_303904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_303904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303904 prefixEnd_303904 := by exact prefixLift 303904
  have htrace : WordTrace (prefixWord ++ tailWord_303904) baseStart_303904 baseEnd_303904 := by
    simpa [prefixWord, tailWord_303904, baseEnd_303904] using wordTrace_append hprefix tailTrace_303904
  have hstable : (prefixWord ++ tailWord_303904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303904).length < 2 ^ (prefixWord ++ tailWord_303904).sum := by decide
  have hdescent : baseEnd_303904 < baseStart_303904 := by decide
  rcases family_descends (prefixWord ++ tailWord_303904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303907 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 1, 5]
def baseStart_303907 : Nat := 118140960795 + 303907 * 2 ^ 59
def prefixEnd_303907 : Nat := 4983230072969 + 3 ^ 40 * 303907 * 2
def baseEnd_303907 : Nat := 52016788422015898721621

theorem tailTrace_303907 : CollatzResearch.WordTrace tailWord_303907 prefixEnd_303907 52016788422015898721621 := by
  unfold tailWord_303907
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084398910004317028485975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7389599273336211352323983 11084398910004317028485975)
  ·
    refine ⟨16626598365006475542728963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11084398910004317028485975 16626598365006475542728963)
    ·
      refine ⟨24939897547509713314093445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16626598365006475542728963 24939897547509713314093445)
      ·
        refine ⟨4676230790158071246392521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24939897547509713314093445 4676230790158071246392521)
        ·
          refine ⟨3507173092618553434794391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4676230790158071246392521 3507173092618553434794391)
          ·
            refine ⟨5260759638927830152191587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507173092618553434794391 5260759638927830152191587)
            ·
              refine ⟨7891139458391745228287381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5260759638927830152191587 7891139458391745228287381)
              ·
                refine ⟨369897162112113057575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7891139458391745228287381 369897162112113057575971)
                ·
                  refine ⟨554845743168169586363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369897162112113057575971 554845743168169586363957)
                  ·
                    refine ⟨52016788422015898721621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 554845743168169586363957 52016788422015898721621)
                    ·
                      rfl

theorem cell23_303907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 5].length) (baseStart_303907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303907 prefixEnd_303907 := by exact prefixLift 303907
  have htrace : WordTrace (prefixWord ++ tailWord_303907) baseStart_303907 baseEnd_303907 := by
    simpa [prefixWord, tailWord_303907, baseEnd_303907] using wordTrace_append hprefix tailTrace_303907
  have hstable : (prefixWord ++ tailWord_303907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303907).length < 2 ^ (prefixWord ++ tailWord_303907).sum := by decide
  have hdescent : baseEnd_303907 < baseStart_303907 := by decide
  rcases family_descends (prefixWord ++ tailWord_303907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303908 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_303908 : Nat := 118140960795 + 303908 * 2 ^ 59
def prefixEnd_303908 : Nat := 4983230072969 + 3 ^ 40 * 303908 * 2
def baseEnd_303908 : Nat := 156050878746702192252359

theorem tailTrace_303908 : CollatzResearch.WordTrace tailWord_303908 prefixEnd_303908 156050878746702192252359 := by
  unfold tailWord_303908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542217691500347099636189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7389623588667129466181585 5542217691500347099636189)
  ·
    refine ⟨2078331634312630162363571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5542217691500347099636189 2078331634312630162363571)
    ·
      refine ⟨3117497451468945243545357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2078331634312630162363571 3117497451468945243545357)
      ·
        refine ⟨1169061544300854466329509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3117497451468945243545357 1169061544300854466329509)
        ·
          refine ⟨219199039556410212436783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1169061544300854466329509 219199039556410212436783)
          ·
            refine ⟨328798559334615318655175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219199039556410212436783 328798559334615318655175)
            ·
              refine ⟨493197839001922977982763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328798559334615318655175 493197839001922977982763)
              ·
                refine ⟨739796758502884466974145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493197839001922977982763 739796758502884466974145)
                ·
                  refine ⟨554847568877163350230609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 739796758502884466974145 554847568877163350230609)
                  ·
                    refine ⟨416135676657872512672957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 554847568877163350230609 416135676657872512672957)
                    ·
                      refine ⟨156050878746702192252359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 416135676657872512672957 156050878746702192252359)
                      ·
                        rfl

theorem cell23_303908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_303908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303908 prefixEnd_303908 := by exact prefixLift 303908
  have htrace : WordTrace (prefixWord ++ tailWord_303908) baseStart_303908 baseEnd_303908 := by
    simpa [prefixWord, tailWord_303908, baseEnd_303908] using wordTrace_append hprefix tailTrace_303908
  have hstable : (prefixWord ++ tailWord_303908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303908).length < 2 ^ (prefixWord ++ tailWord_303908).sum := by decide
  have hdescent : baseEnd_303908 < baseStart_303908 := by decide
  rcases family_descends (prefixWord ++ tailWord_303908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303957 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_303957 : Nat := 118140960795 + 303957 * 2 ^ 59
def prefixEnd_303957 : Nat := 4983230072969 + 3 ^ 40 * 303957 * 2
def baseEnd_303957 : Nat := 156076039298772500539633

theorem tailTrace_303957 : CollatzResearch.WordTrace tailWord_303957 prefixEnd_303957 156076039298772500539633 := by
  unfold tailWord_303957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11086222559823175567806125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7390815039882117045204083 11086222559823175567806125)
  ·
    refine ⟨4157333459933690837927297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11086222559823175567806125 4157333459933690837927297)
    ·
      refine ⟨3118000094950268128445473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4157333459933690837927297 3118000094950268128445473)
      ·
        refine ⟨2338500071212701096334105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3118000094950268128445473 2338500071212701096334105)
        ·
          refine ⟨1753875053409525822250579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338500071212701096334105 1753875053409525822250579)
          ·
            refine ⟨2630812580114288733375869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753875053409525822250579 2630812580114288733375869)
            ·
              refine ⟨986554717542858275015951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2630812580114288733375869 986554717542858275015951)
              ·
                refine ⟨1479832076314287412523927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986554717542858275015951 1479832076314287412523927)
                ·
                  refine ⟨2219748114471431118785891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479832076314287412523927 2219748114471431118785891)
                  ·
                    refine ⟨3329622171707146678178837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2219748114471431118785891 3329622171707146678178837)
                    ·
                      refine ⟨156076039298772500539633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3329622171707146678178837 156076039298772500539633)
                      ·
                        rfl

theorem cell23_303957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_303957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303957 prefixEnd_303957 := by exact prefixLift 303957
  have htrace : WordTrace (prefixWord ++ tailWord_303957) baseStart_303957 baseEnd_303957 := by
    simpa [prefixWord, tailWord_303957, baseEnd_303957] using wordTrace_append hprefix tailTrace_303957
  have hstable : (prefixWord ++ tailWord_303957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303957).length < 2 ^ (prefixWord ++ tailWord_303957).sum := by decide
  have hdescent : baseEnd_303957 < baseStart_303957 := by decide
  rcases family_descends (prefixWord ++ tailWord_303957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303961 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 3, 2, 2]
def baseStart_303961 : Nat := 118140960795 + 303961 * 2 ^ 59
def prefixEnd_303961 : Nat := 4983230072969 + 3 ^ 40 * 303961 * 2
def baseEnd_303961 : Nat := 156078093221390484889615

theorem tailTrace_303961 : CollatzResearch.WordTrace tailWord_303961 prefixEnd_303961 156078093221390484889615 := by
  unfold tailWord_303961
  simp only [CollatzResearch.WordTrace]
  refine ⟨11086368451808684250951737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7390912301205789500634491 11086368451808684250951737)
  ·
    refine ⟨8314776338856513188213803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11086368451808684250951737 8314776338856513188213803)
    ·
      refine ⟨12472164508284769782320705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8314776338856513188213803 12472164508284769782320705)
      ·
        refine ⟨9354123381213577336740529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12472164508284769782320705 9354123381213577336740529)
        ·
          refine ⟨7015592535910183002555397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9354123381213577336740529 7015592535910183002555397)
          ·
            refine ⟨1315423600483159312979137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7015592535910183002555397 1315423600483159312979137)
            ·
              refine ⟨986567700362369484734353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315423600483159312979137 986567700362369484734353)
              ·
                refine ⟨739925775271777113550765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986567700362369484734353 739925775271777113550765)
                ·
                  refine ⟨277472165726916417581537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739925775271777113550765 277472165726916417581537)
                  ·
                    refine ⟨208104124295187313186153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277472165726916417581537 208104124295187313186153)
                    ·
                      refine ⟨156078093221390484889615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208104124295187313186153 156078093221390484889615)
                      ·
                        rfl

theorem cell23_303961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_303961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_303961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_303961 prefixEnd_303961 := by exact prefixLift 303961
  have htrace : WordTrace (prefixWord ++ tailWord_303961) baseStart_303961 baseEnd_303961 := by
    simpa [prefixWord, tailWord_303961, baseEnd_303961] using wordTrace_append hprefix tailTrace_303961
  have hstable : (prefixWord ++ tailWord_303961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303961).length < 2 ^ (prefixWord ++ tailWord_303961).sum := by decide
  have hdescent : baseEnd_303961 < baseStart_303961 := by decide
  rcases family_descends (prefixWord ++ tailWord_303961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304004 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_304004 : Nat := 118140960795 + 304004 * 2 ^ 59
def prefixEnd_304004 : Nat := 4983230072969 + 3 ^ 40 * 304004 * 2
def baseEnd_304004 : Nat := 156100172889533816651917

theorem tailTrace_304004 : CollatzResearch.WordTrace tailWord_304004 prefixEnd_304004 156100172889533816651917 := by
  unfold tailWord_304004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543968395326451297383533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7391957860435268396511377 5543968395326451297383533)
  ·
    refine ⟨2078988148247419236518825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5543968395326451297383533 2078988148247419236518825)
    ·
      refine ⟨1559241111185564427389119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2078988148247419236518825 1559241111185564427389119)
      ·
        refine ⟨2338861666778346641083679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559241111185564427389119 2338861666778346641083679)
        ·
          refine ⟨3508292500167519961625519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338861666778346641083679 3508292500167519961625519)
          ·
            refine ⟨5262438750251279942438279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508292500167519961625519 5262438750251279942438279)
            ·
              refine ⟨7893658125376919913657419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262438750251279942438279 7893658125376919913657419)
              ·
                refine ⟨11840487188065379870486129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893658125376919913657419 11840487188065379870486129)
                ·
                  refine ⟨8880365391049034902864597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11840487188065379870486129 8880365391049034902864597)
                  ·
                    refine ⟨208133563852711755535889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8880365391049034902864597 208133563852711755535889)
                    ·
                      refine ⟨156100172889533816651917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208133563852711755535889 156100172889533816651917)
                      ·
                        rfl

theorem cell23_304004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_304004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304004 prefixEnd_304004 := by exact prefixLift 304004
  have htrace : WordTrace (prefixWord ++ tailWord_304004) baseStart_304004 baseEnd_304004 := by
    simpa [prefixWord, tailWord_304004, baseEnd_304004] using wordTrace_append hprefix tailTrace_304004
  have hstable : (prefixWord ++ tailWord_304004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304004).length < 2 ^ (prefixWord ++ tailWord_304004).sum := by decide
  have hdescent : baseEnd_304004 < baseStart_304004 := by decide
  rcases family_descends (prefixWord ++ tailWord_304004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304021 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_304021 : Nat := 118140960795 + 304021 * 2 ^ 59
def prefixEnd_304021 : Nat := 4983230072969 + 3 ^ 40 * 304021 * 2
def baseEnd_304021 : Nat := 156108902060660250139339

theorem tailTrace_304021 : CollatzResearch.WordTrace tailWord_304021 prefixEnd_304021 156108902060660250139339 := by
  unfold tailWord_304021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088556831591314498135917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7392371221060876332090611 11088556831591314498135917)
  ·
    refine ⟨4158208811846742936800969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11088556831591314498135917 4158208811846742936800969)
    ·
      refine ⟨3118656608885057202600727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4158208811846742936800969 3118656608885057202600727)
      ·
        refine ⟨4677984913327585803901091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3118656608885057202600727 4677984913327585803901091)
        ·
          refine ⟨7016977369991378705851637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677984913327585803901091 7016977369991378705851637)
          ·
            refine ⟨657841628436691753673591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7016977369991378705851637 657841628436691753673591)
            ·
              refine ⟨986762442655037630510387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657841628436691753673591 986762442655037630510387)
              ·
                refine ⟨1480143663982556445765581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986762442655037630510387 1480143663982556445765581)
                ·
                  refine ⟨555053873993458667162093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1480143663982556445765581 555053873993458667162093)
                  ·
                    refine ⟨208145202747547000185785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555053873993458667162093 208145202747547000185785)
                    ·
                      refine ⟨156108902060660250139339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208145202747547000185785 156108902060660250139339)
                      ·
                        rfl

theorem cell23_304021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_304021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304021 prefixEnd_304021 := by exact prefixLift 304021
  have htrace : WordTrace (prefixWord ++ tailWord_304021) baseStart_304021 baseEnd_304021 := by
    simpa [prefixWord, tailWord_304021, baseEnd_304021] using wordTrace_append hprefix tailTrace_304021
  have hstable : (prefixWord ++ tailWord_304021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304021).length < 2 ^ (prefixWord ++ tailWord_304021).sum := by decide
  have hdescent : baseEnd_304021 < baseStart_304021 := by decide
  rcases family_descends (prefixWord ++ tailWord_304021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304064 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_304064 : Nat := 118140960795 + 304064 * 2 ^ 59
def prefixEnd_304064 : Nat := 4983230072969 + 3 ^ 40 * 304064 * 2
def baseEnd_304064 : Nat := 156130981728803581901641

theorem tailTrace_304064 : CollatzResearch.WordTrace tailWord_304064 prefixEnd_304064 156130981728803581901641 := by
  unfold tailWord_304064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5545062585217766420975623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7393416780290355227967497 5545062585217766420975623)
  ·
    refine ⟨8317593877826649631463435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5545062585217766420975623 8317593877826649631463435)
    ·
      refine ⟨12476390816739974447195153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8317593877826649631463435 12476390816739974447195153)
      ·
        refine ⟨9357293112554980835396365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12476390816739974447195153 9357293112554980835396365)
        ·
          refine ⟨3508984917208117813273637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9357293112554980835396365 3508984917208117813273637)
          ·
            refine ⟨657934671976522089988807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3508984917208117813273637 657934671976522089988807)
            ·
              refine ⟨986902007964783134983211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657934671976522089988807 986902007964783134983211)
              ·
                refine ⟨1480353011947174702474817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986902007964783134983211 1480353011947174702474817)
                ·
                  refine ⟨1110264758960381026856113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1480353011947174702474817 1110264758960381026856113)
                  ·
                    refine ⟨832698569220285770142085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1110264758960381026856113 832698569220285770142085)
                    ·
                      refine ⟨156130981728803581901641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 832698569220285770142085 156130981728803581901641)
                      ·
                        rfl

theorem cell23_304064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_304064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304064 prefixEnd_304064 := by exact prefixLift 304064
  have htrace : WordTrace (prefixWord ++ tailWord_304064) baseStart_304064 baseEnd_304064 := by
    simpa [prefixWord, tailWord_304064, baseEnd_304064] using wordTrace_append hprefix tailTrace_304064
  have hstable : (prefixWord ++ tailWord_304064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304064).length < 2 ^ (prefixWord ++ tailWord_304064).sum := by decide
  have hdescent : baseEnd_304064 < baseStart_304064 := by decide
  rcases family_descends (prefixWord ++ tailWord_304064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304104 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_304104 : Nat := 118140960795 + 304104 * 2 ^ 59
def prefixEnd_304104 : Nat := 4983230072969 + 3 ^ 40 * 304104 * 2
def baseEnd_304104 : Nat := 52050506984994475133819

theorem tailTrace_304104 : CollatzResearch.WordTrace tailWord_304104 prefixEnd_304104 52050506984994475133819 := by
  unfold tailWord_304104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5545792045145309836703683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7394389393527079782271577 5545792045145309836703683)
  ·
    refine ⟨8318688067717964755055525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5545792045145309836703683 8318688067717964755055525)
    ·
      refine ⟨1559754012697118391572911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8318688067717964755055525 1559754012697118391572911)
      ·
        refine ⟨2339631019045677587359367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559754012697118391572911 2339631019045677587359367)
        ·
          refine ⟨3509446528568516381039051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339631019045677587359367 3509446528568516381039051)
          ·
            refine ⟨5264169792852774571558577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509446528568516381039051 5264169792852774571558577)
            ·
              refine ⟨3948127344639580928668933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5264169792852774571558577 3948127344639580928668933)
              ·
                refine ⟨740273877119921424125425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3948127344639580928668933 740273877119921424125425)
                ·
                  refine ⟨555205407839941068094069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 740273877119921424125425 555205407839941068094069)
                  ·
                    refine ⟨52050506984994475133819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 555205407839941068094069 52050506984994475133819)
                    ·
                      rfl

theorem cell23_304104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_304104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304104 prefixEnd_304104 := by exact prefixLift 304104
  have htrace : WordTrace (prefixWord ++ tailWord_304104) baseStart_304104 baseEnd_304104 := by
    simpa [prefixWord, tailWord_304104, baseEnd_304104] using wordTrace_append hprefix tailTrace_304104
  have hstable : (prefixWord ++ tailWord_304104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304104).length < 2 ^ (prefixWord ++ tailWord_304104).sum := by decide
  have hdescent : baseEnd_304104 < baseStart_304104 := by decide
  rcases family_descends (prefixWord ++ tailWord_304104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304124 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_304124 : Nat := 118140960795 + 304124 * 2 ^ 59
def prefixEnd_304124 : Nat := 4983230072969 + 3 ^ 40 * 304124 * 2
def baseEnd_304124 : Nat := 156161790568073347151365

theorem tailTrace_304124 : CollatzResearch.WordTrace tailWord_304124 prefixEnd_304124 156161790568073347151365 := by
  unfold tailWord_304124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5546156775109081544567713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7394875700145442059423617 5546156775109081544567713)
  ·
    refine ⟨4159617581331811158425785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5546156775109081544567713 4159617581331811158425785)
    ·
      refine ⟨3119713185998858368819339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4159617581331811158425785 3119713185998858368819339)
      ·
        refine ⟨4679569778998287553229009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119713185998858368819339 4679569778998287553229009)
        ·
          refine ⟨3509677334248715664921757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4679569778998287553229009 3509677334248715664921757)
          ·
            refine ⟨1316129000343268374345659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3509677334248715664921757 1316129000343268374345659)
            ·
              refine ⟨1974193500514902561518489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316129000343268374345659 1974193500514902561518489)
              ·
                refine ⟨1480645125386176921138867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974193500514902561518489 1480645125386176921138867)
                ·
                  refine ⟨2220967688079265381708301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480645125386176921138867 2220967688079265381708301)
                  ·
                    refine ⟨832862883029724518140613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2220967688079265381708301 832862883029724518140613)
                    ·
                      refine ⟨156161790568073347151365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 832862883029724518140613 156161790568073347151365)
                      ·
                        rfl

theorem cell23_304124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_304124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304124 prefixEnd_304124 := by exact prefixLift 304124
  have htrace : WordTrace (prefixWord ++ tailWord_304124) baseStart_304124 baseEnd_304124 := by
    simpa [prefixWord, tailWord_304124, baseEnd_304124] using wordTrace_append hprefix tailTrace_304124
  have hstable : (prefixWord ++ tailWord_304124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304124).length < 2 ^ (prefixWord ++ tailWord_304124).sum := by decide
  have hdescent : baseEnd_304124 < baseStart_304124 := by decide
  rcases family_descends (prefixWord ++ tailWord_304124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304161 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_304161 : Nat := 118140960795 + 304161 * 2 ^ 59
def prefixEnd_304161 : Nat := 4983230072969 + 3 ^ 40 * 304161 * 2
def baseEnd_304161 : Nat := 156180789352289702388695

theorem tailTrace_304161 : CollatzResearch.WordTrace tailWord_304161 prefixEnd_304161 156180789352289702388695 := by
  unfold tailWord_304161
  simp only [CollatzResearch.WordTrace]
  refine ⟨11093663051084118408232337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7395775367389412272154891 11093663051084118408232337)
  ·
    refine ⟨8320247288313088806174253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11093663051084118408232337 8320247288313088806174253)
    ·
      refine ⟨3120092733117408302315345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8320247288313088806174253 3120092733117408302315345)
      ·
        refine ⟨2340069549838056226736509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3120092733117408302315345 2340069549838056226736509)
        ·
          refine ⟨877526081189271085026191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2340069549838056226736509 877526081189271085026191)
          ·
            refine ⟨1316289121783906627539287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877526081189271085026191 1316289121783906627539287)
            ·
              refine ⟨1974433682675859941308931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316289121783906627539287 1974433682675859941308931)
              ·
                refine ⟨2961650524013789911963397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974433682675859941308931 2961650524013789911963397)
                ·
                  refine ⟨555309473252585608493137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2961650524013789911963397 555309473252585608493137)
                  ·
                    refine ⟨416482104939439206369853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 555309473252585608493137 416482104939439206369853)
                    ·
                      refine ⟨156180789352289702388695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 416482104939439206369853 156180789352289702388695)
                      ·
                        rfl

theorem cell23_304161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_304161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304161 prefixEnd_304161 := by exact prefixLift 304161
  have htrace : WordTrace (prefixWord ++ tailWord_304161) baseStart_304161 baseEnd_304161 := by
    simpa [prefixWord, tailWord_304161, baseEnd_304161] using wordTrace_append hprefix tailTrace_304161
  have hstable : (prefixWord ++ tailWord_304161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304161).length < 2 ^ (prefixWord ++ tailWord_304161).sum := by decide
  have hdescent : baseEnd_304161 < baseStart_304161 := by decide
  rcases family_descends (prefixWord ++ tailWord_304161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304191 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 3]
def baseStart_304191 : Nat := 118140960795 + 304191 * 2 ^ 59
def prefixEnd_304191 : Nat := 4983230072969 + 3 ^ 40 * 304191 * 2
def baseEnd_304191 : Nat := 156196193771924585013557

theorem tailTrace_304191 : CollatzResearch.WordTrace tailWord_304191 prefixEnd_304191 156196193771924585013557 := by
  unfold tailWord_304191
  simp only [CollatzResearch.WordTrace]
  refine ⟨11094757240975433531824427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7396504827316955687882951 11094757240975433531824427)
  ·
    refine ⟨16642135861463150297736641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11094757240975433531824427 16642135861463150297736641)
    ·
      refine ⟨12481601896097362723302481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16642135861463150297736641 12481601896097362723302481)
      ·
        refine ⟨9361201422073022042476861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12481601896097362723302481 9361201422073022042476861)
        ·
          refine ⟨3510450533277383265928823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9361201422073022042476861 3510450533277383265928823)
          ·
            refine ⟨5265675799916074898893235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510450533277383265928823 5265675799916074898893235)
            ·
              refine ⟨7898513699874112348339853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265675799916074898893235 7898513699874112348339853)
              ·
                refine ⟨2961942637452792130627445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7898513699874112348339853 2961942637452792130627445)
                ·
                  refine ⟨277682122261199262246323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2961942637452792130627445 277682122261199262246323)
                  ·
                    refine ⟨416523183391798893369485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277682122261199262246323 416523183391798893369485)
                    ·
                      refine ⟨156196193771924585013557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 416523183391798893369485 156196193771924585013557)
                      ·
                        rfl

theorem cell23_304191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_304191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304191 prefixEnd_304191 := by exact prefixLift 304191
  have htrace : WordTrace (prefixWord ++ tailWord_304191) baseStart_304191 baseEnd_304191 := by
    simpa [prefixWord, tailWord_304191, baseEnd_304191] using wordTrace_append hprefix tailTrace_304191
  have hstable : (prefixWord ++ tailWord_304191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304191).length < 2 ^ (prefixWord ++ tailWord_304191).sum := by decide
  have hdescent : baseEnd_304191 < baseStart_304191 := by decide
  rcases family_descends (prefixWord ++ tailWord_304191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304224 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_304224 : Nat := 118140960795 + 304224 * 2 ^ 59
def prefixEnd_304224 : Nat := 4983230072969 + 3 ^ 40 * 304224 * 2
def baseEnd_304224 : Nat := 52071046211174318633635

theorem tailTrace_304224 : CollatzResearch.WordTrace tailWord_304224 prefixEnd_304224 52071046211174318633635 := by
  unfold tailWord_304224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547980424927940083887863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7397307233237253445183817 5547980424927940083887863)
  ·
    refine ⟨8321970637391910125831795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5547980424927940083887863 8321970637391910125831795)
    ·
      refine ⟨12482955956087865188747693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8321970637391910125831795 12482955956087865188747693)
      ·
        refine ⟨4681108483532949445780385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12482955956087865188747693 4681108483532949445780385)
        ·
          refine ⟨3510831362649712084335289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4681108483532949445780385 3510831362649712084335289)
          ·
            refine ⟨2633123521987284063251467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3510831362649712084335289 2633123521987284063251467)
            ·
              refine ⟨3949685282980926094877201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633123521987284063251467 3949685282980926094877201)
              ·
                refine ⟨2962263962235694571157901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3949685282980926094877201 2962263962235694571157901)
                ·
                  refine ⟨1110848985838385464184213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2962263962235694571157901 1110848985838385464184213)
                  ·
                    refine ⟨52071046211174318633635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1110848985838385464184213 52071046211174318633635)
                    ·
                      rfl

theorem cell23_304224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_304224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304224 prefixEnd_304224 := by exact prefixLift 304224
  have htrace : WordTrace (prefixWord ++ tailWord_304224) baseStart_304224 baseEnd_304224 := by
    simpa [prefixWord, tailWord_304224, baseEnd_304224] using wordTrace_append hprefix tailTrace_304224
  have hstable : (prefixWord ++ tailWord_304224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304224).length < 2 ^ (prefixWord ++ tailWord_304224).sum := by decide
  have hdescent : baseEnd_304224 < baseStart_304224 := by decide
  rcases family_descends (prefixWord ++ tailWord_304224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304231 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_304231 : Nat := 118140960795 + 304231 * 2 ^ 59
def prefixEnd_304231 : Nat := 4983230072969 + 3 ^ 40 * 304231 * 2
def baseEnd_304231 : Nat := 156216732998104428513373

theorem tailTrace_304231 : CollatzResearch.WordTrace tailWord_304231 prefixEnd_304231 156216732998104428513373 := by
  unfold tailWord_304231
  simp only [CollatzResearch.WordTrace]
  refine ⟨11096216160830520363280547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7397477440553680242187031 11096216160830520363280547)
  ·
    refine ⟨16644324241245780544920821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11096216160830520363280547 16644324241245780544920821)
    ·
      refine ⟨1560405397616791926086327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16644324241245780544920821 1560405397616791926086327)
      ·
        refine ⟨2340608096425187889129491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560405397616791926086327 2340608096425187889129491)
        ·
          refine ⟨3510912144637781833694237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340608096425187889129491 3510912144637781833694237)
          ·
            refine ⟨1316592054239168187635339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3510912144637781833694237 1316592054239168187635339)
            ·
              refine ⟨1974888081358752281453009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316592054239168187635339 1974888081358752281453009)
              ·
                refine ⟨1481166061019064211089757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974888081358752281453009 1481166061019064211089757)
                ·
                  refine ⟨555437272882149079158659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1481166061019064211089757 555437272882149079158659)
                  ·
                    refine ⟨833155909323223618737989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555437272882149079158659 833155909323223618737989)
                    ·
                      refine ⟨156216732998104428513373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 833155909323223618737989 156216732998104428513373)
                      ·
                        rfl

theorem cell23_304231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_304231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304231 prefixEnd_304231 := by exact prefixLift 304231
  have htrace : WordTrace (prefixWord ++ tailWord_304231) baseStart_304231 baseEnd_304231 := by
    simpa [prefixWord, tailWord_304231, baseEnd_304231] using wordTrace_append hprefix tailTrace_304231
  have hstable : (prefixWord ++ tailWord_304231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304231).length < 2 ^ (prefixWord ++ tailWord_304231).sum := by decide
  have hdescent : baseEnd_304231 < baseStart_304231 := by decide
  rcases family_descends (prefixWord ++ tailWord_304231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304248 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 5, 2, 2]
def baseStart_304248 : Nat := 118140960795 + 304248 * 2 ^ 59
def prefixEnd_304248 : Nat := 4983230072969 + 3 ^ 40 * 304248 * 2
def baseEnd_304248 : Nat := 156225462169230862000795

theorem tailTrace_304248 : CollatzResearch.WordTrace tailWord_304248 prefixEnd_304248 156225462169230862000795 := by
  unfold tailWord_304248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548418100884466133324699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7397890801179288177766265 5548418100884466133324699)
  ·
    refine ⟨8322627151326699199987049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5548418100884466133324699 8322627151326699199987049)
    ·
      refine ⟨6241970363495024399990287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8322627151326699199987049 6241970363495024399990287)
      ·
        refine ⟨9362955545242536599985431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241970363495024399990287 9362955545242536599985431)
        ·
          refine ⟨14044433317863804899978147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362955545242536599985431 14044433317863804899978147)
          ·
            refine ⟨21066649976795707349967221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14044433317863804899978147 21066649976795707349967221)
            ·
              refine ⟨1974998435324597564059427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21066649976795707349967221 1974998435324597564059427)
              ·
                refine ⟨2962497652986896346089141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974998435324597564059427 2962497652986896346089141)
                ·
                  refine ⟨277734154967521532445857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962497652986896346089141 277734154967521532445857)
                  ·
                    refine ⟨208300616225641149334393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277734154967521532445857 208300616225641149334393)
                    ·
                      refine ⟨156225462169230862000795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208300616225641149334393 156225462169230862000795)
                      ·
                        rfl

theorem cell23_304248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_304248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304248 prefixEnd_304248 := by exact prefixLift 304248
  have htrace : WordTrace (prefixWord ++ tailWord_304248) baseStart_304248 baseEnd_304248 := by
    simpa [prefixWord, tailWord_304248, baseEnd_304248] using wordTrace_append hprefix tailTrace_304248
  have hstable : (prefixWord ++ tailWord_304248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304248).length < 2 ^ (prefixWord ++ tailWord_304248).sum := by decide
  have hdescent : baseEnd_304248 < baseStart_304248 := by decide
  rcases family_descends (prefixWord ++ tailWord_304248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304265 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 1, 1, 4]
def baseStart_304265 : Nat := 118140960795 + 304265 * 2 ^ 59
def prefixEnd_304265 : Nat := 4983230072969 + 3 ^ 40 * 304265 * 2
def baseEnd_304265 : Nat := 156234191340357295488217

theorem tailTrace_304265 : CollatzResearch.WordTrace tailWord_304265 prefixEnd_304265 156234191340357295488217 := by
  unfold tailWord_304265
  simp only [CollatzResearch.WordTrace]
  refine ⟨11097456242707344170018249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7398304161804896113345499 11097456242707344170018249)
  ·
    refine ⟨8323092182030508127513687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11097456242707344170018249 8323092182030508127513687)
    ·
      refine ⟨12484638273045762191270531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323092182030508127513687 12484638273045762191270531)
      ·
        refine ⟨18726957409568643286905797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12484638273045762191270531 18726957409568643286905797)
        ·
          refine ⟨3511304514294120616294837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18726957409568643286905797 3511304514294120616294837)
          ·
            refine ⟨329184798215073807777641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3511304514294120616294837 329184798215073807777641)
            ·
              refine ⟨246888598661305355833231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329184798215073807777641 246888598661305355833231)
              ·
                refine ⟨370332897991958033749847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246888598661305355833231 370332897991958033749847)
                ·
                  refine ⟨555499346987937050624771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370332897991958033749847 555499346987937050624771)
                  ·
                    refine ⟨833249020481905575937157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 555499346987937050624771 833249020481905575937157)
                    ·
                      refine ⟨156234191340357295488217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 833249020481905575937157 156234191340357295488217)
                      ·
                        rfl

theorem cell23_304265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 1, 4].length) (baseStart_304265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304265 prefixEnd_304265 := by exact prefixLift 304265
  have htrace : WordTrace (prefixWord ++ tailWord_304265) baseStart_304265 baseEnd_304265 := by
    simpa [prefixWord, tailWord_304265, baseEnd_304265] using wordTrace_append hprefix tailTrace_304265
  have hstable : (prefixWord ++ tailWord_304265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304265).length < 2 ^ (prefixWord ++ tailWord_304265).sum := by decide
  have hdescent : baseEnd_304265 < baseStart_304265 := by decide
  rcases family_descends (prefixWord ++ tailWord_304265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304282 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2]
def baseStart_304282 : Nat := 118140960795 + 304282 * 2 ^ 59
def prefixEnd_304282 : Nat := 4983230072969 + 3 ^ 40 * 304282 * 2
def baseEnd_304282 : Nat := 156242920511483728975639

theorem tailTrace_304282 : CollatzResearch.WordTrace tailWord_304282 prefixEnd_304282 156242920511483728975639 := by
  unfold tailWord_304282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774519070911439018346775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7398717522430504048924733 2774519070911439018346775)
  ·
    refine ⟨4161778606367158527520163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774519070911439018346775 4161778606367158527520163)
    ·
      refine ⟨6242667909550737791280245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161778606367158527520163 6242667909550737791280245)
      ·
        refine ⟨585250116520381667932523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6242667909550737791280245 585250116520381667932523)
        ·
          refine ⟨877875174780572501898785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585250116520381667932523 877875174780572501898785)
          ·
            refine ⟨658406381085429376424089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877875174780572501898785 658406381085429376424089)
            ·
              refine ⟨493804785814072032318067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658406381085429376424089 493804785814072032318067)
              ·
                refine ⟨740707178721108048477101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493804785814072032318067 740707178721108048477101)
                ·
                  refine ⟨277765192020415518178913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740707178721108048477101 277765192020415518178913)
                  ·
                    refine ⟨208323894015311638634185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277765192020415518178913 208323894015311638634185)
                    ·
                      refine ⟨156242920511483728975639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208323894015311638634185 156242920511483728975639)
                      ·
                        rfl

theorem cell23_304282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_304282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304282 prefixEnd_304282 := by exact prefixLift 304282
  have htrace : WordTrace (prefixWord ++ tailWord_304282) baseStart_304282 baseEnd_304282 := by
    simpa [prefixWord, tailWord_304282, baseEnd_304282] using wordTrace_append hprefix tailTrace_304282
  have hstable : (prefixWord ++ tailWord_304282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304282).length < 2 ^ (prefixWord ++ tailWord_304282).sum := by decide
  have hdescent : baseEnd_304282 < baseStart_304282 := by decide
  rcases family_descends (prefixWord ++ tailWord_304282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304295 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_304295 : Nat := 118140960795 + 304295 * 2 ^ 59
def prefixEnd_304295 : Nat := 4983230072969 + 3 ^ 40 * 304295 * 2
def baseEnd_304295 : Nat := 156249595759992178113079

theorem tailTrace_304295 : CollatzResearch.WordTrace tailWord_304295 prefixEnd_304295 156249595759992178113079 := by
  unfold tailWord_304295
  simp only [CollatzResearch.WordTrace]
  refine ⟨11098550432598659293610339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7399033621732439529073559 11098550432598659293610339)
  ·
    refine ⟨16647825648897988940415509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11098550432598659293610339 16647825648897988940415509)
    ·
      refine ⟨780366827292093231581977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16647825648897988940415509 780366827292093231581977)
      ·
        refine ⟨585275120469069923686483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 780366827292093231581977 585275120469069923686483)
        ·
          refine ⟨877912680703604885529725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585275120469069923686483 877912680703604885529725)
          ·
            refine ⟨329217255263851832073647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 877912680703604885529725 329217255263851832073647)
            ·
              refine ⟨493825882895777748110471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329217255263851832073647 493825882895777748110471)
              ·
                refine ⟨740738824343666622165707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493825882895777748110471 740738824343666622165707)
                ·
                  refine ⟨1111108236515499933248561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740738824343666622165707 1111108236515499933248561)
                  ·
                    refine ⟨833331177386624949936421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1111108236515499933248561 833331177386624949936421)
                    ·
                      refine ⟨156249595759992178113079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 833331177386624949936421 156249595759992178113079)
                      ·
                        rfl

theorem cell23_304295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_304295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304295 prefixEnd_304295 := by exact prefixLift 304295
  have htrace : WordTrace (prefixWord ++ tailWord_304295) baseStart_304295 baseEnd_304295 := by
    simpa [prefixWord, tailWord_304295, baseEnd_304295] using wordTrace_append hprefix tailTrace_304295
  have hstable : (prefixWord ++ tailWord_304295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304295).length < 2 ^ (prefixWord ++ tailWord_304295).sum := by decide
  have hdescent : baseEnd_304295 < baseStart_304295 := by decide
  rcases family_descends (prefixWord ++ tailWord_304295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304322 : List Nat := [3, 5, 1, 1, 3, 1, 9]
def baseStart_304322 : Nat := 118140960795 + 304322 * 2 ^ 59
def prefixEnd_304322 : Nat := 4983230072969 + 3 ^ 40 * 304322 * 2
def baseEnd_304322 : Nat := 1929178515279797191055

theorem tailTrace_304322 : CollatzResearch.WordTrace tailWord_304322 prefixEnd_304322 1929178515279797191055 := by
  unfold tailWord_304322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774883800875210726210805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7399690135667228603228813 2774883800875210726210805)
  ·
    refine ⟨260145356332051005582263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2774883800875210726210805 260145356332051005582263)
    ·
      refine ⟨390218034498076508373395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260145356332051005582263 390218034498076508373395)
      ·
        refine ⟨585327051747114762560093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390218034498076508373395 585327051747114762560093)
        ·
          refine ⟨219497644405168035960035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 585327051747114762560093 219497644405168035960035)
          ·
            refine ⟨329246466607752053940053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219497644405168035960035 329246466607752053940053)
            ·
              refine ⟨1929178515279797191055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 329246466607752053940053 1929178515279797191055)
              ·
                rfl

theorem cell23_304322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 9].length) (baseStart_304322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304322 prefixEnd_304322 := by exact prefixLift 304322
  have htrace : WordTrace (prefixWord ++ tailWord_304322) baseStart_304322 baseEnd_304322 := by
    simpa [prefixWord, tailWord_304322, baseEnd_304322] using wordTrace_append hprefix tailTrace_304322
  have hstable : (prefixWord ++ tailWord_304322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304322).length < 2 ^ (prefixWord ++ tailWord_304322).sum := by decide
  have hdescent : baseEnd_304322 < baseStart_304322 := by decide
  rcases family_descends (prefixWord ++ tailWord_304322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304333 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_304333 : Nat := 118140960795 + 304333 * 2 ^ 59
def prefixEnd_304333 : Nat := 4983230072969 + 3 ^ 40 * 304333 * 2
def baseEnd_304333 : Nat := 156269108024863029437905

theorem tailTrace_304333 : CollatzResearch.WordTrace tailWord_304333 prefixEnd_304333 156269108024863029437905 := by
  unfold tailWord_304333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11099936406460991783493653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7399957604307327855662435 11099936406460991783493653)
  ·
    refine ⟨520309519052858989851265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11099936406460991783493653 520309519052858989851265)
    ·
      refine ⟨390232139289644242388449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520309519052858989851265 390232139289644242388449)
      ·
        refine ⟨292674104467233181791337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390232139289644242388449 292674104467233181791337)
        ·
          refine ⟨219505578350424886343503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292674104467233181791337 219505578350424886343503)
          ·
            refine ⟨329258367525637329515255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219505578350424886343503 329258367525637329515255)
            ·
              refine ⟨493887551288455994272883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329258367525637329515255 493887551288455994272883)
              ·
                refine ⟨740831326932683991409325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493887551288455994272883 740831326932683991409325)
                ·
                  refine ⟨277811747599756496778497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740831326932683991409325 277811747599756496778497)
                  ·
                    refine ⟨208358810699817372583873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277811747599756496778497 208358810699817372583873)
                    ·
                      refine ⟨156269108024863029437905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208358810699817372583873 156269108024863029437905)
                      ·
                        rfl

theorem cell23_304333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_304333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304333 prefixEnd_304333 := by exact prefixLift 304333
  have htrace : WordTrace (prefixWord ++ tailWord_304333) baseStart_304333 baseEnd_304333 := by
    simpa [prefixWord, tailWord_304333, baseEnd_304333] using wordTrace_append hprefix tailTrace_304333
  have hstable : (prefixWord ++ tailWord_304333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304333).length < 2 ^ (prefixWord ++ tailWord_304333).sum := by decide
  have hdescent : baseEnd_304333 < baseStart_304333 := by decide
  rcases family_descends (prefixWord ++ tailWord_304333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304351 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_304351 : Nat := 118140960795 + 304351 * 2 ^ 59
def prefixEnd_304351 : Nat := 4983230072969 + 3 ^ 40 * 304351 * 2
def baseEnd_304351 : Nat := 156278350676643959012821

theorem tailTrace_304351 : CollatzResearch.WordTrace tailWord_304351 prefixEnd_304351 156278350676643959012821 := by
  unfold tailWord_304351
  simp only [CollatzResearch.WordTrace]
  refine ⟨11100592920395780857648907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7400395280263853905099271 11100592920395780857648907)
  ·
    refine ⟨16650889380593671286473361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11100592920395780857648907 16650889380593671286473361)
    ·
      refine ⟨12488167035445253464855021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16650889380593671286473361 12488167035445253464855021)
      ·
        refine ⟨4683062638291970049320633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12488167035445253464855021 4683062638291970049320633)
        ·
          refine ⟨3512296978718977536990475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4683062638291970049320633 3512296978718977536990475)
          ·
            refine ⟨5268445468078466305485713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512296978718977536990475 5268445468078466305485713)
            ·
              refine ⟨3951334101058849729114285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5268445468078466305485713 3951334101058849729114285)
              ·
                refine ⟨1481750287897068648417857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3951334101058849729114285 1481750287897068648417857)
                ·
                  refine ⟨1111312715922801486313393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1481750287897068648417857 1111312715922801486313393)
                  ·
                    refine ⟨833484536942101114735045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1111312715922801486313393 833484536942101114735045)
                    ·
                      refine ⟨156278350676643959012821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 833484536942101114735045 156278350676643959012821)
                      ·
                        rfl

theorem cell23_304351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_304351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304351 prefixEnd_304351 := by exact prefixLift 304351
  have htrace : WordTrace (prefixWord ++ tailWord_304351) baseStart_304351 baseEnd_304351 := by
    simpa [prefixWord, tailWord_304351, baseEnd_304351] using wordTrace_append hprefix tailTrace_304351
  have hstable : (prefixWord ++ tailWord_304351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304351).length < 2 ^ (prefixWord ++ tailWord_304351).sum := by decide
  have hdescent : baseEnd_304351 < baseStart_304351 := by decide
  rcases family_descends (prefixWord ++ tailWord_304351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304359 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_304359 : Nat := 118140960795 + 304359 * 2 ^ 59
def prefixEnd_304359 : Nat := 4983230072969 + 3 ^ 40 * 304359 * 2
def baseEnd_304359 : Nat := 156282458521879927712785

theorem tailTrace_304359 : CollatzResearch.WordTrace tailWord_304359 prefixEnd_304359 156282458521879927712785 := by
  unfold tailWord_304359
  simp only [CollatzResearch.WordTrace]
  refine ⟨11100884704366798223940131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7400589802911198815960087 11100884704366798223940131)
  ·
    refine ⟨16651327056550197335910197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11100884704366798223940131 16651327056550197335910197)
    ·
      refine ⟨1561061911551581000241581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16651327056550197335910197 1561061911551581000241581)
      ·
        refine ⟨585398216831842875090593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1561061911551581000241581 585398216831842875090593)
        ·
          refine ⟨439048662623882156317945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585398216831842875090593 439048662623882156317945)
          ·
            refine ⟨329286496967911617238459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439048662623882156317945 329286496967911617238459)
            ·
              refine ⟨493929745451867425857689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329286496967911617238459 493929745451867425857689)
              ·
                refine ⟨370447309088900569393267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493929745451867425857689 370447309088900569393267)
                ·
                  refine ⟨555670963633350854089901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370447309088900569393267 555670963633350854089901)
                  ·
                    refine ⟨208376611362506570283713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555670963633350854089901 208376611362506570283713)
                    ·
                      refine ⟨156282458521879927712785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208376611362506570283713 156282458521879927712785)
                      ·
                        rfl

theorem cell23_304359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_304359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304359 prefixEnd_304359 := by exact prefixLift 304359
  have htrace : WordTrace (prefixWord ++ tailWord_304359) baseStart_304359 baseEnd_304359 := by
    simpa [prefixWord, tailWord_304359, baseEnd_304359] using wordTrace_append hprefix tailTrace_304359
  have hstable : (prefixWord ++ tailWord_304359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304359).length < 2 ^ (prefixWord ++ tailWord_304359).sum := by decide
  have hdescent : baseEnd_304359 < baseStart_304359 := by decide
  rcases family_descends (prefixWord ++ tailWord_304359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304378 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_304378 : Nat := 118140960795 + 304378 * 2 ^ 59
def prefixEnd_304378 : Nat := 4983230072969 + 3 ^ 40 * 304378 * 2
def baseEnd_304378 : Nat := 17365801628257261486133

theorem tailTrace_304378 : CollatzResearch.WordTrace tailWord_304378 prefixEnd_304378 17365801628257261486133 := by
  unfold tailWord_304378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775394422824491117220447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7401051794198642979254525 2775394422824491117220447)
  ·
    refine ⟨4163091634236736675830671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2775394422824491117220447 4163091634236736675830671)
    ·
      refine ⟨6244637451355105013746007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163091634236736675830671 6244637451355105013746007)
      ·
        refine ⟨9366956177032657520619011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244637451355105013746007 9366956177032657520619011)
        ·
          refine ⟨14050434265548986280928517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9366956177032657520619011 14050434265548986280928517)
          ·
            refine ⟨2634456424790434927674097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14050434265548986280928517 2634456424790434927674097)
            ·
              refine ⟨1975842318592826195755573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634456424790434927674097 1975842318592826195755573)
              ·
                refine ⟨185235217368077455852085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1975842318592826195755573 185235217368077455852085)
                ·
                  refine ⟨17365801628257261486133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185235217368077455852085 17365801628257261486133)
                  ·
                    rfl

theorem cell23_304378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_304378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304378 prefixEnd_304378 := by exact prefixLift 304378
  have htrace : WordTrace (prefixWord ++ tailWord_304378) baseStart_304378 baseEnd_304378 := by
    simpa [prefixWord, tailWord_304378, baseEnd_304378] using wordTrace_append hprefix tailTrace_304378
  have hstable : (prefixWord ++ tailWord_304378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304378).length < 2 ^ (prefixWord ++ tailWord_304378).sum := by decide
  have hdescent : baseEnd_304378 < baseStart_304378 := by decide
  rcases family_descends (prefixWord ++ tailWord_304378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304395 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 5]
def baseStart_304395 : Nat := 118140960795 + 304395 * 2 ^ 59
def prefixEnd_304395 : Nat := 4983230072969 + 3 ^ 40 * 304395 * 2
def baseEnd_304395 : Nat := 17366771536160198540291

theorem tailTrace_304395 : CollatzResearch.WordTrace tailWord_304395 prefixEnd_304395 17366771536160198540291 := by
  unfold tailWord_304395
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102197732236376372250639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7401465154824250914833759 11102197732236376372250639)
  ·
    refine ⟨16653296598354564558375959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11102197732236376372250639 16653296598354564558375959)
    ·
      refine ⟨24979944897531846837563939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16653296598354564558375959 24979944897531846837563939)
      ·
        refine ⟨37469917346297770256345909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24979944897531846837563939 37469917346297770256345909)
        ·
          refine ⟨3512804751215415961532429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37469917346297770256345909 3512804751215415961532429)
          ·
            refine ⟨1317301781705780985574661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3512804751215415961532429 1317301781705780985574661)
            ·
              refine ⟨246994084069833934795249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1317301781705780985574661 246994084069833934795249)
              ·
                refine ⟨185245563052375451096437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246994084069833934795249 185245563052375451096437)
                ·
                  refine ⟨17366771536160198540291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185245563052375451096437 17366771536160198540291)
                  ·
                    rfl

theorem cell23_304395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 5].length) (baseStart_304395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304395 prefixEnd_304395 := by exact prefixLift 304395
  have htrace : WordTrace (prefixWord ++ tailWord_304395) baseStart_304395 baseEnd_304395 := by
    simpa [prefixWord, tailWord_304395, baseEnd_304395] using wordTrace_append hprefix tailTrace_304395
  have hstable : (prefixWord ++ tailWord_304395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304395).length < 2 ^ (prefixWord ++ tailWord_304395).sum := by decide
  have hdescent : baseEnd_304395 < baseStart_304395 := by decide
  rcases family_descends (prefixWord ++ tailWord_304395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304401 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_304401 : Nat := 118140960795 + 304401 * 2 ^ 59
def prefixEnd_304401 : Nat := 4983230072969 + 3 ^ 40 * 304401 * 2
def baseEnd_304401 : Nat := 156304024709368763387591

theorem tailTrace_304401 : CollatzResearch.WordTrace tailWord_304401 prefixEnd_304401 156304024709368763387591 := by
  unfold tailWord_304401
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102416570214639396969057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7401611046809759597979371 11102416570214639396969057)
  ·
    refine ⟨8326812427660979547726793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11102416570214639396969057 8326812427660979547726793)
    ·
      refine ⟨6245109320745734660795095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8326812427660979547726793 6245109320745734660795095)
      ·
        refine ⟨9367663981118601991192643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245109320745734660795095 9367663981118601991192643)
        ·
          refine ⟨14051495971677902986788965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367663981118601991192643 14051495971677902986788965)
          ·
            refine ⟨2634655494689606810022931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14051495971677902986788965 2634655494689606810022931)
            ·
              refine ⟨3951983242034410215034397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634655494689606810022931 3951983242034410215034397)
              ·
                refine ⟨1481993715762903830637899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3951983242034410215034397 1481993715762903830637899)
                ·
                  refine ⟨2222990573644355745956849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481993715762903830637899 2222990573644355745956849)
                  ·
                    refine ⟨1667242930233266809467637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2222990573644355745956849 1667242930233266809467637)
                    ·
                      refine ⟨156304024709368763387591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1667242930233266809467637 156304024709368763387591)
                      ·
                        rfl

theorem cell23_304401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_304401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304401 prefixEnd_304401 := by exact prefixLift 304401
  have htrace : WordTrace (prefixWord ++ tailWord_304401) baseStart_304401 baseEnd_304401 := by
    simpa [prefixWord, tailWord_304401, baseEnd_304401] using wordTrace_append hprefix tailTrace_304401
  have hstable : (prefixWord ++ tailWord_304401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304401).length < 2 ^ (prefixWord ++ tailWord_304401).sum := by decide
  have hdescent : baseEnd_304401 < baseStart_304401 := by decide
  rcases family_descends (prefixWord ++ tailWord_304401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304402 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_304402 : Nat := 118140960795 + 304402 * 2 ^ 59
def prefixEnd_304402 : Nat := 4983230072969 + 3 ^ 40 * 304402 * 2
def baseEnd_304402 : Nat := 156304538190023259475087

theorem tailTrace_304402 : CollatzResearch.WordTrace tailWord_304402 prefixEnd_304402 156304538190023259475087 := by
  unfold tailWord_304402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775613260802754141938865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7401635362140677711836973 2775613260802754141938865)
  ·
    refine ⟨2081709945602065606454149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2775613260802754141938865 2081709945602065606454149)
    ·
      refine ⟨390320614800387301210153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2081709945602065606454149 390320614800387301210153)
      ·
        refine ⟨292740461100290475907615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390320614800387301210153 292740461100290475907615)
        ·
          refine ⟨439110691650435713861423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292740461100290475907615 439110691650435713861423)
          ·
            refine ⟨658666037475653570792135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439110691650435713861423 658666037475653570792135)
            ·
              refine ⟨987999056213480356188203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658666037475653570792135 987999056213480356188203)
              ·
                refine ⟨1481998584320220534282305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987999056213480356188203 1481998584320220534282305)
                ·
                  refine ⟨1111498938240165400711729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1481998584320220534282305 1111498938240165400711729)
                  ·
                    refine ⟨833624203680124050533797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1111498938240165400711729 833624203680124050533797)
                    ·
                      refine ⟨156304538190023259475087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 833624203680124050533797 156304538190023259475087)
                      ·
                        rfl

theorem cell23_304402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_304402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304402 prefixEnd_304402 := by exact prefixLift 304402
  have htrace : WordTrace (prefixWord ++ tailWord_304402) baseStart_304402 baseEnd_304402 := by
    simpa [prefixWord, tailWord_304402, baseEnd_304402] using wordTrace_append hprefix tailTrace_304402
  have hstable : (prefixWord ++ tailWord_304402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304402).length < 2 ^ (prefixWord ++ tailWord_304402).sum := by decide
  have hdescent : baseEnd_304402 < baseStart_304402 := by decide
  rcases family_descends (prefixWord ++ tailWord_304402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304411 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4]
def baseStart_304411 : Nat := 118140960795 + 304411 * 2 ^ 59
def prefixEnd_304411 : Nat := 4983230072969 + 3 ^ 40 * 304411 * 2
def baseEnd_304411 : Nat := 156309159515913724262545

theorem tailTrace_304411 : CollatzResearch.WordTrace tailWord_304411 prefixEnd_304411 156309159515913724262545 := by
  unfold tailWord_304411
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102781300178411104833087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7401854200118940736555391 11102781300178411104833087)
  ·
    refine ⟨16654171950267616657249631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11102781300178411104833087 16654171950267616657249631)
    ·
      refine ⟨24981257925401424985874447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654171950267616657249631 24981257925401424985874447)
      ·
        refine ⟨37471886888102137478811671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24981257925401424985874447 37471886888102137478811671)
        ·
          refine ⟨56207830332153206218217507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37471886888102137478811671 56207830332153206218217507)
          ·
            refine ⟨84311745498229809327326261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56207830332153206218217507 84311745498229809327326261)
            ·
              refine ⟨7904226140459044624436837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84311745498229809327326261 7904226140459044624436837)
              ·
                refine ⟨1482042401336070867081907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7904226140459044624436837 1482042401336070867081907)
                ·
                  refine ⟨2223063602004106300622861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482042401336070867081907 2223063602004106300622861)
                  ·
                    refine ⟨833648850751539862733573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223063602004106300622861 833648850751539862733573)
                    ·
                      refine ⟨156309159515913724262545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 833648850751539862733573 156309159515913724262545)
                      ·
                        rfl

theorem cell23_304411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_304411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304411 prefixEnd_304411 := by exact prefixLift 304411
  have htrace : WordTrace (prefixWord ++ tailWord_304411) baseStart_304411 baseEnd_304411 := by
    simpa [prefixWord, tailWord_304411, baseEnd_304411] using wordTrace_append hprefix tailTrace_304411
  have hstable : (prefixWord ++ tailWord_304411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304411).length < 2 ^ (prefixWord ++ tailWord_304411).sum := by decide
  have hdescent : baseEnd_304411 < baseStart_304411 := by decide
  rcases family_descends (prefixWord ++ tailWord_304411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304428 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 6, 2]
def baseStart_304428 : Nat := 118140960795 + 304428 * 2 ^ 59
def prefixEnd_304428 : Nat := 4983230072969 + 3 ^ 40 * 304428 * 2
def baseEnd_304428 : Nat := 156317888687040157749967

theorem tailTrace_304428 : CollatzResearch.WordTrace tailWord_304428 prefixEnd_304428 156317888687040157749967 := by
  unfold tailWord_304428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551700670558411504100969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7402267560744548672134625 5551700670558411504100969)
  ·
    refine ⟨4163775502918808628075727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5551700670558411504100969 4163775502918808628075727)
    ·
      refine ⟨6245663254378212942113591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163775502918808628075727 6245663254378212942113591)
      ·
        refine ⟨9368494881567319413170387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245663254378212942113591 9368494881567319413170387)
        ·
          refine ⟨14052742322350979119755581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368494881567319413170387 14052742322350979119755581)
          ·
            refine ⟨5269778370881617169908343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14052742322350979119755581 5269778370881617169908343)
            ·
              refine ⟨7904667556322425754862515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269778370881617169908343 7904667556322425754862515)
              ·
                refine ⟨11857001334483638632293773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7904667556322425754862515 11857001334483638632293773)
                ·
                  refine ⟨4446375500431364487110165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11857001334483638632293773 4446375500431364487110165)
                  ·
                    refine ⟨208423851582720210333289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4446375500431364487110165 208423851582720210333289)
                    ·
                      refine ⟨156317888687040157749967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208423851582720210333289 156317888687040157749967)
                      ·
                        rfl

theorem cell23_304428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_304428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304428 prefixEnd_304428 := by exact prefixLift 304428
  have htrace : WordTrace (prefixWord ++ tailWord_304428) baseStart_304428 baseEnd_304428 := by
    simpa [prefixWord, tailWord_304428, baseEnd_304428] using wordTrace_append hprefix tailTrace_304428
  have hstable : (prefixWord ++ tailWord_304428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304428).length < 2 ^ (prefixWord ++ tailWord_304428).sum := by decide
  have hdescent : baseEnd_304428 < baseStart_304428 := by decide
  rcases family_descends (prefixWord ++ tailWord_304428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304448 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_304448 : Nat := 118140960795 + 304448 * 2 ^ 59
def prefixEnd_304448 : Nat := 4983230072969 + 3 ^ 40 * 304448 * 2
def baseEnd_304448 : Nat := 156328158300130079499875

theorem tailTrace_304448 : CollatzResearch.WordTrace tailWord_304448 prefixEnd_304448 156328158300130079499875 := by
  unfold tailWord_304448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552065400522183211964999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7402753867362910949286665 5552065400522183211964999)
  ·
    refine ⟨8328098100783274817947499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5552065400522183211964999 8328098100783274817947499)
    ·
      refine ⟨12492147151174912226921249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8328098100783274817947499 12492147151174912226921249)
      ·
        refine ⟨9369110363381184170190937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12492147151174912226921249 9369110363381184170190937)
        ·
          refine ⟨7026832772535888127643203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9369110363381184170190937 7026832772535888127643203)
          ·
            refine ⟨10540249158803832191464805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7026832772535888127643203 10540249158803832191464805)
            ·
              refine ⟨1976296717275718535899651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10540249158803832191464805 1976296717275718535899651)
              ·
                refine ⟨2964445075913577803849477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976296717275718535899651 2964445075913577803849477)
                ·
                  refine ⟨555833451733795838221777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2964445075913577803849477 555833451733795838221777)
                  ·
                    refine ⟨416875088800346878666333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 555833451733795838221777 416875088800346878666333)
                    ·
                      refine ⟨156328158300130079499875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 416875088800346878666333 156328158300130079499875)
                      ·
                        rfl

theorem cell23_304448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_304448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304448 prefixEnd_304448 := by exact prefixLift 304448
  have htrace : WordTrace (prefixWord ++ tailWord_304448) baseStart_304448 baseEnd_304448 := by
    simpa [prefixWord, tailWord_304448, baseEnd_304448] using wordTrace_append hprefix tailTrace_304448
  have hstable : (prefixWord ++ tailWord_304448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304448).length < 2 ^ (prefixWord ++ tailWord_304448).sum := by decide
  have hdescent : baseEnd_304448 < baseStart_304448 := by decide
  rcases family_descends (prefixWord ++ tailWord_304448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304455 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 3, 4]
def baseStart_304455 : Nat := 118140960795 + 304455 * 2 ^ 59
def prefixEnd_304455 : Nat := 4983230072969 + 3 ^ 40 * 304455 * 2
def baseEnd_304455 : Nat := 52110584221570517370781

theorem tailTrace_304455 : CollatzResearch.WordTrace tailWord_304455 prefixEnd_304455 52110584221570517370781 := by
  unfold tailWord_304455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11104386112019006619434819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7402924074679337746289879 11104386112019006619434819)
  ·
    refine ⟨16656579168028509929152229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11104386112019006619434819 16656579168028509929152229)
    ·
      refine ⟨3123108594005345611716043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16656579168028509929152229 3123108594005345611716043)
      ·
        refine ⟨4684662891008018417574065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123108594005345611716043 4684662891008018417574065)
        ·
          refine ⟨3513497168256013813180549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4684662891008018417574065 3513497168256013813180549)
          ·
            refine ⟨658780719048002589971353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3513497168256013813180549 658780719048002589971353)
            ·
              refine ⟨494085539286001942478515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658780719048002589971353 494085539286001942478515)
              ·
                refine ⟨741128308929002913717773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494085539286001942478515 741128308929002913717773)
                ·
                  refine ⟨277923115848376092644165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741128308929002913717773 277923115848376092644165)
                  ·
                    refine ⟨52110584221570517370781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277923115848376092644165 52110584221570517370781)
                    ·
                      rfl

theorem cell23_304455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_304455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304455 prefixEnd_304455 := by exact prefixLift 304455
  have htrace : WordTrace (prefixWord ++ tailWord_304455) baseStart_304455 baseEnd_304455 := by
    simpa [prefixWord, tailWord_304455, baseEnd_304455] using wordTrace_append hprefix tailTrace_304455
  have hstable : (prefixWord ++ tailWord_304455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304455).length < 2 ^ (prefixWord ++ tailWord_304455).sum := by decide
  have hdescent : baseEnd_304455 < baseStart_304455 := by decide
  rcases family_descends (prefixWord ++ tailWord_304455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304481 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_304481 : Nat := 118140960795 + 304481 * 2 ^ 59
def prefixEnd_304481 : Nat := 4983230072969 + 3 ^ 40 * 304481 * 2
def baseEnd_304481 : Nat := 52115034387242816795741

theorem tailTrace_304481 : CollatzResearch.WordTrace tailWord_304481 prefixEnd_304481 52115034387242816795741 := by
  unfold tailWord_304481
  simp only [CollatzResearch.WordTrace]
  refine ⟨11105334409924813059881297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7403556273283208706587531 11105334409924813059881297)
  ·
    refine ⟨8329000807443609794910973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11105334409924813059881297 8329000807443609794910973)
    ·
      refine ⟨3123375302791353673091615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8329000807443609794910973 3123375302791353673091615)
      ·
        refine ⟨4685062954187030509637423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123375302791353673091615 4685062954187030509637423)
        ·
          refine ⟨7027594431280545764456135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685062954187030509637423 7027594431280545764456135)
          ·
            refine ⟨10541391646920818646684203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7027594431280545764456135 10541391646920818646684203)
            ·
              refine ⟨15812087470381227970026305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10541391646920818646684203 15812087470381227970026305)
              ·
                refine ⟨11859065602785920977519729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15812087470381227970026305 11859065602785920977519729)
                ·
                  refine ⟨8894299202089440733139797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11859065602785920977519729 8894299202089440733139797)
                  ·
                    refine ⟨52115034387242816795741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 8894299202089440733139797 52115034387242816795741)
                    ·
                      rfl

theorem cell23_304481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_304481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304481 prefixEnd_304481 := by exact prefixLift 304481
  have htrace : WordTrace (prefixWord ++ tailWord_304481) baseStart_304481 baseEnd_304481 := by
    simpa [prefixWord, tailWord_304481, baseEnd_304481] using wordTrace_append hprefix tailTrace_304481
  have hstable : (prefixWord ++ tailWord_304481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304481).length < 2 ^ (prefixWord ++ tailWord_304481).sum := by decide
  have hdescent : baseEnd_304481 < baseStart_304481 := by decide
  rcases family_descends (prefixWord ++ tailWord_304481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304491 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_304491 : Nat := 118140960795 + 304491 * 2 ^ 59
def prefixEnd_304491 : Nat := 4983230072969 + 3 ^ 40 * 304491 * 2
def baseEnd_304491 : Nat := 156350237968273411262177

theorem tailTrace_304491 : CollatzResearch.WordTrace tailWord_304491 prefixEnd_304491 156350237968273411262177 := by
  unfold tailWord_304491
  simp only [CollatzResearch.WordTrace]
  refine ⟨11105699139888584767745327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7403799426592389845163551 11105699139888584767745327)
  ·
    refine ⟨16658548709832877151617991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11105699139888584767745327 16658548709832877151617991)
    ·
      refine ⟨24987823064749315727426987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16658548709832877151617991 24987823064749315727426987)
      ·
        refine ⟨37481734597123973591140481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24987823064749315727426987 37481734597123973591140481)
        ·
          refine ⟨28111300947842980193355361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37481734597123973591140481 28111300947842980193355361)
          ·
            refine ⟨21083475710882235145016521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28111300947842980193355361 21083475710882235145016521)
            ·
              refine ⟨15812606783161676358762391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21083475710882235145016521 15812606783161676358762391)
              ·
                refine ⟨23718910174742514538143587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15812606783161676358762391 23718910174742514538143587)
                ·
                  refine ⟨35578365262113771807215381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23718910174742514538143587 35578365262113771807215381)
                  ·
                    refine ⟨1667735871661583053463221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35578365262113771807215381 1667735871661583053463221)
                    ·
                      refine ⟨156350237968273411262177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1667735871661583053463221 156350237968273411262177)
                      ·
                        rfl

theorem cell23_304491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_304491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304491 prefixEnd_304491 := by exact prefixLift 304491
  have htrace : WordTrace (prefixWord ++ tailWord_304491) baseStart_304491 baseEnd_304491 := by
    simpa [prefixWord, tailWord_304491, baseEnd_304491] using wordTrace_append hprefix tailTrace_304491
  have hstable : (prefixWord ++ tailWord_304491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304491).length < 2 ^ (prefixWord ++ tailWord_304491).sum := by decide
  have hdescent : baseEnd_304491 < baseStart_304491 := by decide
  rcases family_descends (prefixWord ++ tailWord_304491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304505 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 4, 3, 2]
def baseStart_304505 : Nat := 118140960795 + 304505 * 2 ^ 59
def prefixEnd_304505 : Nat := 4983230072969 + 3 ^ 40 * 304505 * 2
def baseEnd_304505 : Nat := 156357426697436356487113

theorem tailTrace_304505 : CollatzResearch.WordTrace tailWord_304505 prefixEnd_304505 156357426697436356487113 := by
  unfold tailWord_304505
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106209761837865158754969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7404139841225243439169979 11106209761837865158754969)
  ·
    refine ⟨8329657321378398869066227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11106209761837865158754969 8329657321378398869066227)
    ·
      refine ⟨12494485982067598303599341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8329657321378398869066227 12494485982067598303599341)
      ·
        refine ⟨4685432243275349363849753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12494485982067598303599341 4685432243275349363849753)
        ·
          refine ⟨3514074182456512022887315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685432243275349363849753 3514074182456512022887315)
          ·
            refine ⟨5271111273684768034330973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514074182456512022887315 5271111273684768034330973)
            ·
              refine ⟨1976666727631788012874115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5271111273684768034330973 1976666727631788012874115)
              ·
                refine ⟨2965000091447682019311173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976666727631788012874115 2965000091447682019311173)
                ·
                  refine ⟨555937517146440378620845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2965000091447682019311173 555937517146440378620845)
                  ·
                    refine ⟨208476568929915141982817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 555937517146440378620845 208476568929915141982817)
                    ·
                      refine ⟨156357426697436356487113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208476568929915141982817 156357426697436356487113)
                      ·
                        rfl

theorem cell23_304505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_304505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304505 prefixEnd_304505 := by exact prefixLift 304505
  have htrace : WordTrace (prefixWord ++ tailWord_304505) baseStart_304505 baseEnd_304505 := by
    simpa [prefixWord, tailWord_304505, baseEnd_304505] using wordTrace_append hprefix tailTrace_304505
  have hstable : (prefixWord ++ tailWord_304505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304505).length < 2 ^ (prefixWord ++ tailWord_304505).sum := by decide
  have hdescent : baseEnd_304505 < baseStart_304505 := by decide
  rcases family_descends (prefixWord ++ tailWord_304505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304511 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 10]
def baseStart_304511 : Nat := 118140960795 + 304511 * 2 ^ 59
def prefixEnd_304511 : Nat := 4983230072969 + 3 ^ 40 * 304511 * 2
def baseEnd_304511 : Nat := 52120169193787777670695

theorem tailTrace_304511 : CollatzResearch.WordTrace tailWord_304511 prefixEnd_304511 52120169193787777670695 := by
  unfold tailWord_304511
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106428599816128183473387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7404285733210752122315591 11106428599816128183473387)
  ·
    refine ⟨16659642899724192275210081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11106428599816128183473387 16659642899724192275210081)
    ·
      refine ⟨12494732174793144206407561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16659642899724192275210081 12494732174793144206407561)
      ·
        refine ⟨9371049131094858154805671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12494732174793144206407561 9371049131094858154805671)
        ·
          refine ⟨14056573696642287232208507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9371049131094858154805671 14056573696642287232208507)
          ·
            refine ⟨21084860544963430848312761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14056573696642287232208507 21084860544963430848312761)
            ·
              refine ⟨15813645408722573136234571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21084860544963430848312761 15813645408722573136234571)
              ·
                refine ⟨23720468113083859704351857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15813645408722573136234571 23720468113083859704351857)
                ·
                  refine ⟨17790351084812894778263893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23720468113083859704351857 17790351084812894778263893)
                  ·
                    refine ⟨52120169193787777670695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 17790351084812894778263893 52120169193787777670695)
                    ·
                      rfl

theorem cell23_304511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_304511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304511 prefixEnd_304511 := by exact prefixLift 304511
  have htrace : WordTrace (prefixWord ++ tailWord_304511) baseStart_304511 baseEnd_304511 := by
    simpa [prefixWord, tailWord_304511, baseEnd_304511] using wordTrace_append hprefix tailTrace_304511
  have hstable : (prefixWord ++ tailWord_304511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304511).length < 2 ^ (prefixWord ++ tailWord_304511).sum := by decide
  have hdescent : baseEnd_304511 < baseStart_304511 := by decide
  rcases family_descends (prefixWord ++ tailWord_304511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304512 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 1, 1, 3]
def baseStart_304512 : Nat := 118140960795 + 304512 * 2 ^ 59
def prefixEnd_304512 : Nat := 4983230072969 + 3 ^ 40 * 304512 * 2
def baseEnd_304512 : Nat := 156361021062017829099581

theorem tailTrace_304512 : CollatzResearch.WordTrace tailWord_304512 prefixEnd_304512 156361021062017829099581 := by
  unfold tailWord_304512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553232536406252677129895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7404310048541670236173193 5553232536406252677129895)
  ·
    refine ⟨8329848804609379015694843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5553232536406252677129895 8329848804609379015694843)
    ·
      refine ⟨12494773206914068523542265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8329848804609379015694843 12494773206914068523542265)
      ·
        refine ⟨9371079905185551392656699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12494773206914068523542265 9371079905185551392656699)
        ·
          refine ⟨14056619857778327088985049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9371079905185551392656699 14056619857778327088985049)
          ·
            refine ⟨10542464893333745316738787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14056619857778327088985049 10542464893333745316738787)
            ·
              refine ⟨15813697340000617975108181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542464893333745316738787 15813697340000617975108181)
              ·
                refine ⟨185316765703132241895799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 15813697340000617975108181 185316765703132241895799)
                ·
                  refine ⟨277975148554698362843699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185316765703132241895799 277975148554698362843699)
                  ·
                    refine ⟨416962722832047544265549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277975148554698362843699 416962722832047544265549)
                    ·
                      refine ⟨156361021062017829099581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 416962722832047544265549 156361021062017829099581)
                      ·
                        rfl

theorem cell23_304512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_304512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304512 prefixEnd_304512 := by exact prefixLift 304512
  have htrace : WordTrace (prefixWord ++ tailWord_304512) baseStart_304512 baseEnd_304512 := by
    simpa [prefixWord, tailWord_304512, baseEnd_304512] using wordTrace_append hprefix tailTrace_304512
  have hstable : (prefixWord ++ tailWord_304512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304512).length < 2 ^ (prefixWord ++ tailWord_304512).sum := by decide
  have hdescent : baseEnd_304512 < baseStart_304512 := by decide
  rcases family_descends (prefixWord ++ tailWord_304512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304532 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_304532 : Nat := 118140960795 + 304532 * 2 ^ 59
def prefixEnd_304532 : Nat := 4983230072969 + 3 ^ 40 * 304532 * 2
def baseEnd_304532 : Nat := 52123763558369250283163

theorem tailTrace_304532 : CollatzResearch.WordTrace tailWord_304532 prefixEnd_304532 52123763558369250283163 := by
  unfold tailWord_304532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553597266370024384993925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7404796355160032513325233 5553597266370024384993925)
  ·
    refine ⟨1041299487444379572186361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5553597266370024384993925 1041299487444379572186361)
    ·
      refine ⟨780974615583284679139771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1041299487444379572186361 780974615583284679139771)
      ·
        refine ⟨1171461923374927018709657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780974615583284679139771 1171461923374927018709657)
        ·
          refine ⟨878596442531195264032243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1171461923374927018709657 878596442531195264032243)
          ·
            refine ⟨1317894663796792896048365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878596442531195264032243 1317894663796792896048365)
            ·
              refine ⟨494210498923797336018137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1317894663796792896048365 494210498923797336018137)
              ·
                refine ⟨370657874192848002013603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494210498923797336018137 370657874192848002013603)
                ·
                  refine ⟨555986811289272003020405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370657874192848002013603 555986811289272003020405)
                  ·
                    refine ⟨52123763558369250283163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 555986811289272003020405 52123763558369250283163)
                    ·
                      rfl

theorem cell23_304532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_304532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304532 prefixEnd_304532 := by exact prefixLift 304532
  have htrace : WordTrace (prefixWord ++ tailWord_304532) baseStart_304532 baseEnd_304532 := by
    simpa [prefixWord, tailWord_304532, baseEnd_304532] using wordTrace_append hprefix tailTrace_304532
  have hstable : (prefixWord ++ tailWord_304532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304532).length < 2 ^ (prefixWord ++ tailWord_304532).sum := by decide
  have hdescent : baseEnd_304532 < baseStart_304532 := by decide
  rcases family_descends (prefixWord ++ tailWord_304532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304585 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 3]
def baseStart_304585 : Nat := 118140960795 + 304585 * 2 ^ 59
def prefixEnd_304585 : Nat := 4983230072969 + 3 ^ 40 * 304585 * 2
def baseEnd_304585 : Nat := 156398505149796043486745

theorem tailTrace_304585 : CollatzResearch.WordTrace tailWord_304585 prefixEnd_304585 156398505149796043486745 := by
  unfold tailWord_304585
  simp only [CollatzResearch.WordTrace]
  refine ⟨11109127601548038821667209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7406085067698692547778139 11109127601548038821667209)
  ·
    refine ⟨8331845701161029116250407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11109127601548038821667209 8331845701161029116250407)
    ·
      refine ⟨12497768551741543674375611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8331845701161029116250407 12497768551741543674375611)
      ·
        refine ⟨18746652827612315511563417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12497768551741543674375611 18746652827612315511563417)
        ·
          refine ⟨14059989620709236633672563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18746652827612315511563417 14059989620709236633672563)
          ·
            refine ⟨21089984431063854950508845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14059989620709236633672563 21089984431063854950508845)
            ·
              refine ⟨7908744161648945606440817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21089984431063854950508845 7908744161648945606440817)
              ·
                refine ⟨5931558121236709204830613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908744161648945606440817 5931558121236709204830613)
                ·
                  refine ⟨278041786932970743976435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5931558121236709204830613 278041786932970743976435)
                  ·
                    refine ⟨417062680399456115964653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 278041786932970743976435 417062680399456115964653)
                    ·
                      refine ⟨156398505149796043486745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417062680399456115964653 156398505149796043486745)
                      ·
                        rfl

theorem cell23_304585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_304585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304585 prefixEnd_304585 := by exact prefixLift 304585
  have htrace : WordTrace (prefixWord ++ tailWord_304585) baseStart_304585 baseEnd_304585 := by
    simpa [prefixWord, tailWord_304585, baseEnd_304585] using wordTrace_append hprefix tailTrace_304585
  have hstable : (prefixWord ++ tailWord_304585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304585).length < 2 ^ (prefixWord ++ tailWord_304585).sum := by decide
  have hdescent : baseEnd_304585 < baseStart_304585 := by decide
  rcases family_descends (prefixWord ++ tailWord_304585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304608 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_304608 : Nat := 118140960795 + 304608 * 2 ^ 59
def prefixEnd_304608 : Nat := 4983230072969 + 3 ^ 40 * 304608 * 2
def baseEnd_304608 : Nat := 156410315204849453499139

theorem tailTrace_304608 : CollatzResearch.WordTrace tailWord_304608 prefixEnd_304608 156410315204849453499139 := by
  unfold tailWord_304608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554983240232356874877239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7406644320309809166502985 5554983240232356874877239)
  ·
    refine ⟨8332474860348535312315859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5554983240232356874877239 8332474860348535312315859)
    ·
      refine ⟨12498712290522802968473789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8332474860348535312315859 12498712290522802968473789)
      ·
        refine ⟨4687017108946051113177671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12498712290522802968473789 4687017108946051113177671)
        ·
          refine ⟨7030525663419076669766507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687017108946051113177671 7030525663419076669766507)
          ·
            refine ⟨10545788495128615004649761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030525663419076669766507 10545788495128615004649761)
            ·
              refine ⟨7909341371346461253487321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10545788495128615004649761 7909341371346461253487321)
              ·
                refine ⟨5932006028509845940115491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7909341371346461253487321 5932006028509845940115491)
                ·
                  refine ⟨8898009042764768910173237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5932006028509845940115491 8898009042764768910173237)
                  ·
                    refine ⟨834188347759197085328741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8898009042764768910173237 834188347759197085328741)
                    ·
                      refine ⟨156410315204849453499139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 834188347759197085328741 156410315204849453499139)
                      ·
                        rfl

theorem cell23_304608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_304608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304608 prefixEnd_304608 := by exact prefixLift 304608
  have htrace : WordTrace (prefixWord ++ tailWord_304608) baseStart_304608 baseEnd_304608 := by
    simpa [prefixWord, tailWord_304608, baseEnd_304608] using wordTrace_append hprefix tailTrace_304608
  have hstable : (prefixWord ++ tailWord_304608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304608).length < 2 ^ (prefixWord ++ tailWord_304608).sum := by decide
  have hdescent : baseEnd_304608 < baseStart_304608 := by decide
  rcases family_descends (prefixWord ++ tailWord_304608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304693 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_304693 : Nat := 118140960795 + 304693 * 2 ^ 59
def prefixEnd_304693 : Nat := 4983230072969 + 3 ^ 40 * 304693 * 2
def baseEnd_304693 : Nat := 156453961060481620936249

theorem tailTrace_304693 : CollatzResearch.WordTrace tailWord_304693 prefixEnd_304693 156453961060481620936249 := by
  unfold tailWord_304693
  simp only [CollatzResearch.WordTrace]
  refine ⟨11113066685156773266598733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7408711123437848844399155 11113066685156773266598733)
  ·
    refine ⟨4167400006933789974974525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11113066685156773266598733 4167400006933789974974525)
    ·
      refine ⟨1562775002600171240615447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4167400006933789974974525 1562775002600171240615447)
      ·
        refine ⟨2344162503900256860923171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562775002600171240615447 2344162503900256860923171)
        ·
          refine ⟨3516243755850385291384757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344162503900256860923171 3516243755850385291384757)
          ·
            refine ⟨329647852110973621067321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3516243755850385291384757 329647852110973621067321)
            ·
              refine ⟨247235889083230215800491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329647852110973621067321 247235889083230215800491)
              ·
                refine ⟨370853833624845323700737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247235889083230215800491 370853833624845323700737)
                ·
                  refine ⟨278140375218633992775553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370853833624845323700737 278140375218633992775553)
                  ·
                    refine ⟨208605281413975494581665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 278140375218633992775553 208605281413975494581665)
                    ·
                      refine ⟨156453961060481620936249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208605281413975494581665 156453961060481620936249)
                      ·
                        rfl

theorem cell23_304693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_304693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304693 prefixEnd_304693 := by exact prefixLift 304693
  have htrace : WordTrace (prefixWord ++ tailWord_304693) baseStart_304693 baseEnd_304693 := by
    simpa [prefixWord, tailWord_304693, baseEnd_304693] using wordTrace_append hprefix tailTrace_304693
  have hstable : (prefixWord ++ tailWord_304693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304693).length < 2 ^ (prefixWord ++ tailWord_304693).sum := by decide
  have hdescent : baseEnd_304693 < baseStart_304693 := by decide
  rcases family_descends (prefixWord ++ tailWord_304693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304705 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_304705 : Nat := 118140960795 + 304705 * 2 ^ 59
def prefixEnd_304705 : Nat := 4983230072969 + 3 ^ 40 * 304705 * 2
def baseEnd_304705 : Nat := 156460122828335573986193

theorem tailTrace_304705 : CollatzResearch.WordTrace tailWord_304705 prefixEnd_304705 156460122828335573986193 := by
  unfold tailWord_304705
  simp only [CollatzResearch.WordTrace]
  refine ⟨11113504361113299316035569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7409002907408866210690379 11113504361113299316035569)
  ·
    refine ⟨8335128270834974487026677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11113504361113299316035569 8335128270834974487026677)
    ·
      refine ⟨781418275390778858158751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8335128270834974487026677 781418275390778858158751)
      ·
        refine ⟨1172127413086168287238127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781418275390778858158751 1172127413086168287238127)
        ·
          refine ⟨1758191119629252430857191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172127413086168287238127 1758191119629252430857191)
          ·
            refine ⟨2637286679443878646285787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758191119629252430857191 2637286679443878646285787)
            ·
              refine ⟨3955930019165817969428681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637286679443878646285787 3955930019165817969428681)
              ·
                refine ⟨2966947514374363477071511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3955930019165817969428681 2966947514374363477071511)
                ·
                  refine ⟨4450421271561545215607267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966947514374363477071511 4450421271561545215607267)
                  ·
                    refine ⟨6675631907342317823410901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450421271561545215607267 6675631907342317823410901)
                    ·
                      refine ⟨156460122828335573986193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6675631907342317823410901 156460122828335573986193)
                      ·
                        rfl

theorem cell23_304705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_304705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304705 prefixEnd_304705 := by exact prefixLift 304705
  have htrace : WordTrace (prefixWord ++ tailWord_304705) baseStart_304705 baseEnd_304705 := by
    simpa [prefixWord, tailWord_304705, baseEnd_304705] using wordTrace_append hprefix tailTrace_304705
  have hstable : (prefixWord ++ tailWord_304705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304705).length < 2 ^ (prefixWord ++ tailWord_304705).sum := by decide
  have hdescent : baseEnd_304705 < baseStart_304705 := by decide
  rcases family_descends (prefixWord ++ tailWord_304705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304735 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_304735 : Nat := 118140960795 + 304735 * 2 ^ 59
def prefixEnd_304735 : Nat := 4983230072969 + 3 ^ 40 * 304735 * 2
def baseEnd_304735 : Nat := 156475527247970456611055

theorem tailTrace_304735 : CollatzResearch.WordTrace tailWord_304735 prefixEnd_304735 156475527247970456611055 := by
  unfold tailWord_304735
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114598551004614439627659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7409732367336409626418439 11114598551004614439627659)
  ·
    refine ⟨16671897826506921659441489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11114598551004614439627659 16671897826506921659441489)
    ·
      refine ⟨12503923369880191244581117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16671897826506921659441489 12503923369880191244581117)
      ·
        refine ⟨4688971263705071716717919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12503923369880191244581117 4688971263705071716717919)
        ·
          refine ⟨7033456895557607575076879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688971263705071716717919 7033456895557607575076879)
          ·
            refine ⟨10550185343336411362615319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7033456895557607575076879 10550185343336411362615319)
            ·
              refine ⟨15825278015004617043922979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10550185343336411362615319 15825278015004617043922979)
              ·
                refine ⟨23737917022506925565884469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15825278015004617043922979 23737917022506925565884469)
                ·
                  refine ⟨2225429720860024271801669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23737917022506925565884469 2225429720860024271801669)
                  ·
                    refine ⟨417268072661254550962813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225429720860024271801669 417268072661254550962813)
                    ·
                      refine ⟨156475527247970456611055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417268072661254550962813 156475527247970456611055)
                      ·
                        rfl

theorem cell23_304735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_304735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304735 prefixEnd_304735 := by exact prefixLift 304735
  have htrace : WordTrace (prefixWord ++ tailWord_304735) baseStart_304735 baseEnd_304735 := by
    simpa [prefixWord, tailWord_304735, baseEnd_304735] using wordTrace_append hprefix tailTrace_304735
  have hstable : (prefixWord ++ tailWord_304735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304735).length < 2 ^ (prefixWord ++ tailWord_304735).sum := by decide
  have hdescent : baseEnd_304735 < baseStart_304735 := by decide
  rcases family_descends (prefixWord ++ tailWord_304735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304769 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_304769 : Nat := 118140960795 + 304769 * 2 ^ 59
def prefixEnd_304769 : Nat := 4983230072969 + 3 ^ 40 * 304769 * 2
def baseEnd_304769 : Nat := 156492985590223323585899

theorem tailTrace_304769 : CollatzResearch.WordTrace tailWord_304769 prefixEnd_304769 156492985590223323585899 := by
  unfold tailWord_304769
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115838632881438246365361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7410559088587625497576907 11115838632881438246365361)
  ·
    refine ⟨8336878974661078684774021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11115838632881438246365361 8336878974661078684774021)
    ·
      refine ⟨1563164807748952253395129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8336878974661078684774021 1563164807748952253395129)
      ·
        refine ⟨1172373605811714190046347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1563164807748952253395129 1172373605811714190046347)
        ·
          refine ⟨1758560408717571285069521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172373605811714190046347 1758560408717571285069521)
          ·
            refine ⟨1318920306538178463802141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758560408717571285069521 1318920306538178463802141)
            ·
              refine ⟨494595114951816923925803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1318920306538178463802141 494595114951816923925803)
              ·
                refine ⟨741892672427725385888705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494595114951816923925803 741892672427725385888705)
                ·
                  refine ⟨556419504320794039416529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 741892672427725385888705 556419504320794039416529)
                  ·
                    refine ⟨417314628240595529562397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 556419504320794039416529 417314628240595529562397)
                    ·
                      refine ⟨156492985590223323585899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417314628240595529562397 156492985590223323585899)
                      ·
                        rfl

theorem cell23_304769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_304769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304769 prefixEnd_304769 := by exact prefixLift 304769
  have htrace : WordTrace (prefixWord ++ tailWord_304769) baseStart_304769 baseEnd_304769 := by
    simpa [prefixWord, tailWord_304769, baseEnd_304769] using wordTrace_append hprefix tailTrace_304769
  have hstable : (prefixWord ++ tailWord_304769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304769).length < 2 ^ (prefixWord ++ tailWord_304769).sum := by decide
  have hdescent : baseEnd_304769 < baseStart_304769 := by decide
  rcases family_descends (prefixWord ++ tailWord_304769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304785 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_304785 : Nat := 118140960795 + 304785 * 2 ^ 59
def prefixEnd_304785 : Nat := 4983230072969 + 3 ^ 40 * 304785 * 2
def baseEnd_304785 : Nat := 52167067093565086995275

theorem tailTrace_304785 : CollatzResearch.WordTrace tailWord_304785 prefixEnd_304785 52167067093565086995275 := by
  unfold tailWord_304785
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116422200823472978947809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7410948133882315319298539 11116422200823472978947809)
  ·
    refine ⟨8337316650617604734210857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11116422200823472978947809 8337316650617604734210857)
    ·
      refine ⟨6252987487963203550658143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8337316650617604734210857 6252987487963203550658143)
      ·
        refine ⟨9379481231944805325987215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6252987487963203550658143 9379481231944805325987215)
        ·
          refine ⟨14069221847917207988980823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9379481231944805325987215 14069221847917207988980823)
          ·
            refine ⟨21103832771875811983471235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14069221847917207988980823 21103832771875811983471235)
            ·
              refine ⟨31655749157813717975206853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21103832771875811983471235 31655749157813717975206853)
              ·
                refine ⟨5935452967090072120351285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31655749157813717975206853 5935452967090072120351285)
                ·
                  refine ⟨556448715664694261282933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5935452967090072120351285 556448715664694261282933)
                  ·
                    refine ⟨52167067093565086995275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 556448715664694261282933 52167067093565086995275)
                    ·
                      rfl

theorem cell23_304785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_304785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304785 prefixEnd_304785 := by exact prefixLift 304785
  have htrace : WordTrace (prefixWord ++ tailWord_304785) baseStart_304785 baseEnd_304785 := by
    simpa [prefixWord, tailWord_304785, baseEnd_304785] using wordTrace_append hprefix tailTrace_304785
  have hstable : (prefixWord ++ tailWord_304785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304785).length < 2 ^ (prefixWord ++ tailWord_304785).sum := by decide
  have hdescent : baseEnd_304785 < baseStart_304785 := by decide
  rcases family_descends (prefixWord ++ tailWord_304785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304832 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 6, 4]
def baseStart_304832 : Nat := 118140960795 + 304832 * 2 ^ 59
def prefixEnd_304832 : Nat := 4983230072969 + 3 ^ 40 * 304832 * 2
def baseEnd_304832 : Nat := 52175111623818859032703

theorem tailTrace_304832 : CollatzResearch.WordTrace tailWord_304832 prefixEnd_304832 52175111623818859032703 := by
  unfold tailWord_304832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559068215826600002954375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7412090954435466670605833 5559068215826600002954375)
  ·
    refine ⟨8338602323739900004431563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5559068215826600002954375 8338602323739900004431563)
    ·
      refine ⟨12507903485609850006647345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8338602323739900004431563 12507903485609850006647345)
      ·
        refine ⟨9380927614207387504985509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12507903485609850006647345 9380927614207387504985509)
        ·
          refine ⟨1758923927663885157184783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9380927614207387504985509 1758923927663885157184783)
          ·
            refine ⟨2638385891495827735777175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758923927663885157184783 2638385891495827735777175)
            ·
              refine ⟨3957578837243741603665763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638385891495827735777175 3957578837243741603665763)
              ·
                refine ⟨5936368255865612405498645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957578837243741603665763 5936368255865612405498645)
                ·
                  refine ⟨278267261993700581507749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5936368255865612405498645 278267261993700581507749)
                  ·
                    refine ⟨52175111623818859032703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278267261993700581507749 52175111623818859032703)
                    ·
                      rfl

theorem cell23_304832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_304832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304832 prefixEnd_304832 := by exact prefixLift 304832
  have htrace : WordTrace (prefixWord ++ tailWord_304832) baseStart_304832 baseEnd_304832 := by
    simpa [prefixWord, tailWord_304832, baseEnd_304832] using wordTrace_append hprefix tailTrace_304832
  have hstable : (prefixWord ++ tailWord_304832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304832).length < 2 ^ (prefixWord ++ tailWord_304832).sum := by decide
  have hdescent : baseEnd_304832 < baseStart_304832 := by decide
  rcases family_descends (prefixWord ++ tailWord_304832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304850 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_304850 : Nat := 118140960795 + 304850 * 2 ^ 59
def prefixEnd_304850 : Nat := 4983230072969 + 3 ^ 40 * 304850 * 2
def baseEnd_304850 : Nat := 156534577523237506673027

theorem tailTrace_304850 : CollatzResearch.WordTrace tailWord_304850 prefixEnd_304850 156534577523237506673027 := by
  unfold tailWord_304850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779698236396997270016001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7412528630391992720042669 2779698236396997270016001)
  ·
    refine ⟨2084773677297747952512001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2779698236396997270016001 2084773677297747952512001)
    ·
      refine ⟨1563580257973310964384001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2084773677297747952512001 1563580257973310964384001)
      ·
        refine ⟨1172685193479983223288001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1563580257973310964384001 1172685193479983223288001)
        ·
          refine ⟨879513895109987417466001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172685193479983223288001 879513895109987417466001)
          ·
            refine ⟨659635421332490563099501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879513895109987417466001 659635421332490563099501)
            ·
              refine ⟨247363282999683961162313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 659635421332490563099501 247363282999683961162313)
              ·
                refine ⟨185522462249762970871735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247363282999683961162313 185522462249762970871735)
                ·
                  refine ⟨278283693374644456307603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185522462249762970871735 278283693374644456307603)
                  ·
                    refine ⟨417425540061966684461405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 278283693374644456307603 417425540061966684461405)
                    ·
                      refine ⟨156534577523237506673027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417425540061966684461405 156534577523237506673027)
                      ·
                        rfl

theorem cell23_304850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_304850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304850 prefixEnd_304850 := by exact prefixLift 304850
  have htrace : WordTrace (prefixWord ++ tailWord_304850) baseStart_304850 baseEnd_304850 := by
    simpa [prefixWord, tailWord_304850, baseEnd_304850] using wordTrace_append hprefix tailTrace_304850
  have hstable : (prefixWord ++ tailWord_304850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304850).length < 2 ^ (prefixWord ++ tailWord_304850).sum := by decide
  have hdescent : baseEnd_304850 < baseStart_304850 := by decide
  rcases family_descends (prefixWord ++ tailWord_304850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304906 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_304906 : Nat := 118140960795 + 304906 * 2 ^ 59
def prefixEnd_304906 : Nat := 4983230072969 + 3 ^ 40 * 304906 * 2
def baseEnd_304906 : Nat := 156563332439889287572769

theorem tailTrace_304906 : CollatzResearch.WordTrace tailWord_304906 prefixEnd_304906 156563332439889287572769 := by
  unfold tailWord_304906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780208858346277661025643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7413890288923407096068381 2780208858346277661025643)
  ·
    refine ⟨4170313287519416491538465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2780208858346277661025643 4170313287519416491538465)
    ·
      refine ⟨3127734965639562368653849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4170313287519416491538465 3127734965639562368653849)
      ·
        refine ⟨2345801224229671776490387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3127734965639562368653849 2345801224229671776490387)
        ·
          refine ⟨3518701836344507664735581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345801224229671776490387 3518701836344507664735581)
          ·
            refine ⟨1319513188629190374275843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3518701836344507664735581 1319513188629190374275843)
            ·
              refine ⟨1979269782943785561413765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319513188629190374275843 1979269782943785561413765)
              ·
                refine ⟨371113084301959792765081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1979269782943785561413765 371113084301959792765081)
                ·
                  refine ⟨278334813226469844573811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371113084301959792765081 278334813226469844573811)
                  ·
                    refine ⟨417502219839704766860717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 278334813226469844573811 417502219839704766860717)
                    ·
                      refine ⟨156563332439889287572769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417502219839704766860717 156563332439889287572769)
                      ·
                        rfl

theorem cell23_304906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_304906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304906 prefixEnd_304906 := by exact prefixLift 304906
  have htrace : WordTrace (prefixWord ++ tailWord_304906) baseStart_304906 baseEnd_304906 := by
    simpa [prefixWord, tailWord_304906, baseEnd_304906] using wordTrace_append hprefix tailTrace_304906
  have hstable : (prefixWord ++ tailWord_304906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304906).length < 2 ^ (prefixWord ++ tailWord_304906).sum := by decide
  have hdescent : baseEnd_304906 < baseStart_304906 := by decide
  rcases family_descends (prefixWord ++ tailWord_304906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304922 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_304922 : Nat := 118140960795 + 304922 * 2 ^ 59
def prefixEnd_304922 : Nat := 4983230072969 + 3 ^ 40 * 304922 * 2
def baseEnd_304922 : Nat := 52190516043453741657565

theorem tailTrace_304922 : CollatzResearch.WordTrace tailWord_304922 prefixEnd_304922 52190516043453741657565 := by
  unfold tailWord_304922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780354750331786344171255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7414279334218096917790013 2780354750331786344171255)
  ·
    refine ⟨4170532125497679516256883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2780354750331786344171255 4170532125497679516256883)
    ·
      refine ⟨6255798188246519274385325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170532125497679516256883 6255798188246519274385325)
      ·
        refine ⟨2345924320592444727894497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6255798188246519274385325 2345924320592444727894497)
        ·
          refine ⟨1759443240444333545920873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2345924320592444727894497 1759443240444333545920873)
          ·
            refine ⟨1319582430333250159440655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759443240444333545920873 1319582430333250159440655)
            ·
              refine ⟨1979373645499875239160983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319582430333250159440655 1979373645499875239160983)
              ·
                refine ⟨2969060468249812858741475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979373645499875239160983 2969060468249812858741475)
                ·
                  refine ⟨4453590702374719288112213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969060468249812858741475 4453590702374719288112213)
                  ·
                    refine ⟨52190516043453741657565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4453590702374719288112213 52190516043453741657565)
                    ·
                      rfl

theorem cell23_304922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_304922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304922 prefixEnd_304922 := by exact prefixLift 304922
  have htrace : WordTrace (prefixWord ++ tailWord_304922) baseStart_304922 baseEnd_304922 := by
    simpa [prefixWord, tailWord_304922, baseEnd_304922] using wordTrace_append hprefix tailTrace_304922
  have hstable : (prefixWord ++ tailWord_304922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304922).length < 2 ^ (prefixWord ++ tailWord_304922).sum := by decide
  have hdescent : baseEnd_304922 < baseStart_304922 := by decide
  rcases family_descends (prefixWord ++ tailWord_304922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304946 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_304946 : Nat := 118140960795 + 304946 * 2 ^ 59
def prefixEnd_304946 : Nat := 4983230072969 + 3 ^ 40 * 304946 * 2
def baseEnd_304946 : Nat := 156583871666069131072585

theorem tailTrace_304946 : CollatzResearch.WordTrace tailWord_304946 prefixEnd_304946 156583871666069131072585 := by
  unfold tailWord_304946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780573588310049368889673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7414862902160131650372461 2780573588310049368889673)
  ·
    refine ⟨2085430191232537026667255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2780573588310049368889673 2085430191232537026667255)
    ·
      refine ⟨3128145286848805540000883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085430191232537026667255 3128145286848805540000883)
      ·
        refine ⟨4692217930273208310001325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128145286848805540000883 4692217930273208310001325)
        ·
          refine ⟨1759581723852453116250497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4692217930273208310001325 1759581723852453116250497)
          ·
            refine ⟨1319686292889339837187873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759581723852453116250497 1319686292889339837187873)
            ·
              refine ⟨989764719667004877890905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319686292889339837187873 989764719667004877890905)
              ·
                refine ⟨742323539750253658418179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989764719667004877890905 742323539750253658418179)
                ·
                  refine ⟨1113485309625380487627269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742323539750253658418179 1113485309625380487627269)
                  ·
                    refine ⟨208778495554758841430113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1113485309625380487627269 208778495554758841430113)
                    ·
                      refine ⟨156583871666069131072585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208778495554758841430113 156583871666069131072585)
                      ·
                        rfl

theorem cell23_304946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_304946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304946 prefixEnd_304946 := by exact prefixLift 304946
  have htrace : WordTrace (prefixWord ++ tailWord_304946) baseStart_304946 baseEnd_304946 := by
    simpa [prefixWord, tailWord_304946, baseEnd_304946] using wordTrace_append hprefix tailTrace_304946
  have hstable : (prefixWord ++ tailWord_304946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304946).length < 2 ^ (prefixWord ++ tailWord_304946).sum := by decide
  have hdescent : baseEnd_304946 < baseStart_304946 := by decide
  rcases family_descends (prefixWord ++ tailWord_304946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304950 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_304950 : Nat := 118140960795 + 304950 * 2 ^ 59
def prefixEnd_304950 : Nat := 4983230072969 + 3 ^ 40 * 304950 * 2
def baseEnd_304950 : Nat := 156585925588687115422567

theorem tailTrace_304950 : CollatzResearch.WordTrace tailWord_304950 prefixEnd_304950 156585925588687115422567 := by
  unfold tailWord_304950
  simp only [CollatzResearch.WordTrace]
  refine ⟨695152515326606634919019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7414960163483804105802869 695152515326606634919019)
  ·
    refine ⟨1042728772989909952378529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 695152515326606634919019 1042728772989909952378529)
    ·
      refine ⟨782046579742432464283897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1042728772989909952378529 782046579742432464283897)
      ·
        refine ⟨586534934806824348212923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782046579742432464283897 586534934806824348212923)
        ·
          refine ⟨879802402210236522319385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586534934806824348212923 879802402210236522319385)
          ·
            refine ⟨659851801657677391739539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879802402210236522319385 659851801657677391739539)
            ·
              refine ⟨989777702486516087609309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659851801657677391739539 989777702486516087609309)
              ·
                refine ⟨371166638432443532853491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989777702486516087609309 371166638432443532853491)
                ·
                  refine ⟨556749957648665299280237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371166638432443532853491 556749957648665299280237)
                  ·
                    refine ⟨208781234118249487230089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556749957648665299280237 208781234118249487230089)
                    ·
                      refine ⟨156585925588687115422567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208781234118249487230089 156585925588687115422567)
                      ·
                        rfl

theorem cell23_304950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_304950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304950 prefixEnd_304950 := by exact prefixLift 304950
  have htrace : WordTrace (prefixWord ++ tailWord_304950) baseStart_304950 baseEnd_304950 := by
    simpa [prefixWord, tailWord_304950, baseEnd_304950] using wordTrace_append hprefix tailTrace_304950
  have hstable : (prefixWord ++ tailWord_304950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304950).length < 2 ^ (prefixWord ++ tailWord_304950).sum := by decide
  have hdescent : baseEnd_304950 < baseStart_304950 := by decide
  rcases family_descends (prefixWord ++ tailWord_304950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304963 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 2, 2, 2]
def baseStart_304963 : Nat := 118140960795 + 304963 * 2 ^ 59
def prefixEnd_304963 : Nat := 4983230072969 + 3 ^ 40 * 304963 * 2
def baseEnd_304963 : Nat := 156592600837195564560007

theorem tailTrace_304963 : CollatzResearch.WordTrace tailWord_304963 prefixEnd_304963 156592600837195564560007 := by
  unfold tailWord_304963
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122914394178609378927543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7415276262785739585951695 11122914394178609378927543)
  ·
    refine ⟨16684371591267914068391315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11122914394178609378927543 16684371591267914068391315)
    ·
      refine ⟨25026557386901871102586973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16684371591267914068391315 25026557386901871102586973)
      ·
        refine ⟨9384959020088201663470115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25026557386901871102586973 9384959020088201663470115)
        ·
          refine ⟨14077438530132302495205173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9384959020088201663470115 14077438530132302495205173)
          ·
            refine ⟨1319759862199903358925485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14077438530132302495205173 1319759862199903358925485)
            ·
              refine ⟨494909948324963759597057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1319759862199903358925485 494909948324963759597057)
              ·
                refine ⟨371182461243722819697793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494909948324963759597057 371182461243722819697793)
                ·
                  refine ⟨278386845932792114773345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371182461243722819697793 278386845932792114773345)
                  ·
                    refine ⟨208790134449594086080009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 278386845932792114773345 208790134449594086080009)
                    ·
                      refine ⟨156592600837195564560007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208790134449594086080009 156592600837195564560007)
                      ·
                        rfl

theorem cell23_304963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_304963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304963 prefixEnd_304963 := by exact prefixLift 304963
  have htrace : WordTrace (prefixWord ++ tailWord_304963) baseStart_304963 baseEnd_304963 := by
    simpa [prefixWord, tailWord_304963, baseEnd_304963] using wordTrace_append hprefix tailTrace_304963
  have hstable : (prefixWord ++ tailWord_304963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304963).length < 2 ^ (prefixWord ++ tailWord_304963).sum := by decide
  have hdescent : baseEnd_304963 < baseStart_304963 := by decide
  rcases family_descends (prefixWord ++ tailWord_304963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304969 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 5]
def baseStart_304969 : Nat := 118140960795 + 304969 * 2 ^ 59
def prefixEnd_304969 : Nat := 4983230072969 + 3 ^ 40 * 304969 * 2
def baseEnd_304969 : Nat := 17399520191235837898331

theorem tailTrace_304969 : CollatzResearch.WordTrace tailWord_304969 prefixEnd_304969 17399520191235837898331 := by
  unfold tailWord_304969
  simp only [CollatzResearch.WordTrace]
  refine ⟨11123133232156872403645961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7415422154771248269097307 11123133232156872403645961)
  ·
    refine ⟨8342349924117654302734471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11123133232156872403645961 8342349924117654302734471)
    ·
      refine ⟨12513524886176481454101707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8342349924117654302734471 12513524886176481454101707)
      ·
        refine ⟨18770287329264722181152561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513524886176481454101707 18770287329264722181152561)
        ·
          refine ⟨14077715496948541635864421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18770287329264722181152561 14077715496948541635864421)
          ·
            refine ⟨2639571655677851556724579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14077715496948541635864421 2639571655677851556724579)
            ·
              refine ⟨3959357483516777335086869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639571655677851556724579 3959357483516777335086869)
              ·
                refine ⟨185594882039848937582197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3959357483516777335086869 185594882039848937582197)
                ·
                  refine ⟨17399520191235837898331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185594882039848937582197 17399520191235837898331)
                  ·
                    rfl

theorem cell23_304969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 5].length) (baseStart_304969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304969 prefixEnd_304969 := by exact prefixLift 304969
  have htrace : WordTrace (prefixWord ++ tailWord_304969) baseStart_304969 baseEnd_304969 := by
    simpa [prefixWord, tailWord_304969, baseEnd_304969] using wordTrace_append hprefix tailTrace_304969
  have hstable : (prefixWord ++ tailWord_304969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304969).length < 2 ^ (prefixWord ++ tailWord_304969).sum := by decide
  have hdescent : baseEnd_304969 < baseStart_304969 := by decide
  rcases family_descends (prefixWord ++ tailWord_304969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304999 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 2, 5]
def baseStart_304999 : Nat := 118140960795 + 304999 * 2 ^ 59
def prefixEnd_304999 : Nat := 4983230072969 + 3 ^ 40 * 304999 * 2
def baseEnd_304999 : Nat := 52203695380252474569947

theorem tailTrace_304999 : CollatzResearch.WordTrace tailWord_304999 prefixEnd_304999 52203695380252474569947 := by
  unfold tailWord_304999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124227422048187527238051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7416151614698791684825367 11124227422048187527238051)
  ·
    refine ⟨16686341133072281290857077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11124227422048187527238051 16686341133072281290857077)
    ·
      refine ⟨1564344481225526371017851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16686341133072281290857077 1564344481225526371017851)
      ·
        refine ⟨2346516721838289556526777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564344481225526371017851 2346516721838289556526777)
        ·
          refine ⟨1759887541378717167395083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346516721838289556526777 1759887541378717167395083)
          ·
            refine ⟨2639831312068075751092625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759887541378717167395083 2639831312068075751092625)
            ·
              refine ⟨1979873484051056813319469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639831312068075751092625 1979873484051056813319469)
              ·
                refine ⟨742452556519146304994801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1979873484051056813319469 742452556519146304994801)
                ·
                  refine ⟨556839417389359728746101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 742452556519146304994801 556839417389359728746101)
                  ·
                    refine ⟨52203695380252474569947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 556839417389359728746101 52203695380252474569947)
                    ·
                      rfl

theorem cell23_304999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_304999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_304999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_304999 prefixEnd_304999 := by exact prefixLift 304999
  have htrace : WordTrace (prefixWord ++ tailWord_304999) baseStart_304999 baseEnd_304999 := by
    simpa [prefixWord, tailWord_304999, baseEnd_304999] using wordTrace_append hprefix tailTrace_304999
  have hstable : (prefixWord ++ tailWord_304999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304999).length < 2 ^ (prefixWord ++ tailWord_304999).sum := by decide
  have hdescent : baseEnd_304999 < baseStart_304999 := by decide
  rcases family_descends (prefixWord ++ tailWord_304999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305113 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 1, 5, 2]
def baseStart_305113 : Nat := 118140960795 + 305113 * 2 ^ 59
def prefixEnd_305113 : Nat := 4983230072969 + 3 ^ 40 * 305113 * 2
def baseEnd_305113 : Nat := 156669622935369977684317

theorem tailTrace_305113 : CollatzResearch.WordTrace tailWord_305113 prefixEnd_305113 156669622935369977684317 := by
  unfold tailWord_305113
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128385343635184996887993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7418923562423456664591995 11128385343635184996887993)
  ·
    refine ⟨8346289007726388747665995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11128385343635184996887993 8346289007726388747665995)
    ·
      refine ⟨12519433511589583121498993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346289007726388747665995 12519433511589583121498993)
      ·
        refine ⟨9389575133692187341124245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12519433511589583121498993 9389575133692187341124245)
        ·
          refine ⟨440136334391821281615199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9389575133692187341124245 440136334391821281615199)
          ·
            refine ⟨660204501587731922422799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440136334391821281615199 660204501587731922422799)
            ·
              refine ⟨990306752381597883634199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660204501587731922422799 990306752381597883634199)
              ·
                refine ⟨1485460128572396825451299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990306752381597883634199 1485460128572396825451299)
                ·
                  refine ⟨2228190192858595238176949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485460128572396825451299 2228190192858595238176949)
                  ·
                    refine ⟨208892830580493303579089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2228190192858595238176949 208892830580493303579089)
                    ·
                      refine ⟨156669622935369977684317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208892830580493303579089 156669622935369977684317)
                      ·
                        rfl

theorem cell23_305113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_305113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305113 prefixEnd_305113 := by exact prefixLift 305113
  have htrace : WordTrace (prefixWord ++ tailWord_305113) baseStart_305113 baseEnd_305113 := by
    simpa [prefixWord, tailWord_305113, baseEnd_305113] using wordTrace_append hprefix tailTrace_305113
  have hstable : (prefixWord ++ tailWord_305113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305113).length < 2 ^ (prefixWord ++ tailWord_305113).sum := by decide
  have hdescent : baseEnd_305113 < baseStart_305113 := by decide
  rcases family_descends (prefixWord ++ tailWord_305113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305123 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 1, 5]
def baseStart_305123 : Nat := 118140960795 + 305123 * 2 ^ 59
def prefixEnd_305123 : Nat := 4983230072969 + 3 ^ 40 * 305123 * 2
def baseEnd_305123 : Nat := 52224919247304979519757

theorem tailTrace_305123 : CollatzResearch.WordTrace tailWord_305123 prefixEnd_305123 52224919247304979519757 := by
  unfold tailWord_305123
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128750073598956704752023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7419166715732637803168015 11128750073598956704752023)
  ·
    refine ⟨16693125110398435057128035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128750073598956704752023 16693125110398435057128035)
    ·
      refine ⟨25039687665597652585692053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16693125110398435057128035 25039687665597652585692053)
      ·
        refine ⟨1173735359324889964954315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25039687665597652585692053 1173735359324889964954315)
        ·
          refine ⟨1760603038987334947431473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173735359324889964954315 1760603038987334947431473)
          ·
            refine ⟨1320452279240501210573605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760603038987334947431473 1320452279240501210573605)
            ·
              refine ⟨247584802357593976982551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1320452279240501210573605 247584802357593976982551)
              ·
                refine ⟨371377203536390965473827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247584802357593976982551 371377203536390965473827)
                ·
                  refine ⟨557065805304586448210741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371377203536390965473827 557065805304586448210741)
                  ·
                    refine ⟨52224919247304979519757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 557065805304586448210741 52224919247304979519757)
                    ·
                      rfl

theorem cell23_305123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 5].length) (baseStart_305123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305123 prefixEnd_305123 := by exact prefixLift 305123
  have htrace : WordTrace (prefixWord ++ tailWord_305123) baseStart_305123 baseEnd_305123 := by
    simpa [prefixWord, tailWord_305123, baseEnd_305123] using wordTrace_append hprefix tailTrace_305123
  have hstable : (prefixWord ++ tailWord_305123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305123).length < 2 ^ (prefixWord ++ tailWord_305123).sum := by decide
  have hdescent : baseEnd_305123 < baseStart_305123 := by decide
  rcases family_descends (prefixWord ++ tailWord_305123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305139 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4]
def baseStart_305139 : Nat := 118140960795 + 305139 * 2 ^ 59
def prefixEnd_305139 : Nat := 4983230072969 + 3 ^ 40 * 305139 * 2
def baseEnd_305139 : Nat := 156682973432386875959197

theorem tailTrace_305139 : CollatzResearch.WordTrace tailWord_305139 prefixEnd_305139 156682973432386875959197 := by
  unfold tailWord_305139
  simp only [CollatzResearch.WordTrace]
  refine ⟨11129333641540991437334471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7419555761027327624889647 11129333641540991437334471)
  ·
    refine ⟨16694000462311487156001707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11129333641540991437334471 16694000462311487156001707)
    ·
      refine ⟨25041000693467230734002561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16694000462311487156001707 25041000693467230734002561)
      ·
        refine ⟨18780750520100423050501921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25041000693467230734002561 18780750520100423050501921)
        ·
          refine ⟨14085562890075317287876441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18780750520100423050501921 14085562890075317287876441)
          ·
            refine ⟨10564172167556487965907331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14085562890075317287876441 10564172167556487965907331)
            ·
              refine ⟨15846258251334731948860997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10564172167556487965907331 15846258251334731948860997)
              ·
                refine ⟨2971173422125262240411437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15846258251334731948860997 2971173422125262240411437)
                ·
                  refine ⟨1114190033296973340154289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2971173422125262240411437 1114190033296973340154289)
                  ·
                    refine ⟨835642524972730005115717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1114190033296973340154289 835642524972730005115717)
                    ·
                      refine ⟨156682973432386875959197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 835642524972730005115717 156682973432386875959197)
                      ·
                        rfl

theorem cell23_305139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_305139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305139 prefixEnd_305139 := by exact prefixLift 305139
  have htrace : WordTrace (prefixWord ++ tailWord_305139) baseStart_305139 baseEnd_305139 := by
    simpa [prefixWord, tailWord_305139, baseEnd_305139] using wordTrace_append hprefix tailTrace_305139
  have hstable : (prefixWord ++ tailWord_305139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305139).length < 2 ^ (prefixWord ++ tailWord_305139).sum := by decide
  have hdescent : baseEnd_305139 < baseStart_305139 := by decide
  rcases family_descends (prefixWord ++ tailWord_305139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305163 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 3]
def baseStart_305163 : Nat := 118140960795 + 305163 * 2 ^ 59
def prefixEnd_305163 : Nat := 4983230072969 + 3 ^ 40 * 305163 * 2
def baseEnd_305163 : Nat := 156695296968094782059087

theorem tailTrace_305163 : CollatzResearch.WordTrace tailWord_305163 prefixEnd_305163 156695296968094782059087 := by
  unfold tailWord_305163
  simp only [CollatzResearch.WordTrace]
  refine ⟨11130208993454043536208143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7420139328969362357472095 11130208993454043536208143)
  ·
    refine ⟨16695313490181065304312215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11130208993454043536208143 16695313490181065304312215)
    ·
      refine ⟨25042970235271597956468323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16695313490181065304312215 25042970235271597956468323)
      ·
        refine ⟨37564455352907396934702485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25042970235271597956468323 37564455352907396934702485)
        ·
          refine ⟨1760833844667534231314179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37564455352907396934702485 1760833844667534231314179)
          ·
            refine ⟨2641250767001301346971269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760833844667534231314179 2641250767001301346971269)
            ·
              refine ⟨495234518812744002557113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2641250767001301346971269 495234518812744002557113)
              ·
                refine ⟨371425889109558001917835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495234518812744002557113 371425889109558001917835)
                ·
                  refine ⟨557138833664337002876753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371425889109558001917835 557138833664337002876753)
                  ·
                    refine ⟨417854125248252752157565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 557138833664337002876753 417854125248252752157565)
                    ·
                      refine ⟨156695296968094782059087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417854125248252752157565 156695296968094782059087)
                      ·
                        rfl

theorem cell23_305163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 3].length) (baseStart_305163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305163 prefixEnd_305163 := by exact prefixLift 305163
  have htrace : WordTrace (prefixWord ++ tailWord_305163) baseStart_305163 baseEnd_305163 := by
    simpa [prefixWord, tailWord_305163, baseEnd_305163] using wordTrace_append hprefix tailTrace_305163
  have hstable : (prefixWord ++ tailWord_305163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305163).length < 2 ^ (prefixWord ++ tailWord_305163).sum := by decide
  have hdescent : baseEnd_305163 < baseStart_305163 := by decide
  rcases family_descends (prefixWord ++ tailWord_305163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305176 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_305176 : Nat := 118140960795 + 305176 * 2 ^ 59
def prefixEnd_305176 : Nat := 4983230072969 + 3 ^ 40 * 305176 * 2
def baseEnd_305176 : Nat := 156701972216603231196527

theorem tailTrace_305176 : CollatzResearch.WordTrace tailWord_305176 prefixEnd_305176 156701972216603231196527 := by
  unfold tailWord_305176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565341571203473378215691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7420455428271297837620921 5565341571203473378215691)
  ·
    refine ⟨8348012356805210067323537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5565341571203473378215691 8348012356805210067323537)
    ·
      refine ⟨6261009267603907550492653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8348012356805210067323537 6261009267603907550492653)
      ·
        refine ⟨2347878475351465331434745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6261009267603907550492653 2347878475351465331434745)
        ·
          refine ⟨1760908856513598998576059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2347878475351465331434745 1760908856513598998576059)
          ·
            refine ⟨2641363284770398497864089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760908856513598998576059 2641363284770398497864089)
            ·
              refine ⟨1981022463577798873398067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2641363284770398497864089 1981022463577798873398067)
              ·
                refine ⟨2971533695366698310097101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981022463577798873398067 2971533695366698310097101)
                ·
                  refine ⟨1114325135762511866286413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2971533695366698310097101 1114325135762511866286413)
                  ·
                    refine ⟨417871925910941949857405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114325135762511866286413 417871925910941949857405)
                    ·
                      refine ⟨156701972216603231196527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417871925910941949857405 156701972216603231196527)
                      ·
                        rfl

theorem cell23_305176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_305176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305176 prefixEnd_305176 := by exact prefixLift 305176
  have htrace : WordTrace (prefixWord ++ tailWord_305176) baseStart_305176 baseEnd_305176 := by
    simpa [prefixWord, tailWord_305176, baseEnd_305176] using wordTrace_append hprefix tailTrace_305176
  have hstable : (prefixWord ++ tailWord_305176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305176).length < 2 ^ (prefixWord ++ tailWord_305176).sum := by decide
  have hdescent : baseEnd_305176 < baseStart_305176 := by decide
  rcases family_descends (prefixWord ++ tailWord_305176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305204 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_305204 : Nat := 118140960795 + 305204 * 2 ^ 59
def prefixEnd_305204 : Nat := 4983230072969 + 3 ^ 40 * 305204 * 2
def baseEnd_305204 : Nat := 52238783224976373882133

theorem tailTrace_305204 : CollatzResearch.WordTrace tailWord_305204 prefixEnd_305204 52238783224976373882133 := by
  unfold tailWord_305204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565852193152753769225333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7421136257537005025633777 5565852193152753769225333)
  ·
    refine ⟨521798643108070665864875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5565852193152753769225333 521798643108070665864875)
    ·
      refine ⟨782697964662105998797313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521798643108070665864875 782697964662105998797313)
      ·
        refine ⟨587023473496579499097985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782697964662105998797313 587023473496579499097985)
        ·
          refine ⟨440267605122434624323489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587023473496579499097985 440267605122434624323489)
          ·
            refine ⟨330200703841825968242617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440267605122434624323489 330200703841825968242617)
            ·
              refine ⟨247650527881369476181963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330200703841825968242617 247650527881369476181963)
              ·
                refine ⟨371475791822054214272945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247650527881369476181963 371475791822054214272945)
                ·
                  refine ⟨278606843866540660704709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371475791822054214272945 278606843866540660704709)
                  ·
                    refine ⟨52238783224976373882133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278606843866540660704709 52238783224976373882133)
                    ·
                      rfl

theorem cell23_305204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_305204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305204 prefixEnd_305204 := by exact prefixLift 305204
  have htrace : WordTrace (prefixWord ++ tailWord_305204) baseStart_305204 baseEnd_305204 := by
    simpa [prefixWord, tailWord_305204, baseEnd_305204] using wordTrace_append hprefix tailTrace_305204
  have hstable : (prefixWord ++ tailWord_305204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305204).length < 2 ^ (prefixWord ++ tailWord_305204).sum := by decide
  have hdescent : baseEnd_305204 < baseStart_305204 := by decide
  rcases family_descends (prefixWord ++ tailWord_305204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305214 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_305214 : Nat := 118140960795 + 305214 * 2 ^ 59
def prefixEnd_305214 : Nat := 4983230072969 + 3 ^ 40 * 305214 * 2
def baseEnd_305214 : Nat := 156721484481474082521353

theorem tailTrace_305214 : CollatzResearch.WordTrace tailWord_305214 prefixEnd_305214 156721484481474082521353 := by
  unfold tailWord_305214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391508639533659905789337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7421379410846186164209797 1391508639533659905789337)
  ·
    refine ⟨1043631479650244929342003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1391508639533659905789337 1043631479650244929342003)
    ·
      refine ⟨1565447219475367394013005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043631479650244929342003 1565447219475367394013005)
      ·
        refine ⟨587042707303262772754877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1565447219475367394013005 587042707303262772754877)
        ·
          refine ⟨220141015238723539783079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 587042707303262772754877 220141015238723539783079)
          ·
            refine ⟨330211522858085309674619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220141015238723539783079 330211522858085309674619)
            ·
              refine ⟨495317284287127964511929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330211522858085309674619 495317284287127964511929)
              ·
                refine ⟨371487963215345973383947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495317284287127964511929 371487963215345973383947)
                ·
                  refine ⟨557231944823018960075921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371487963215345973383947 557231944823018960075921)
                  ·
                    refine ⟨417923958617264220056941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 557231944823018960075921 417923958617264220056941)
                    ·
                      refine ⟨156721484481474082521353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 417923958617264220056941 156721484481474082521353)
                      ·
                        rfl

theorem cell23_305214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_305214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305214 prefixEnd_305214 := by exact prefixLift 305214
  have htrace : WordTrace (prefixWord ++ tailWord_305214) baseStart_305214 baseEnd_305214 := by
    simpa [prefixWord, tailWord_305214, baseEnd_305214] using wordTrace_append hprefix tailTrace_305214
  have hstable : (prefixWord ++ tailWord_305214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305214).length < 2 ^ (prefixWord ++ tailWord_305214).sum := by decide
  have hdescent : baseEnd_305214 < baseStart_305214 := by decide
  rcases family_descends (prefixWord ++ tailWord_305214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305237 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_305237 : Nat := 118140960795 + 305237 * 2 ^ 59
def prefixEnd_305237 : Nat := 4983230072969 + 3 ^ 40 * 305237 * 2
def baseEnd_305237 : Nat := 156733294536527492533747

theorem tailTrace_305237 : CollatzResearch.WordTrace tailWord_305237 prefixEnd_305237 156733294536527492533747 := by
  unfold tailWord_305237
  simp only [CollatzResearch.WordTrace]
  refine ⟨11132907995185954174401965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7421938663457302782934643 11132907995185954174401965)
  ·
    refine ⟨4174840498194732815400737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11132907995185954174401965 4174840498194732815400737)
    ·
      refine ⟨3131130373646049611550553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4174840498194732815400737 3131130373646049611550553)
      ·
        refine ⟨2348347780234537208662915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3131130373646049611550553 2348347780234537208662915)
        ·
          refine ⟨3522521670351805812994373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348347780234537208662915 3522521670351805812994373)
          ·
            refine ⟨660472813190963589936445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3522521670351805812994373 660472813190963589936445)
            ·
              refine ⟨247677304946611346226167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660472813190963589936445 247677304946611346226167)
              ·
                refine ⟨371515957419917019339251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247677304946611346226167 371515957419917019339251)
                ·
                  refine ⟨557273936129875529008877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371515957419917019339251 557273936129875529008877)
                  ·
                    refine ⟨208977726048703323378329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557273936129875529008877 208977726048703323378329)
                    ·
                      refine ⟨156733294536527492533747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 208977726048703323378329 156733294536527492533747)
                      ·
                        rfl

theorem cell23_305237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_305237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305237 prefixEnd_305237 := by exact prefixLift 305237
  have htrace : WordTrace (prefixWord ++ tailWord_305237) baseStart_305237 baseEnd_305237 := by
    simpa [prefixWord, tailWord_305237, baseEnd_305237] using wordTrace_append hprefix tailTrace_305237
  have hstable : (prefixWord ++ tailWord_305237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305237).length < 2 ^ (prefixWord ++ tailWord_305237).sum := by decide
  have hdescent : baseEnd_305237 < baseStart_305237 := by decide
  rcases family_descends (prefixWord ++ tailWord_305237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305290 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_305290 : Nat := 118140960795 + 305290 * 2 ^ 59
def prefixEnd_305290 : Nat := 4983230072969 + 3 ^ 40 * 305290 * 2
def baseEnd_305290 : Nat := 17417834334579531685667

theorem tailTrace_305290 : CollatzResearch.WordTrace tailWord_305290 prefixEnd_305290 17417834334579531685667 := by
  unfold tailWord_305290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783710265998486056520331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7423227375995962817387549 2783710265998486056520331)
  ·
    refine ⟨4175565398997729084780497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783710265998486056520331 4175565398997729084780497)
    ·
      refine ⟨3131674049248296813585373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4175565398997729084780497 3131674049248296813585373)
      ·
        refine ⟨1174377768468111305094515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3131674049248296813585373 1174377768468111305094515)
        ·
          refine ⟨1761566652702166957641773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174377768468111305094515 1761566652702166957641773)
          ·
            refine ⟨660587494763312609115665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1761566652702166957641773 660587494763312609115665)
            ·
              refine ⟨495440621072484456836749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660587494763312609115665 495440621072484456836749)
              ·
                refine ⟨185790232902181671313781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495440621072484456836749 185790232902181671313781)
                ·
                  refine ⟨17417834334579531685667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185790232902181671313781 17417834334579531685667)
                  ·
                    rfl

theorem cell23_305290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_305290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305290 prefixEnd_305290 := by exact prefixLift 305290
  have htrace : WordTrace (prefixWord ++ tailWord_305290) baseStart_305290 baseEnd_305290 := by
    simpa [prefixWord, tailWord_305290, baseEnd_305290] using wordTrace_append hprefix tailTrace_305290
  have hstable : (prefixWord ++ tailWord_305290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305290).length < 2 ^ (prefixWord ++ tailWord_305290).sum := by decide
  have hdescent : baseEnd_305290 < baseStart_305290 := by decide
  rcases family_descends (prefixWord ++ tailWord_305290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305336 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_305336 : Nat := 118140960795 + 305336 * 2 ^ 59
def prefixEnd_305336 : Nat := 4983230072969 + 3 ^ 40 * 305336 * 2
def baseEnd_305336 : Nat := 156784129121322605195791

theorem tailTrace_305336 : CollatzResearch.WordTrace tailWord_305336 prefixEnd_305336 156784129121322605195791 := by
  unfold tailWord_305336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568259410913647041127931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7424345881218196054837241 5568259410913647041127931)
  ·
    refine ⟨8352389116370470561691897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5568259410913647041127931 8352389116370470561691897)
    ·
      refine ⟨6264291837277852921268923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8352389116370470561691897 6264291837277852921268923)
      ·
        refine ⟨9396437755916779381903385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264291837277852921268923 9396437755916779381903385)
        ·
          refine ⟨7047328316937584536427539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9396437755916779381903385 7047328316937584536427539)
          ·
            refine ⟨10570992475406376804641309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047328316937584536427539 10570992475406376804641309)
            ·
              refine ⟨3964122178277391301740491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10570992475406376804641309 3964122178277391301740491)
              ·
                refine ⟨5946183267416086952610737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964122178277391301740491 5946183267416086952610737)
                ·
                  refine ⟨4459637450562065214458053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5946183267416086952610737 4459637450562065214458053)
                  ·
                    refine ⟨836182021980387227710885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459637450562065214458053 836182021980387227710885)
                    ·
                      refine ⟨156784129121322605195791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 836182021980387227710885 156784129121322605195791)
                      ·
                        rfl

theorem cell23_305336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_305336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305336 prefixEnd_305336 := by exact prefixLift 305336
  have htrace : WordTrace (prefixWord ++ tailWord_305336) baseStart_305336 baseEnd_305336 := by
    simpa [prefixWord, tailWord_305336, baseEnd_305336] using wordTrace_append hprefix tailTrace_305336
  have hstable : (prefixWord ++ tailWord_305336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305336).length < 2 ^ (prefixWord ++ tailWord_305336).sum := by decide
  have hdescent : baseEnd_305336 < baseStart_305336 := by decide
  rcases family_descends (prefixWord ++ tailWord_305336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305343 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_305343 : Nat := 118140960795 + 305343 * 2 ^ 59
def prefixEnd_305343 : Nat := 4983230072969 + 3 ^ 40 * 305343 * 2
def baseEnd_305343 : Nat := 156787723485904077808259

theorem tailTrace_305343 : CollatzResearch.WordTrace tailWord_305343 prefixEnd_305343 156787723485904077808259 := by
  unfold tailWord_305343
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136774132801934277760683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7424516088534622851840455 11136774132801934277760683)
  ·
    refine ⟨16705161199202901416641025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11136774132801934277760683 16705161199202901416641025)
    ·
      refine ⟨12528870899402176062480769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16705161199202901416641025 12528870899402176062480769)
      ·
        refine ⟨9396653174551632046860577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12528870899402176062480769 9396653174551632046860577)
        ·
          refine ⟨7047489880913724035145433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9396653174551632046860577 7047489880913724035145433)
          ·
            refine ⟨5285617410685293026359075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7047489880913724035145433 5285617410685293026359075)
            ·
              refine ⟨7928426116027939539538613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285617410685293026359075 7928426116027939539538613)
              ·
                refine ⟨743289948377619331831745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7928426116027939539538613 743289948377619331831745)
                ·
                  refine ⟨557467461283214498873809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 743289948377619331831745 557467461283214498873809)
                  ·
                    refine ⟨418100595962410874155357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 557467461283214498873809 418100595962410874155357)
                    ·
                      refine ⟨156787723485904077808259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418100595962410874155357 156787723485904077808259)
                      ·
                        rfl

theorem cell23_305343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_305343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305343 prefixEnd_305343 := by exact prefixLift 305343
  have htrace : WordTrace (prefixWord ++ tailWord_305343) baseStart_305343 baseEnd_305343 := by
    simpa [prefixWord, tailWord_305343, baseEnd_305343] using wordTrace_append hprefix tailTrace_305343
  have hstable : (prefixWord ++ tailWord_305343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305343).length < 2 ^ (prefixWord ++ tailWord_305343).sum := by decide
  have hdescent : baseEnd_305343 < baseStart_305343 := by decide
  rcases family_descends (prefixWord ++ tailWord_305343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305390 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_305390 : Nat := 118140960795 + 305390 * 2 ^ 59
def prefixEnd_305390 : Nat := 4983230072969 + 3 ^ 40 * 305390 * 2
def baseEnd_305390 : Nat := 156811857076665393920543

theorem tailTrace_305390 : CollatzResearch.WordTrace tailWord_305390 prefixEnd_305390 156811857076665393920543 := by
  unfold tailWord_305390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392311045453957663090203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7425658909087774203147749 1392311045453957663090203)
  ·
    refine ⟨2088466568180936494635305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1392311045453957663090203 2088466568180936494635305)
    ·
      refine ⟨1566349926135702370976479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2088466568180936494635305 1566349926135702370976479)
      ·
        refine ⟨2349524889203553556464719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566349926135702370976479 2349524889203553556464719)
        ·
          refine ⟨3524287333805330334697079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349524889203553556464719 3524287333805330334697079)
          ·
            refine ⟨5286431000707995502045619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524287333805330334697079 5286431000707995502045619)
            ·
              refine ⟨7929646501061993253068429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286431000707995502045619 7929646501061993253068429)
              ·
                refine ⟨2973617437898247469900661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7929646501061993253068429 2973617437898247469900661)
                ·
                  refine ⟨278776634802960700303187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2973617437898247469900661 278776634802960700303187)
                  ·
                    refine ⟨418164952204441050454781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 278776634802960700303187 418164952204441050454781)
                    ·
                      refine ⟨156811857076665393920543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418164952204441050454781 156811857076665393920543)
                      ·
                        rfl

theorem cell23_305390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_305390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305390 prefixEnd_305390 := by exact prefixLift 305390
  have htrace : WordTrace (prefixWord ++ tailWord_305390) baseStart_305390 baseEnd_305390 := by
    simpa [prefixWord, tailWord_305390, baseEnd_305390] using wordTrace_append hprefix tailTrace_305390
  have hstable : (prefixWord ++ tailWord_305390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305390).length < 2 ^ (prefixWord ++ tailWord_305390).sum := by decide
  have hdescent : baseEnd_305390 < baseStart_305390 := by decide
  rcases family_descends (prefixWord ++ tailWord_305390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305407 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 1, 1, 3]
def baseStart_305407 : Nat := 118140960795 + 305407 * 2 ^ 59
def prefixEnd_305407 : Nat := 4983230072969 + 3 ^ 40 * 305407 * 2
def baseEnd_305407 : Nat := 156820586247791827407965

theorem tailTrace_305407 : CollatzResearch.WordTrace tailWord_305407 prefixEnd_305407 156820586247791827407965 := by
  unfold tailWord_305407
  simp only [CollatzResearch.WordTrace]
  refine ⟨11139108404570073208090475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7426072269713382138726983 11139108404570073208090475)
  ·
    refine ⟨16708662606855109812135713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11139108404570073208090475 16708662606855109812135713)
    ·
      refine ⟨12531496955141332359101785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16708662606855109812135713 12531496955141332359101785)
      ·
        refine ⟨9398622716355999269326339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12531496955141332359101785 9398622716355999269326339)
        ·
          refine ⟨14097934074533998903989509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9398622716355999269326339 14097934074533998903989509)
          ·
            refine ⟨2643362638975124794498033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14097934074533998903989509 2643362638975124794498033)
            ·
              refine ⟨1982521979231343595873525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2643362638975124794498033 1982521979231343595873525)
              ·
                refine ⟨185861435552938462113143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1982521979231343595873525 185861435552938462113143)
                ·
                  refine ⟨278792153329407693169715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185861435552938462113143 278792153329407693169715)
                  ·
                    refine ⟨418188229994111539754573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 278792153329407693169715 418188229994111539754573)
                    ·
                      refine ⟨156820586247791827407965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418188229994111539754573 156820586247791827407965)
                      ·
                        rfl

theorem cell23_305407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_305407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305407 prefixEnd_305407 := by exact prefixLift 305407
  have htrace : WordTrace (prefixWord ++ tailWord_305407) baseStart_305407 baseEnd_305407 := by
    simpa [prefixWord, tailWord_305407, baseEnd_305407] using wordTrace_append hprefix tailTrace_305407
  have hstable : (prefixWord ++ tailWord_305407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305407).length < 2 ^ (prefixWord ++ tailWord_305407).sum := by decide
  have hdescent : baseEnd_305407 < baseStart_305407 := by decide
  rcases family_descends (prefixWord ++ tailWord_305407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305423 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 4, 4]
def baseStart_305423 : Nat := 118140960795 + 305423 * 2 ^ 59
def prefixEnd_305423 : Nat := 4983230072969 + 3 ^ 40 * 305423 * 2
def baseEnd_305423 : Nat := 52276267312754588269297

theorem tailTrace_305423 : CollatzResearch.WordTrace tailWord_305423 prefixEnd_305423 52276267312754588269297 := by
  unfold tailWord_305423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11139691972512107940672923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7426461315008071960448615 11139691972512107940672923)
  ·
    refine ⟨16709537958768161911009385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11139691972512107940672923 16709537958768161911009385)
    ·
      refine ⟨12532153469076121433257039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16709537958768161911009385 12532153469076121433257039)
      ·
        refine ⟨18798230203614182149885559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12532153469076121433257039 18798230203614182149885559)
        ·
          refine ⟨28197345305421273224828339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18798230203614182149885559 28197345305421273224828339)
          ·
            refine ⟨42296017958131909837242509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28197345305421273224828339 42296017958131909837242509)
            ·
              refine ⟨15861006734299466188965941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42296017958131909837242509 15861006734299466188965941)
              ·
                refine ⟨1486969381340574955215557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15861006734299466188965941 1486969381340574955215557)
                ·
                  refine ⟨278806759001357804102917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1486969381340574955215557 278806759001357804102917)
                  ·
                    refine ⟨52276267312754588269297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278806759001357804102917 52276267312754588269297)
                    ·
                      rfl

theorem cell23_305423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_305423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305423 prefixEnd_305423 := by exact prefixLift 305423
  have htrace : WordTrace (prefixWord ++ tailWord_305423) baseStart_305423 baseEnd_305423 := by
    simpa [prefixWord, tailWord_305423, baseEnd_305423] using wordTrace_append hprefix tailTrace_305423
  have hstable : (prefixWord ++ tailWord_305423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305423).length < 2 ^ (prefixWord ++ tailWord_305423).sum := by decide
  have hdescent : baseEnd_305423 < baseStart_305423 := by decide
  rcases family_descends (prefixWord ++ tailWord_305423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305440 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 1, 6]
def baseStart_305440 : Nat := 118140960795 + 305440 * 2 ^ 59
def prefixEnd_305440 : Nat := 4983230072969 + 3 ^ 40 * 305440 * 2
def baseEnd_305440 : Nat := 52279177036463399431771

theorem tailTrace_305440 : CollatzResearch.WordTrace tailWord_305440 prefixEnd_305440 52279177036463399431771 := by
  unfold tailWord_305440
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570156006725259922020887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7426874675633679896027849 5570156006725259922020887)
  ·
    refine ⟨8355234010087889883031331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5570156006725259922020887 8355234010087889883031331)
    ·
      refine ⟨12532851015131834824546997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8355234010087889883031331 12532851015131834824546997)
      ·
        refine ⟨1174954782668609514801281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12532851015131834824546997 1174954782668609514801281)
        ·
          refine ⟨881216087001457136100961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1174954782668609514801281 881216087001457136100961)
          ·
            refine ⟨660912065251092852075721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881216087001457136100961 660912065251092852075721)
            ·
              refine ⟨495684048938319639056791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660912065251092852075721 495684048938319639056791)
              ·
                refine ⟨743526073407479458585187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495684048938319639056791 743526073407479458585187)
                ·
                  refine ⟨1115289110111219187877781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743526073407479458585187 1115289110111219187877781)
                  ·
                    refine ⟨52279177036463399431771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1115289110111219187877781 52279177036463399431771)
                    ·
                      rfl

theorem cell23_305440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_305440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305440 prefixEnd_305440 := by exact prefixLift 305440
  have htrace : WordTrace (prefixWord ++ tailWord_305440) baseStart_305440 baseEnd_305440 := by
    simpa [prefixWord, tailWord_305440, baseEnd_305440] using wordTrace_append hprefix tailTrace_305440
  have hstable : (prefixWord ++ tailWord_305440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305440).length < 2 ^ (prefixWord ++ tailWord_305440).sum := by decide
  have hdescent : baseEnd_305440 < baseStart_305440 := by decide
  rcases family_descends (prefixWord ++ tailWord_305440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305464 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 1, 2, 2]
def baseStart_305464 : Nat := 118140960795 + 305464 * 2 ^ 59
def prefixEnd_305464 : Nat := 4983230072969 + 3 ^ 40 * 305464 * 2
def baseEnd_305464 : Nat := 156849854645098104395203

theorem tailTrace_305464 : CollatzResearch.WordTrace tailWord_305464 prefixEnd_305464 156849854645098104395203 := by
  unfold tailWord_305464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570593682681785971457723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7427458243575714628610297 5570593682681785971457723)
  ·
    refine ⟨8355890524022678957186585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5570593682681785971457723 8355890524022678957186585)
    ·
      refine ⟨6266917893017009217889939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8355890524022678957186585 6266917893017009217889939)
      ·
        refine ⟨9400376839525513826834909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266917893017009217889939 9400376839525513826834909)
        ·
          refine ⟨3525141314822067685063091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9400376839525513826834909 3525141314822067685063091)
          ·
            refine ⟨5287711972233101527594637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525141314822067685063091 5287711972233101527594637)
            ·
              refine ⟨1982891989587413072847989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5287711972233101527594637 1982891989587413072847989)
              ·
                refine ⟨185896124023819975579499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1982891989587413072847989 185896124023819975579499)
                ·
                  refine ⟨278844186035729963369249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185896124023819975579499 278844186035729963369249)
                  ·
                    refine ⟨209133139526797472526937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 278844186035729963369249 209133139526797472526937)
                    ·
                      refine ⟨156849854645098104395203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209133139526797472526937 156849854645098104395203)
                      ·
                        rfl

theorem cell23_305464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_305464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305464 prefixEnd_305464 := by exact prefixLift 305464
  have htrace : WordTrace (prefixWord ++ tailWord_305464) baseStart_305464 baseEnd_305464 := by
    simpa [prefixWord, tailWord_305464, baseEnd_305464] using wordTrace_append hprefix tailTrace_305464
  have hstable : (prefixWord ++ tailWord_305464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305464).length < 2 ^ (prefixWord ++ tailWord_305464).sum := by decide
  have hdescent : baseEnd_305464 < baseStart_305464 := by decide
  rcases family_descends (prefixWord ++ tailWord_305464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305503 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_305503 : Nat := 118140960795 + 305503 * 2 ^ 59
def prefixEnd_305503 : Nat := 4983230072969 + 3 ^ 40 * 305503 * 2
def baseEnd_305503 : Nat := 156869880390623451807523

theorem tailTrace_305503 : CollatzResearch.WordTrace tailWord_305503 prefixEnd_305503 156869880390623451807523 := by
  unfold tailWord_305503
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142609812222281603585163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7428406541481521069056775 11142609812222281603585163)
  ·
    refine ⟨16713914718333422405377745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11142609812222281603585163 16713914718333422405377745)
    ·
      refine ⟨12535436038750066804033309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16713914718333422405377745 12535436038750066804033309)
      ·
        refine ⟨4700788514531275051512491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12535436038750066804033309 4700788514531275051512491)
        ·
          refine ⟨7051182771796912577268737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4700788514531275051512491 7051182771796912577268737)
          ·
            refine ⟨5288387078847684432951553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7051182771796912577268737 5288387078847684432951553)
            ·
              refine ⟨3966290309135763324713665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288387078847684432951553 3966290309135763324713665)
              ·
                refine ⟨2974717731851822493535249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966290309135763324713665 2974717731851822493535249)
                ·
                  refine ⟨2231038298888866870151437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974717731851822493535249 2231038298888866870151437)
                  ·
                    refine ⟨836639362083325076306789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231038298888866870151437 836639362083325076306789)
                    ·
                      refine ⟨156869880390623451807523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 836639362083325076306789 156869880390623451807523)
                      ·
                        rfl

theorem cell23_305503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_305503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305503 prefixEnd_305503 := by exact prefixLift 305503
  have htrace : WordTrace (prefixWord ++ tailWord_305503) baseStart_305503 baseEnd_305503 := by
    simpa [prefixWord, tailWord_305503, baseEnd_305503] using wordTrace_append hprefix tailTrace_305503
  have hstable : (prefixWord ++ tailWord_305503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305503).length < 2 ^ (prefixWord ++ tailWord_305503).sum := by decide
  have hdescent : baseEnd_305503 < baseStart_305503 := by decide
  rcases family_descends (prefixWord ++ tailWord_305503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305523 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5]
def baseStart_305523 : Nat := 118140960795 + 305523 * 2 ^ 59
def prefixEnd_305523 : Nat := 4983230072969 + 3 ^ 40 * 305523 * 2
def baseEnd_305523 : Nat := 156880150003713373557431

theorem tailTrace_305523 : CollatzResearch.WordTrace tailWord_305523 prefixEnd_305523 156880150003713373557431 := by
  unfold tailWord_305523
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143339272149825019313223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7428892848099883346208815 11143339272149825019313223)
  ·
    refine ⟨16715008908224737528969835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11143339272149825019313223 16715008908224737528969835)
    ·
      refine ⟨25072513362337106293454753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16715008908224737528969835 25072513362337106293454753)
      ·
        refine ⟨18804385021752829720091065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25072513362337106293454753 18804385021752829720091065)
        ·
          refine ⟨14103288766314622290068299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18804385021752829720091065 14103288766314622290068299)
          ·
            refine ⟨21154933149471933435102449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14103288766314622290068299 21154933149471933435102449)
            ·
              refine ⟨15866199862103950076326837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21154933149471933435102449 15866199862103950076326837)
              ·
                refine ⟨1487456237072245319655641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15866199862103950076326837 1487456237072245319655641)
                ·
                  refine ⟨1115592177804183989741731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487456237072245319655641 1115592177804183989741731)
                  ·
                    refine ⟨1673388266706275984612597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1115592177804183989741731 1673388266706275984612597)
                    ·
                      refine ⟨156880150003713373557431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1673388266706275984612597 156880150003713373557431)
                      ·
                        rfl

theorem cell23_305523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_305523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305523 prefixEnd_305523 := by exact prefixLift 305523
  have htrace : WordTrace (prefixWord ++ tailWord_305523) baseStart_305523 baseEnd_305523 := by
    simpa [prefixWord, tailWord_305523, baseEnd_305523] using wordTrace_append hprefix tailTrace_305523
  have hstable : (prefixWord ++ tailWord_305523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305523).length < 2 ^ (prefixWord ++ tailWord_305523).sum := by decide
  have hdescent : baseEnd_305523 < baseStart_305523 := by decide
  rcases family_descends (prefixWord ++ tailWord_305523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305540 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_305540 : Nat := 118140960795 + 305540 * 2 ^ 59
def prefixEnd_305540 : Nat := 4983230072969 + 3 ^ 40 * 305540 * 2
def baseEnd_305540 : Nat := 156888879174839807044853

theorem tailTrace_305540 : CollatzResearch.WordTrace tailWord_305540 prefixEnd_305540 156888879174839807044853 := by
  unfold tailWord_305540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571979656544118461341037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7429306208725491281788049 5571979656544118461341037)
  ·
    refine ⟨2089492371204044423002889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5571979656544118461341037 2089492371204044423002889)
    ·
      refine ⟨1567119278403033317252167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2089492371204044423002889 1567119278403033317252167)
      ·
        refine ⟨2350678917604549975878251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567119278403033317252167 2350678917604549975878251)
        ·
          refine ⟨3526018376406824963817377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350678917604549975878251 3526018376406824963817377)
          ·
            refine ⟨2644513782305118722863033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526018376406824963817377 2644513782305118722863033)
            ·
              refine ⟨1983385336728839042147275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644513782305118722863033 1983385336728839042147275)
              ·
                refine ⟨2975078005093258563220913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983385336728839042147275 2975078005093258563220913)
                ·
                  refine ⟨2231308503819943922415685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975078005093258563220913 2231308503819943922415685)
                  ·
                    refine ⟨418370344466239485452941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231308503819943922415685 418370344466239485452941)
                    ·
                      refine ⟨156888879174839807044853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418370344466239485452941 156888879174839807044853)
                      ·
                        rfl

theorem cell23_305540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_305540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305540 prefixEnd_305540 := by exact prefixLift 305540
  have htrace : WordTrace (prefixWord ++ tailWord_305540) baseStart_305540 baseEnd_305540 := by
    simpa [prefixWord, tailWord_305540, baseEnd_305540] using wordTrace_append hprefix tailTrace_305540
  have hstable : (prefixWord ++ tailWord_305540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305540).length < 2 ^ (prefixWord ++ tailWord_305540).sum := by decide
  have hdescent : baseEnd_305540 < baseStart_305540 := by decide
  rcases family_descends (prefixWord ++ tailWord_305540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305597 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_305597 : Nat := 118140960795 + 305597 * 2 ^ 59
def prefixEnd_305597 : Nat := 4983230072969 + 3 ^ 40 * 305597 * 2
def baseEnd_305597 : Nat := 156918147572146084032091

theorem tailTrace_305597 : CollatzResearch.WordTrace tailWord_305597 prefixEnd_305597 156918147572146084032091 := by
  unfold tailWord_305597
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146038273881735657507045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7430692182587823771671363 11146038273881735657507045)
  ·
    refine ⟨2089882176352825435782571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11146038273881735657507045 2089882176352825435782571)
    ·
      refine ⟨3134823264529238153673857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2089882176352825435782571 3134823264529238153673857)
      ·
        refine ⟨2351117448396928615255393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3134823264529238153673857 2351117448396928615255393)
        ·
          refine ⟨1763338086297696461441545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351117448396928615255393 1763338086297696461441545)
          ·
            refine ⟨1322503564723272346081159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763338086297696461441545 1322503564723272346081159)
            ·
              refine ⟨1983755347084908519121739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322503564723272346081159 1983755347084908519121739)
              ·
                refine ⟨2975633020627362778682609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983755347084908519121739 2975633020627362778682609)
                ·
                  refine ⟨2231724765470522084011957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975633020627362778682609 2231724765470522084011957)
                  ·
                    refine ⟨209224196762861445376121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2231724765470522084011957 209224196762861445376121)
                    ·
                      refine ⟨156918147572146084032091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209224196762861445376121 156918147572146084032091)
                      ·
                        rfl

theorem cell23_305597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_305597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305597 prefixEnd_305597 := by exact prefixLift 305597
  have htrace : WordTrace (prefixWord ++ tailWord_305597) baseStart_305597 baseEnd_305597 := by
    simpa [prefixWord, tailWord_305597, baseEnd_305597] using wordTrace_append hprefix tailTrace_305597
  have hstable : (prefixWord ++ tailWord_305597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305597).length < 2 ^ (prefixWord ++ tailWord_305597).sum := by decide
  have hdescent : baseEnd_305597 < baseStart_305597 := by decide
  rcases family_descends (prefixWord ++ tailWord_305597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305601 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_305601 : Nat := 118140960795 + 305601 * 2 ^ 59
def prefixEnd_305601 : Nat := 4983230072969 + 3 ^ 40 * 305601 * 2
def baseEnd_305601 : Nat := 156920201494764068382073

theorem tailTrace_305601 : CollatzResearch.WordTrace tailWord_305601 prefixEnd_305601 156920201494764068382073 := by
  unfold tailWord_305601
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146184165867244340652657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7430789443911496227101771 11146184165867244340652657)
  ·
    refine ⟨8359638124400433255489493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11146184165867244340652657 8359638124400433255489493)
    ·
      refine ⟨195929018540635154425535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8359638124400433255489493 195929018540635154425535)
      ·
        refine ⟨293893527810952731638303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195929018540635154425535 293893527810952731638303)
        ·
          refine ⟨440840291716429097457455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293893527810952731638303 440840291716429097457455)
          ·
            refine ⟨661260437574643646186183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440840291716429097457455 661260437574643646186183)
            ·
              refine ⟨991890656361965469279275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661260437574643646186183 991890656361965469279275)
              ·
                refine ⟨1487835984542948203918913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991890656361965469279275 1487835984542948203918913)
                ·
                  refine ⟨1115876988407211152939185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487835984542948203918913 1115876988407211152939185)
                  ·
                    refine ⟨836907741305408364704389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1115876988407211152939185 836907741305408364704389)
                    ·
                      refine ⟨156920201494764068382073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 836907741305408364704389 156920201494764068382073)
                      ·
                        rfl

theorem cell23_305601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_305601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305601 prefixEnd_305601 := by exact prefixLift 305601
  have htrace : WordTrace (prefixWord ++ tailWord_305601) baseStart_305601 baseEnd_305601 := by
    simpa [prefixWord, tailWord_305601, baseEnd_305601] using wordTrace_append hprefix tailTrace_305601
  have hstable : (prefixWord ++ tailWord_305601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305601).length < 2 ^ (prefixWord ++ tailWord_305601).sum := by decide
  have hdescent : baseEnd_305601 < baseStart_305601 := by decide
  rcases family_descends (prefixWord ++ tailWord_305601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305603 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 8]
def baseStart_305603 : Nat := 118140960795 + 305603 * 2 ^ 59
def prefixEnd_305603 : Nat := 4983230072969 + 3 ^ 40 * 305603 * 2
def baseEnd_305603 : Nat := 52307076152024353519021

theorem tailTrace_305603 : CollatzResearch.WordTrace tailWord_305603 prefixEnd_305603 52307076152024353519021 := by
  unfold tailWord_305603
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146257111859998682225463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7430838074573332454816975 11146257111859998682225463)
  ·
    refine ⟨16719385667789998023338195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11146257111859998682225463 16719385667789998023338195)
    ·
      refine ⟨25079078501684997035007293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16719385667789998023338195 25079078501684997035007293)
      ·
        refine ⟨9404654438131873888127735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25079078501684997035007293 9404654438131873888127735)
        ·
          refine ⟨14106981657197810832191603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9404654438131873888127735 14106981657197810832191603)
          ·
            refine ⟨21160472485796716248287405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14106981657197810832191603 21160472485796716248287405)
            ·
              refine ⟨7935177182173768593107777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21160472485796716248287405 7935177182173768593107777)
              ·
                refine ⟨5951382886630326444830833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7935177182173768593107777 5951382886630326444830833)
                ·
                  refine ⟨4463537164972744833623125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951382886630326444830833 4463537164972744833623125)
                  ·
                    refine ⟨52307076152024353519021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4463537164972744833623125 52307076152024353519021)
                    ·
                      rfl

theorem cell23_305603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_305603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305603 prefixEnd_305603 := by exact prefixLift 305603
  have htrace : WordTrace (prefixWord ++ tailWord_305603) baseStart_305603 baseEnd_305603 := by
    simpa [prefixWord, tailWord_305603, baseEnd_305603] using wordTrace_append hprefix tailTrace_305603
  have hstable : (prefixWord ++ tailWord_305603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305603).length < 2 ^ (prefixWord ++ tailWord_305603).sum := by decide
  have hdescent : baseEnd_305603 < baseStart_305603 := by decide
  rcases family_descends (prefixWord ++ tailWord_305603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305604 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_305604 : Nat := 118140960795 + 305604 * 2 ^ 59
def prefixEnd_305604 : Nat := 4983230072969 + 3 ^ 40 * 305604 * 2
def baseEnd_305604 : Nat := 156921741936727556644559

theorem tailTrace_305604 : CollatzResearch.WordTrace tailWord_305604 prefixEnd_305604 156921741936727556644559 := by
  unfold tailWord_305604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573146792428187926505933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7430862389904250568674577 5573146792428187926505933)
  ·
    refine ⟨2089930047160570472439725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5573146792428187926505933 2089930047160570472439725)
    ·
      refine ⟨783723767685213927164897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2089930047160570472439725 783723767685213927164897)
      ·
        refine ⟨587792825763910445373673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 783723767685213927164897 587792825763910445373673)
        ·
          refine ⟨440844619322932834030255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587792825763910445373673 440844619322932834030255)
          ·
            refine ⟨661266928984399251045383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440844619322932834030255 661266928984399251045383)
            ·
              refine ⟨991900393476598876568075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661266928984399251045383 991900393476598876568075)
              ·
                refine ⟨1487850590214898314852113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991900393476598876568075 1487850590214898314852113)
                ·
                  refine ⟨1115887942661173736139085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1487850590214898314852113 1115887942661173736139085)
                  ·
                    refine ⟨418457978497940151052157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1115887942661173736139085 418457978497940151052157)
                    ·
                      refine ⟨156921741936727556644559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418457978497940151052157 156921741936727556644559)
                      ·
                        rfl

theorem cell23_305604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_305604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305604 prefixEnd_305604 := by exact prefixLift 305604
  have htrace : WordTrace (prefixWord ++ tailWord_305604) baseStart_305604 baseEnd_305604 := by
    simpa [prefixWord, tailWord_305604, baseEnd_305604] using wordTrace_append hprefix tailTrace_305604
  have hstable : (prefixWord ++ tailWord_305604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305604).length < 2 ^ (prefixWord ++ tailWord_305604).sum := by decide
  have hdescent : baseEnd_305604 < baseStart_305604 := by decide
  rcases family_descends (prefixWord ++ tailWord_305604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305610 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_305610 : Nat := 118140960795 + 305610 * 2 ^ 59
def prefixEnd_305610 : Nat := 4983230072969 + 3 ^ 40 * 305610 * 2
def baseEnd_305610 : Nat := 156924822820654533169531

theorem tailTrace_305610 : CollatzResearch.WordTrace tailWord_305610 prefixEnd_305610 156924822820654533169531 := by
  unfold tailWord_305610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786628105708659719432571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7431008281889759251820189 2786628105708659719432571)
  ·
    refine ⟨4179942158562989579148857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2786628105708659719432571 4179942158562989579148857)
    ·
      refine ⟨3134956618922242184361643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4179942158562989579148857 3134956618922242184361643)
      ·
        refine ⟨4702434928383363276542465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3134956618922242184361643 4702434928383363276542465)
        ·
          refine ⟨3526826196287522457406849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4702434928383363276542465 3526826196287522457406849)
          ·
            refine ⟨2645119647215641843055137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526826196287522457406849 2645119647215641843055137)
            ·
              refine ⟨1983839735411731382291353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645119647215641843055137 1983839735411731382291353)
              ·
                refine ⟨1487879801558798536718515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983839735411731382291353 1487879801558798536718515)
                ·
                  refine ⟨2231819702338197805077773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487879801558798536718515 2231819702338197805077773)
                  ·
                    refine ⟨836932388376824176904165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2231819702338197805077773 836932388376824176904165)
                    ·
                      refine ⟨156924822820654533169531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 836932388376824176904165 156924822820654533169531)
                      ·
                        rfl

theorem cell23_305610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_305610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305610 prefixEnd_305610 := by exact prefixLift 305610
  have htrace : WordTrace (prefixWord ++ tailWord_305610) baseStart_305610 baseEnd_305610 := by
    simpa [prefixWord, tailWord_305610, baseEnd_305610] using wordTrace_append hprefix tailTrace_305610
  have hstable : (prefixWord ++ tailWord_305610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305610).length < 2 ^ (prefixWord ++ tailWord_305610).sum := by decide
  have hdescent : baseEnd_305610 < baseStart_305610 := by decide
  rcases family_descends (prefixWord ++ tailWord_305610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305640 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_305640 : Nat := 118140960795 + 305640 * 2 ^ 59
def prefixEnd_305640 : Nat := 4983230072969 + 3 ^ 40 * 305640 * 2
def baseEnd_305640 : Nat := 156940227240289415794393

theorem tailTrace_305640 : CollatzResearch.WordTrace tailWord_305640 prefixEnd_305640 156940227240289415794393 := by
  unfold tailWord_305640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573803306362977000661187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7431737741817302667548249 5573803306362977000661187)
  ·
    refine ⟨8360704959544465500991781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5573803306362977000661187 8360704959544465500991781)
    ·
      refine ⟨1567632179914587281435959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8360704959544465500991781 1567632179914587281435959)
      ·
        refine ⟨2351448269871880922153939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567632179914587281435959 2351448269871880922153939)
        ·
          refine ⟨3527172404807821383230909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351448269871880922153939 3527172404807821383230909)
          ·
            refine ⟨1322689651802933018711591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3527172404807821383230909 1322689651802933018711591)
            ·
              refine ⟨1984034477704399528067387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322689651802933018711591 1984034477704399528067387)
              ·
                refine ⟨2976051716556599292101081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984034477704399528067387 2976051716556599292101081)
                ·
                  refine ⟨2232038787417449469075811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976051716556599292101081 2232038787417449469075811)
                  ·
                    refine ⟨3348058181126174203613717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232038787417449469075811 3348058181126174203613717)
                    ·
                      refine ⟨156940227240289415794393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3348058181126174203613717 156940227240289415794393)
                      ·
                        rfl

theorem cell23_305640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_305640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305640 prefixEnd_305640 := by exact prefixLift 305640
  have htrace : WordTrace (prefixWord ++ tailWord_305640) baseStart_305640 baseEnd_305640 := by
    simpa [prefixWord, tailWord_305640, baseEnd_305640] using wordTrace_append hprefix tailTrace_305640
  have hstable : (prefixWord ++ tailWord_305640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305640).length < 2 ^ (prefixWord ++ tailWord_305640).sum := by decide
  have hdescent : baseEnd_305640 < baseStart_305640 := by decide
  rcases family_descends (prefixWord ++ tailWord_305640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305654 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_305654 : Nat := 118140960795 + 305654 * 2 ^ 59
def prefixEnd_305654 : Nat := 4983230072969 + 3 ^ 40 * 305654 * 2
def baseEnd_305654 : Nat := 52315805323150787006443

theorem tailTrace_305654 : CollatzResearch.WordTrace tailWord_305654 prefixEnd_305654 52315805323150787006443 := by
  unfold tailWord_305654
  simp only [CollatzResearch.WordTrace]
  refine ⟨696757327167202149520751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7432078156450156261554677 696757327167202149520751)
  ·
    refine ⟨1045135990750803224281127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696757327167202149520751 1045135990750803224281127)
    ·
      refine ⟨1567703986126204836421691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045135990750803224281127 1567703986126204836421691)
      ·
        refine ⟨2351555979189307254632537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567703986126204836421691 2351555979189307254632537)
        ·
          refine ⟨1763666984391980440974403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351555979189307254632537 1763666984391980440974403)
          ·
            refine ⟨2645500476587970661461605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763666984391980440974403 2645500476587970661461605)
            ·
              refine ⟨496031339360244499024051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2645500476587970661461605 496031339360244499024051)
              ·
                refine ⟨744047009040366748536077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496031339360244499024051 744047009040366748536077)
                ·
                  refine ⟨279017628390137530701029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744047009040366748536077 279017628390137530701029)
                  ·
                    refine ⟨52315805323150787006443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 279017628390137530701029 52315805323150787006443)
                    ·
                      rfl

theorem cell23_305654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_305654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305654 prefixEnd_305654 := by exact prefixLift 305654
  have htrace : WordTrace (prefixWord ++ tailWord_305654) baseStart_305654 baseEnd_305654 := by
    simpa [prefixWord, tailWord_305654, baseEnd_305654] using wordTrace_append hprefix tailTrace_305654
  have hstable : (prefixWord ++ tailWord_305654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305654).length < 2 ^ (prefixWord ++ tailWord_305654).sum := by decide
  have hdescent : baseEnd_305654 < baseStart_305654 := by decide
  rcases family_descends (prefixWord ++ tailWord_305654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305667 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 6]
def baseStart_305667 : Nat := 118140960795 + 305667 * 2 ^ 59
def prefixEnd_305667 : Nat := 4983230072969 + 3 ^ 40 * 305667 * 2
def baseEnd_305667 : Nat := 17439343468662312239641

theorem tailTrace_305667 : CollatzResearch.WordTrace tailWord_305667 prefixEnd_305667 17439343468662312239641 := by
  unfold tailWord_305667
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148591383628137612555255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432394255752091741703503 11148591383628137612555255)
  ·
    refine ⟨16722887075442206418832883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11148591383628137612555255 16722887075442206418832883)
    ·
      refine ⟨25084330613163309628249325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16722887075442206418832883 25084330613163309628249325)
      ·
        refine ⟨9406623979936241110593497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25084330613163309628249325 9406623979936241110593497)
        ·
          refine ⟨7054967984952180832945123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9406623979936241110593497 7054967984952180832945123)
          ·
            refine ⟨10582451977428271249417685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7054967984952180832945123 10582451977428271249417685)
            ·
              refine ⟨248026218220975107408227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10582451977428271249417685 248026218220975107408227)
              ·
                refine ⟨372039327331462661112341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248026218220975107408227 372039327331462661112341)
                ·
                  refine ⟨17439343468662312239641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 372039327331462661112341 17439343468662312239641)
                  ·
                    rfl

theorem cell23_305667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 6].length) (baseStart_305667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305667 prefixEnd_305667 := by exact prefixLift 305667
  have htrace : WordTrace (prefixWord ++ tailWord_305667) baseStart_305667 baseEnd_305667 := by
    simpa [prefixWord, tailWord_305667, baseEnd_305667] using wordTrace_append hprefix tailTrace_305667
  have hstable : (prefixWord ++ tailWord_305667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305667).length < 2 ^ (prefixWord ++ tailWord_305667).sum := by decide
  have hdescent : baseEnd_305667 < baseStart_305667 := by decide
  rcases family_descends (prefixWord ++ tailWord_305667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305697 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 1, 5]
def baseStart_305697 : Nat := 118140960795 + 305697 * 2 ^ 59
def prefixEnd_305697 : Nat := 4983230072969 + 3 ^ 40 * 305697 * 2
def baseEnd_305697 : Nat := 52323165212531897593877

theorem tailTrace_305697 : CollatzResearch.WordTrace tailWord_305697 prefixEnd_305697 52323165212531897593877 := by
  unfold tailWord_305697
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149685573519452736147345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7433123715679635157431563 11149685573519452736147345)
  ·
    refine ⟨8362264180139589552110509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11149685573519452736147345 8362264180139589552110509)
    ·
      refine ⟨3135849067552346082041441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8362264180139589552110509 3135849067552346082041441)
      ·
        refine ⟨2351886800664259561531081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3135849067552346082041441 2351886800664259561531081)
        ·
          refine ⟨1763915100498194671148311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351886800664259561531081 1763915100498194671148311)
          ·
            refine ⟨2645872650747292006722467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763915100498194671148311 2645872650747292006722467)
            ·
              refine ⟨3968808976120938010083701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645872650747292006722467 3968808976120938010083701)
              ·
                refine ⟨372075841511337938445347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3968808976120938010083701 372075841511337938445347)
                ·
                  refine ⟨558113762267006907668021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372075841511337938445347 558113762267006907668021)
                  ·
                    refine ⟨52323165212531897593877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 558113762267006907668021 52323165212531897593877)
                    ·
                      rfl

theorem cell23_305697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_305697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305697 prefixEnd_305697 := by exact prefixLift 305697
  have htrace : WordTrace (prefixWord ++ tailWord_305697) baseStart_305697 baseEnd_305697 := by
    simpa [prefixWord, tailWord_305697, baseEnd_305697] using wordTrace_append hprefix tailTrace_305697
  have hstable : (prefixWord ++ tailWord_305697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305697).length < 2 ^ (prefixWord ++ tailWord_305697).sum := by decide
  have hdescent : baseEnd_305697 < baseStart_305697 := by decide
  rcases family_descends (prefixWord ++ tailWord_305697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305717 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_305717 : Nat := 118140960795 + 305717 * 2 ^ 59
def prefixEnd_305717 : Nat := 4983230072969 + 3 ^ 40 * 305717 * 2
def baseEnd_305717 : Nat := 156979765250685614531539

theorem tailTrace_305717 : CollatzResearch.WordTrace tailWord_305717 prefixEnd_305717 156979765250685614531539 := by
  unfold tailWord_305717
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150415033446996151875405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7433610022297997434583603 11150415033446996151875405)
  ·
    refine ⟨4181405637542623556953277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11150415033446996151875405 4181405637542623556953277)
    ·
      refine ⟨1568027114078483833857479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4181405637542623556953277 1568027114078483833857479)
      ·
        refine ⟨2352040671117725750786219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568027114078483833857479 2352040671117725750786219)
        ·
          refine ⟨3528061006676588626179329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352040671117725750786219 3528061006676588626179329)
          ·
            refine ⟨2646045755007441469634497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3528061006676588626179329 2646045755007441469634497)
            ·
              refine ⟨1984534316255581102225873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2646045755007441469634497 1984534316255581102225873)
              ·
                refine ⟨1488400737191685826669405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984534316255581102225873 1488400737191685826669405)
                ·
                  refine ⟨558150276446882185001027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1488400737191685826669405 558150276446882185001027)
                  ·
                    refine ⟨837225414670323277501541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558150276446882185001027 837225414670323277501541)
                    ·
                      refine ⟨156979765250685614531539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 837225414670323277501541 156979765250685614531539)
                      ·
                        rfl

theorem cell23_305717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_305717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305717 prefixEnd_305717 := by exact prefixLift 305717
  have htrace : WordTrace (prefixWord ++ tailWord_305717) baseStart_305717 baseEnd_305717 := by
    simpa [prefixWord, tailWord_305717, baseEnd_305717] using wordTrace_append hprefix tailTrace_305717
  have hstable : (prefixWord ++ tailWord_305717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305717).length < 2 ^ (prefixWord ++ tailWord_305717).sum := by decide
  have hdescent : baseEnd_305717 < baseStart_305717 := by decide
  rcases family_descends (prefixWord ++ tailWord_305717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305740 : List Nat := [2, 2, 1, 3, 1, 2, 1, 11]
def baseStart_305740 : Nat := 118140960795 + 305740 * 2 ^ 59
def prefixEnd_305740 : Nat := 4983230072969 + 3 ^ 40 * 305740 * 2
def baseEnd_305740 : Nat := 5814502789101445353479

theorem tailTrace_305740 : CollatzResearch.WordTrace tailWord_305740 prefixEnd_305740 5814502789101445353479 := by
  unfold tailWord_305740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575626956181835539981337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7434169274909114053308449 5575626956181835539981337)
  ·
    refine ⟨4181720217136376654986003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5575626956181835539981337 4181720217136376654986003)
    ·
      refine ⟨6272580325704564982479005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181720217136376654986003 6272580325704564982479005)
      ·
        refine ⟨2352217622139211868429627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6272580325704564982479005 2352217622139211868429627)
        ·
          refine ⟨3528326433208817802644441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352217622139211868429627 3528326433208817802644441)
          ·
            refine ⟨2646244824906613351983331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3528326433208817802644441 2646244824906613351983331)
            ·
              refine ⟨3969367237359920027974997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646244824906613351983331 3969367237359920027974997)
              ·
                refine ⟨5814502789101445353479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 3969367237359920027974997 5814502789101445353479)
                ·
                  rfl

theorem cell23_305740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 11].length) (baseStart_305740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305740 prefixEnd_305740 := by exact prefixLift 305740
  have htrace : WordTrace (prefixWord ++ tailWord_305740) baseStart_305740 baseEnd_305740 := by
    simpa [prefixWord, tailWord_305740, baseEnd_305740] using wordTrace_append hprefix tailTrace_305740
  have hstable : (prefixWord ++ tailWord_305740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305740).length < 2 ^ (prefixWord ++ tailWord_305740).sum := by decide
  have hdescent : baseEnd_305740 < baseStart_305740 := by decide
  rcases family_descends (prefixWord ++ tailWord_305740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305767 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_305767 : Nat := 118140960795 + 305767 * 2 ^ 59
def prefixEnd_305767 : Nat := 4983230072969 + 3 ^ 40 * 305767 * 2
def baseEnd_305767 : Nat := 157005439283410418906309

theorem tailTrace_305767 : CollatzResearch.WordTrace tailWord_305767 prefixEnd_305767 157005439283410418906309 := by
  unfold tailWord_305767
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152238683265854691195555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7434825788843903127463703 11152238683265854691195555)
  ·
    refine ⟨16728358024898782036793333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11152238683265854691195555 16728358024898782036793333)
    ·
      refine ⟨1568283564834260815949375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16728358024898782036793333 1568283564834260815949375)
      ·
        refine ⟨2352425347251391223924063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568283564834260815949375 2352425347251391223924063)
        ·
          refine ⟨3528638020877086835886095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352425347251391223924063 3528638020877086835886095)
          ·
            refine ⟨5292957031315630253829143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528638020877086835886095 5292957031315630253829143)
            ·
              refine ⟨7939435546973445380743715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292957031315630253829143 7939435546973445380743715)
              ·
                refine ⟨11909153320460168071115573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7939435546973445380743715 11909153320460168071115573)
                ·
                  refine ⟨1116483123793140756667085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11909153320460168071115573 1116483123793140756667085)
                  ·
                    refine ⟨418681171422427783750157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116483123793140756667085 418681171422427783750157)
                    ·
                      refine ⟨157005439283410418906309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418681171422427783750157 157005439283410418906309)
                      ·
                        rfl

theorem cell23_305767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_305767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305767 prefixEnd_305767 := by exact prefixLift 305767
  have htrace : WordTrace (prefixWord ++ tailWord_305767) baseStart_305767 baseEnd_305767 := by
    simpa [prefixWord, tailWord_305767, baseEnd_305767] using wordTrace_append hprefix tailTrace_305767
  have hstable : (prefixWord ++ tailWord_305767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305767).length < 2 ^ (prefixWord ++ tailWord_305767).sum := by decide
  have hdescent : baseEnd_305767 < baseStart_305767 := by decide
  rcases family_descends (prefixWord ++ tailWord_305767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305774 : List Nat := [4, 1, 2, 2, 2, 3, 1, 8]
def baseStart_305774 : Nat := 118140960795 + 305774 * 2 ^ 59
def prefixEnd_305774 : Nat := 4983230072969 + 3 ^ 40 * 305774 * 2
def baseEnd_305774 : Nat := 5815149394370070056251

theorem tailTrace_305774 : CollatzResearch.WordTrace tailWord_305774 prefixEnd_305774 5815149394370070056251 := by
  unfold tailWord_305774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394061749280061860837547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7434995996160329924466917 1394061749280061860837547)
  ·
    refine ⟨2091092623920092791256321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1394061749280061860837547 2091092623920092791256321)
    ·
      refine ⟨1568319467940069593442241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2091092623920092791256321 1568319467940069593442241)
      ·
        refine ⟨1176239600955052195081681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568319467940069593442241 1176239600955052195081681)
        ·
          refine ⟨882179700716289146311261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176239600955052195081681 882179700716289146311261)
          ·
            refine ⟨330817387768608429866723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 882179700716289146311261 330817387768608429866723)
            ·
              refine ⟨496226081652912644800085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330817387768608429866723 496226081652912644800085)
              ·
                refine ⟨5815149394370070056251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 496226081652912644800085 5815149394370070056251)
                ·
                  rfl

theorem cell23_305774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_305774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305774 prefixEnd_305774 := by exact prefixLift 305774
  have htrace : WordTrace (prefixWord ++ tailWord_305774) baseStart_305774 baseEnd_305774 := by
    simpa [prefixWord, tailWord_305774, baseEnd_305774] using wordTrace_append hprefix tailTrace_305774
  have hstable : (prefixWord ++ tailWord_305774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305774).length < 2 ^ (prefixWord ++ tailWord_305774).sum := by decide
  have hdescent : baseEnd_305774 < baseStart_305774 := by decide
  rcases family_descends (prefixWord ++ tailWord_305774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305781 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_305781 : Nat := 118140960795 + 305781 * 2 ^ 59
def prefixEnd_305781 : Nat := 4983230072969 + 3 ^ 40 * 305781 * 2
def baseEnd_305781 : Nat := 157012628012573364131245

theorem tailTrace_305781 : CollatzResearch.WordTrace tailWord_305781 prefixEnd_305781 157012628012573364131245 := by
  unfold tailWord_305781
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152749305215135082205197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7435166203476756721470131 11152749305215135082205197)
  ·
    refine ⟨4182280989455675655826949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11152749305215135082205197 4182280989455675655826949)
    ·
      refine ⟨784177685522939185467553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4182280989455675655826949 784177685522939185467553)
      ·
        refine ⟨588133264142204389100665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 784177685522939185467553 588133264142204389100665)
        ·
          refine ⟨441099948106653291825499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588133264142204389100665 441099948106653291825499)
          ·
            refine ⟨661649922159979937738249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441099948106653291825499 661649922159979937738249)
            ·
              refine ⟨496237441619984953303687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661649922159979937738249 496237441619984953303687)
              ·
                refine ⟨744356162429977429955531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496237441619984953303687 744356162429977429955531)
                ·
                  refine ⟨1116534243644966144933297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744356162429977429955531 1116534243644966144933297)
                  ·
                    refine ⟨837400682733724608699973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1116534243644966144933297 837400682733724608699973)
                    ·
                      refine ⟨157012628012573364131245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 837400682733724608699973 157012628012573364131245)
                      ·
                        rfl

theorem cell23_305781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_305781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305781 prefixEnd_305781 := by exact prefixLift 305781
  have htrace : WordTrace (prefixWord ++ tailWord_305781) baseStart_305781 baseEnd_305781 := by
    simpa [prefixWord, tailWord_305781, baseEnd_305781] using wordTrace_append hprefix tailTrace_305781
  have hstable : (prefixWord ++ tailWord_305781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305781).length < 2 ^ (prefixWord ++ tailWord_305781).sum := by decide
  have hdescent : baseEnd_305781 < baseStart_305781 := by decide
  rcases family_descends (prefixWord ++ tailWord_305781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305818 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_305818 : Nat := 118140960795 + 305818 * 2 ^ 59
def prefixEnd_305818 : Nat := 4983230072969 + 3 ^ 40 * 305818 * 2
def baseEnd_305818 : Nat := 157031626796789719368575

theorem tailTrace_305818 : CollatzResearch.WordTrace tailWord_305818 prefixEnd_305818 157031626796789719368575 := by
  unfold tailWord_305818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788524701520272600325527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7436065870720726934201405 2788524701520272600325527)
  ·
    refine ⟨4182787052280408900488291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788524701520272600325527 4182787052280408900488291)
    ·
      refine ⟨6274180578420613350732437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182787052280408900488291 6274180578420613350732437)
      ·
        refine ⟨294102214613466250815583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6274180578420613350732437 294102214613466250815583)
        ·
          refine ⟨441153321920199376223375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294102214613466250815583 441153321920199376223375)
          ·
            refine ⟨661729982880299064335063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441153321920199376223375 661729982880299064335063)
            ·
              refine ⟨992594974320448596502595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661729982880299064335063 992594974320448596502595)
              ·
                refine ⟨1488892461480672894753893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992594974320448596502595 1488892461480672894753893)
                ·
                  refine ⟨279167336527626167766355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488892461480672894753893 279167336527626167766355)
                  ·
                    refine ⟨418751004791439251649533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 279167336527626167766355 418751004791439251649533)
                    ·
                      refine ⟨157031626796789719368575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418751004791439251649533 157031626796789719368575)
                      ·
                        rfl

theorem cell23_305818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_305818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305818 prefixEnd_305818 := by exact prefixLift 305818
  have htrace : WordTrace (prefixWord ++ tailWord_305818) baseStart_305818 baseEnd_305818 := by
    simpa [prefixWord, tailWord_305818, baseEnd_305818] using wordTrace_append hprefix tailTrace_305818
  have hstable : (prefixWord ++ tailWord_305818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305818).length < 2 ^ (prefixWord ++ tailWord_305818).sum := by decide
  have hdescent : baseEnd_305818 < baseStart_305818 := by decide
  rcases family_descends (prefixWord ++ tailWord_305818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305827 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 3]
def baseStart_305827 : Nat := 118140960795 + 305827 * 2 ^ 59
def prefixEnd_305827 : Nat := 4983230072969 + 3 ^ 40 * 305827 * 2
def baseEnd_305827 : Nat := 157036248122680184156033

theorem tailTrace_305827 : CollatzResearch.WordTrace tailWord_305827 prefixEnd_305827 157036248122680184156033 := by
  unfold tailWord_305827
  simp only [CollatzResearch.WordTrace]
  refine ⟨11154427063048484938379735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7436284708698989958919823 11154427063048484938379735)
  ·
    refine ⟨16731640594572727407569603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11154427063048484938379735 16731640594572727407569603)
    ·
      refine ⟨25097460891859091111354405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16731640594572727407569603 25097460891859091111354405)
      ·
        refine ⟨4705773917223579583378951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25097460891859091111354405 4705773917223579583378951)
        ·
          refine ⟨7058660875835369375068427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705773917223579583378951 7058660875835369375068427)
          ·
            refine ⟨10587991313753054062602641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058660875835369375068427 10587991313753054062602641)
            ·
              refine ⟨7940993485314790546951981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10587991313753054062602641 7940993485314790546951981)
              ·
                refine ⟨2977872556993046455106993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7940993485314790546951981 2977872556993046455106993)
                ·
                  refine ⟨2233404417744784841330245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2977872556993046455106993 2233404417744784841330245)
                  ·
                    refine ⟨418763328327147157749421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233404417744784841330245 418763328327147157749421)
                    ·
                      refine ⟨157036248122680184156033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418763328327147157749421 157036248122680184156033)
                      ·
                        rfl

theorem cell23_305827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_305827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305827 prefixEnd_305827 := by exact prefixLift 305827
  have htrace : WordTrace (prefixWord ++ tailWord_305827) baseStart_305827 baseEnd_305827 := by
    simpa [prefixWord, tailWord_305827, baseEnd_305827] using wordTrace_append hprefix tailTrace_305827
  have hstable : (prefixWord ++ tailWord_305827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305827).length < 2 ^ (prefixWord ++ tailWord_305827).sum := by decide
  have hdescent : baseEnd_305827 < baseStart_305827 := by decide
  rcases family_descends (prefixWord ++ tailWord_305827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305881 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 5]
def baseStart_305881 : Nat := 118140960795 + 305881 * 2 ^ 59
def prefixEnd_305881 : Nat := 4983230072969 + 3 ^ 40 * 305881 * 2
def baseEnd_305881 : Nat := 17451552897558108097865

theorem tailTrace_305881 : CollatzResearch.WordTrace tailWord_305881 prefixEnd_305881 17451552897558108097865 := by
  unfold tailWord_305881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156396604852852160845497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7437597736568568107230331 11156396604852852160845497)
  ·
    refine ⟨8367297453639639120634123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11156396604852852160845497 8367297453639639120634123)
    ·
      refine ⟨12550946180459458680951185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8367297453639639120634123 12550946180459458680951185)
      ·
        refine ⟨9413209635344594010713389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12550946180459458680951185 9413209635344594010713389)
        ·
          refine ⟨3529953613254222754017521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9413209635344594010713389 3529953613254222754017521)
          ·
            refine ⟨2647465209940667065513141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529953613254222754017521 2647465209940667065513141)
            ·
              refine ⟨248199863431937537391857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2647465209940667065513141 248199863431937537391857)
              ·
                refine ⟨186149897573953153043893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248199863431937537391857 186149897573953153043893)
                ·
                  refine ⟨17451552897558108097865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186149897573953153043893 17451552897558108097865)
                  ·
                    rfl

theorem cell23_305881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 5].length) (baseStart_305881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305881 prefixEnd_305881 := by exact prefixLift 305881
  have htrace : WordTrace (prefixWord ++ tailWord_305881) baseStart_305881 baseEnd_305881 := by
    simpa [prefixWord, tailWord_305881, baseEnd_305881] using wordTrace_append hprefix tailTrace_305881
  have hstable : (prefixWord ++ tailWord_305881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305881).length < 2 ^ (prefixWord ++ tailWord_305881).sum := by decide
  have hdescent : baseEnd_305881 < baseStart_305881 := by decide
  rcases family_descends (prefixWord ++ tailWord_305881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305887 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_305887 : Nat := 118140960795 + 305887 * 2 ^ 59
def prefixEnd_305887 : Nat := 4983230072969 + 3 ^ 40 * 305887 * 2
def baseEnd_305887 : Nat := 157067056961949949405757

theorem tailTrace_305887 : CollatzResearch.WordTrace tailWord_305887 prefixEnd_305887 157067056961949949405757 := by
  unfold tailWord_305887
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156615442831115185563915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7437743628554076790375943 11156615442831115185563915)
  ·
    refine ⟨16734923164246672778345873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11156615442831115185563915 16734923164246672778345873)
    ·
      refine ⟨12551192373185004583759405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16734923164246672778345873 12551192373185004583759405)
      ·
        refine ⟨4706697139944376718909777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12551192373185004583759405 4706697139944376718909777)
        ·
          refine ⟨3530022854958282539182333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4706697139944376718909777 3530022854958282539182333)
          ·
            refine ⟨1323758570609355952193375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3530022854958282539182333 1323758570609355952193375)
            ·
              refine ⟨1985637855914033928290063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323758570609355952193375 1985637855914033928290063)
              ·
                refine ⟨2978456783871050892435095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985637855914033928290063 2978456783871050892435095)
                ·
                  refine ⟨4467685175806576338652643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978456783871050892435095 4467685175806576338652643)
                  ·
                    refine ⟨6701527763709864507978965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4467685175806576338652643 6701527763709864507978965)
                    ·
                      refine ⟨157067056961949949405757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6701527763709864507978965 157067056961949949405757)
                      ·
                        rfl

theorem cell23_305887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_305887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305887 prefixEnd_305887 := by exact prefixLift 305887
  have htrace : WordTrace (prefixWord ++ tailWord_305887) baseStart_305887 baseEnd_305887 := by
    simpa [prefixWord, tailWord_305887, baseEnd_305887] using wordTrace_append hprefix tailTrace_305887
  have hstable : (prefixWord ++ tailWord_305887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305887).length < 2 ^ (prefixWord ++ tailWord_305887).sum := by decide
  have hdescent : baseEnd_305887 < baseStart_305887 := by decide
  rcases family_descends (prefixWord ++ tailWord_305887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305897 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_305897 : Nat := 118140960795 + 305897 * 2 ^ 59
def prefixEnd_305897 : Nat := 4983230072969 + 3 ^ 40 * 305897 * 2
def baseEnd_305897 : Nat := 157072191768494910280711

theorem tailTrace_305897 : CollatzResearch.WordTrace tailWord_305897 prefixEnd_305897 157072191768494910280711 := by
  unfold tailWord_305897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156980172794886893427945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7437986781863257928951963 11156980172794886893427945)
  ·
    refine ⟨8367735129596165170070959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11156980172794886893427945 8367735129596165170070959)
    ·
      refine ⟨12551602694394247755106439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8367735129596165170070959 12551602694394247755106439)
      ·
        refine ⟨18827404041591371632659659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12551602694394247755106439 18827404041591371632659659)
        ·
          refine ⟨28241106062387057448989489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18827404041591371632659659 28241106062387057448989489)
          ·
            refine ⟨21180829546790293086742117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28241106062387057448989489 21180829546790293086742117)
            ·
              refine ⟨3971405540023179953764147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21180829546790293086742117 3971405540023179953764147)
              ·
                refine ⟨5957108310034769930646221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971405540023179953764147 5957108310034769930646221)
                ·
                  refine ⟨2233915616263038723992333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5957108310034769930646221 2233915616263038723992333)
                  ·
                    refine ⟨837718356098639521497125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2233915616263038723992333 837718356098639521497125)
                    ·
                      refine ⟨157072191768494910280711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 837718356098639521497125 157072191768494910280711)
                      ·
                        rfl

theorem cell23_305897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_305897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305897 prefixEnd_305897 := by exact prefixLift 305897
  have htrace : WordTrace (prefixWord ++ tailWord_305897) baseStart_305897 baseEnd_305897 := by
    simpa [prefixWord, tailWord_305897, baseEnd_305897] using wordTrace_append hprefix tailTrace_305897
  have hstable : (prefixWord ++ tailWord_305897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305897).length < 2 ^ (prefixWord ++ tailWord_305897).sum := by decide
  have hdescent : baseEnd_305897 < baseStart_305897 := by decide
  rcases family_descends (prefixWord ++ tailWord_305897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305914 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_305914 : Nat := 118140960795 + 305914 * 2 ^ 59
def prefixEnd_305914 : Nat := 4983230072969 + 3 ^ 40 * 305914 * 2
def baseEnd_305914 : Nat := 157080920939621343768133

theorem tailTrace_305914 : CollatzResearch.WordTrace tailWord_305914 prefixEnd_305914 157080920939621343768133 := by
  unfold tailWord_305914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789400053433324699199199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7438400142488865864531197 2789400053433324699199199)
  ·
    refine ⟨4184100080149987048798799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2789400053433324699199199 4184100080149987048798799)
    ·
      refine ⟨6276150120224980573198199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4184100080149987048798799 6276150120224980573198199)
      ·
        refine ⟨9414225180337470859797299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276150120224980573198199 9414225180337470859797299)
        ·
          refine ⟨14121337770506206289695949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9414225180337470859797299 14121337770506206289695949)
          ·
            refine ⟨5295501663939827358635981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14121337770506206289695949 5295501663939827358635981)
            ·
              refine ⟨1985813123977435259488493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5295501663939827358635981 1985813123977435259488493)
              ·
                refine ⟨744679921491538222308185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1985813123977435259488493 744679921491538222308185)
                ·
                  refine ⟨558509941118653666731139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744679921491538222308185 558509941118653666731139)
                  ·
                    refine ⟨837764911677980500096709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558509941118653666731139 837764911677980500096709)
                    ·
                      refine ⟨157080920939621343768133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 837764911677980500096709 157080920939621343768133)
                      ·
                        rfl

theorem cell23_305914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_305914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305914 prefixEnd_305914 := by exact prefixLift 305914
  have htrace : WordTrace (prefixWord ++ tailWord_305914) baseStart_305914 baseEnd_305914 := by
    simpa [prefixWord, tailWord_305914, baseEnd_305914] using wordTrace_append hprefix tailTrace_305914
  have hstable : (prefixWord ++ tailWord_305914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305914).length < 2 ^ (prefixWord ++ tailWord_305914).sum := by decide
  have hdescent : baseEnd_305914 < baseStart_305914 := by decide
  rcases family_descends (prefixWord ++ tailWord_305914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305934 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_305934 : Nat := 118140960795 + 305934 * 2 ^ 59
def prefixEnd_305934 : Nat := 4983230072969 + 3 ^ 40 * 305934 * 2
def baseEnd_305934 : Nat := 157091190552711265518041

theorem tailTrace_305934 : CollatzResearch.WordTrace tailWord_305934 prefixEnd_305934 157091190552711265518041 := by
  unfold tailWord_305934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394791209207605276565607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7438886449107228141683237 1394791209207605276565607)
  ·
    refine ⟨2092186813811407914848411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1394791209207605276565607 2092186813811407914848411)
    ·
      refine ⟨3138280220717111872272617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092186813811407914848411 3138280220717111872272617)
      ·
        refine ⟨2353710165537833904204463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3138280220717111872272617 2353710165537833904204463)
        ·
          refine ⟨3530565248306750856306695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353710165537833904204463 3530565248306750856306695)
          ·
            refine ⟨5295847872460126284460043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530565248306750856306695 5295847872460126284460043)
            ·
              refine ⟨7943771808690189426690065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295847872460126284460043 7943771808690189426690065)
              ·
                refine ⟨5957828856517642070017549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7943771808690189426690065 5957828856517642070017549)
                ·
                  refine ⟨2234185821194115776256581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5957828856517642070017549 2234185821194115776256581)
                  ·
                    refine ⟨418909841473896708048109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2234185821194115776256581 418909841473896708048109)
                    ·
                      refine ⟨157091190552711265518041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 418909841473896708048109 157091190552711265518041)
                      ·
                        rfl

theorem cell23_305934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_305934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305934 prefixEnd_305934 := by exact prefixLift 305934
  have htrace : WordTrace (prefixWord ++ tailWord_305934) baseStart_305934 baseEnd_305934 := by
    simpa [prefixWord, tailWord_305934, baseEnd_305934] using wordTrace_append hprefix tailTrace_305934
  have hstable : (prefixWord ++ tailWord_305934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305934).length < 2 ^ (prefixWord ++ tailWord_305934).sum := by decide
  have hdescent : baseEnd_305934 < baseStart_305934 := by decide
  rcases family_descends (prefixWord ++ tailWord_305934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305937 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 8]
def baseStart_305937 : Nat := 118140960795 + 305937 * 2 ^ 59
def prefixEnd_305937 : Nat := 4983230072969 + 3 ^ 40 * 305937 * 2
def baseEnd_305937 : Nat := 17454747888297194864503

theorem tailTrace_305937 : CollatzResearch.WordTrace tailWord_305937 prefixEnd_305937 17454747888297194864503 := by
  unfold tailWord_305937
  simp only [CollatzResearch.WordTrace]
  refine ⟨11158439092649973724884065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7438959395099982483256043 11158439092649973724884065)
  ·
    refine ⟨8368829319487480293663049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11158439092649973724884065 8368829319487480293663049)
    ·
      refine ⟨6276621989615610220247287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8368829319487480293663049 6276621989615610220247287)
      ·
        refine ⟨9414932984423415330370931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276621989615610220247287 9414932984423415330370931)
        ·
          refine ⟨14122399476635122995556397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9414932984423415330370931 14122399476635122995556397)
          ·
            refine ⟨5295899803738171123333649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14122399476635122995556397 5295899803738171123333649)
            ·
              refine ⟨3971924852803628342500237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295899803738171123333649 3971924852803628342500237)
              ·
                refine ⟨1489471819801360628437589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3971924852803628342500237 1489471819801360628437589)
                ·
                  refine ⟨17454747888297194864503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1489471819801360628437589 17454747888297194864503)
                  ·
                    rfl

theorem cell23_305937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_305937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305937 prefixEnd_305937 := by exact prefixLift 305937
  have htrace : WordTrace (prefixWord ++ tailWord_305937) baseStart_305937 baseEnd_305937 := by
    simpa [prefixWord, tailWord_305937, baseEnd_305937] using wordTrace_append hprefix tailTrace_305937
  have hstable : (prefixWord ++ tailWord_305937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305937).length < 2 ^ (prefixWord ++ tailWord_305937).sum := by decide
  have hdescent : baseEnd_305937 < baseStart_305937 := by decide
  rcases family_descends (prefixWord ++ tailWord_305937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305988 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 8]
def baseStart_305988 : Nat := 118140960795 + 305988 * 2 ^ 59
def prefixEnd_305988 : Nat := 4983230072969 + 3 ^ 40 * 305988 * 2
def baseEnd_305988 : Nat := 17457657612006006026977

theorem tailTrace_305988 : CollatzResearch.WordTrace tailWord_305988 prefixEnd_305988 17457657612006006026977 := by
  unfold tailWord_305988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580149607732604717495309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7440199476976806289993745 5580149607732604717495309)
  ·
    refine ⟨2092556102899726769060741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5580149607732604717495309 2092556102899726769060741)
    ·
      refine ⟨392354269293698769198889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2092556102899726769060741 392354269293698769198889)
      ·
        refine ⟨294265701970274076899167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392354269293698769198889 294265701970274076899167)
        ·
          refine ⟨441398552955411115348751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294265701970274076899167 441398552955411115348751)
          ·
            refine ⟨662097829433116673023127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441398552955411115348751 662097829433116673023127)
            ·
              refine ⟨993146744149675009534691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662097829433116673023127 993146744149675009534691)
              ·
                refine ⟨1489720116224512514302037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993146744149675009534691 1489720116224512514302037)
                ·
                  refine ⟨17457657612006006026977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1489720116224512514302037 17457657612006006026977)
                  ·
                    rfl

theorem cell23_305988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_305988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305988 prefixEnd_305988 := by exact prefixLift 305988
  have htrace : WordTrace (prefixWord ++ tailWord_305988) baseStart_305988 baseEnd_305988 := by
    simpa [prefixWord, tailWord_305988, baseEnd_305988] using wordTrace_append hprefix tailTrace_305988
  have hstable : (prefixWord ++ tailWord_305988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305988).length < 2 ^ (prefixWord ++ tailWord_305988).sum := by decide
  have hdescent : baseEnd_305988 < baseStart_305988 := by decide
  rcases family_descends (prefixWord ++ tailWord_305988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305991 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_305991 : Nat := 118140960795 + 305991 * 2 ^ 59
def prefixEnd_305991 : Nat := 4983230072969 + 3 ^ 40 * 305991 * 2
def baseEnd_305991 : Nat := 157120458950017542505279

theorem tailTrace_305991 : CollatzResearch.WordTrace tailWord_305991 prefixEnd_305991 157120458950017542505279 := by
  unfold tailWord_305991
  simp only [CollatzResearch.WordTrace]
  refine ⟨11160408634454340947349827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7440272422969560631566551 11160408634454340947349827)
  ·
    refine ⟨16740612951681511421024741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11160408634454340947349827 16740612951681511421024741)
    ·
      refine ⟨3138864928440283391442139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16740612951681511421024741 3138864928440283391442139)
      ·
        refine ⟨4708297392660425087163209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138864928440283391442139 4708297392660425087163209)
        ·
          refine ⟨3531223044495318815372407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4708297392660425087163209 3531223044495318815372407)
          ·
            refine ⟨5296834566742978223058611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3531223044495318815372407 5296834566742978223058611)
            ·
              refine ⟨7945251850114467334587917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5296834566742978223058611 7945251850114467334587917)
              ·
                refine ⟨2979469443792925250470469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7945251850114467334587917 2979469443792925250470469)
                ·
                  refine ⟨558650520711173484463213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2979469443792925250470469 558650520711173484463213)
                  ·
                    refine ⟨209493945266690056673705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558650520711173484463213 209493945266690056673705)
                    ·
                      refine ⟨157120458950017542505279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209493945266690056673705 157120458950017542505279)
                      ·
                        rfl

theorem cell23_305991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_305991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_305991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_305991 prefixEnd_305991 := by exact prefixLift 305991
  have htrace : WordTrace (prefixWord ++ tailWord_305991) baseStart_305991 baseEnd_305991 := by
    simpa [prefixWord, tailWord_305991, baseEnd_305991] using wordTrace_append hprefix tailTrace_305991
  have hstable : (prefixWord ++ tailWord_305991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305991).length < 2 ^ (prefixWord ++ tailWord_305991).sum := by decide
  have hdescent : baseEnd_305991 < baseStart_305991 := by decide
  rcases family_descends (prefixWord ++ tailWord_305991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306021 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_306021 : Nat := 118140960795 + 306021 * 2 ^ 59
def prefixEnd_306021 : Nat := 4983230072969 + 3 ^ 40 * 306021 * 2
def baseEnd_306021 : Nat := 157135863369652425130141

theorem tailTrace_306021 : CollatzResearch.WordTrace tailWord_306021 prefixEnd_306021 157135863369652425130141 := by
  unfold tailWord_306021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11161502824345656070941917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441001882897104047294611 11161502824345656070941917)
  ·
    refine ⟨4185563559129621026603219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11161502824345656070941917 4185563559129621026603219)
    ·
      refine ⟨6278345338694431539904829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4185563559129621026603219 6278345338694431539904829)
      ·
        refine ⟨2354379502010411827464311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6278345338694431539904829 2354379502010411827464311)
        ·
          refine ⟨3531569253015617741196467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354379502010411827464311 3531569253015617741196467)
          ·
            refine ⟨5297353879523426611794701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3531569253015617741196467 5297353879523426611794701)
            ·
              refine ⟨1986507704821284979423013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5297353879523426611794701 1986507704821284979423013)
              ·
                refine ⟨372470194653990933641815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1986507704821284979423013 372470194653990933641815)
                ·
                  refine ⟨558705291980986400462723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372470194653990933641815 558705291980986400462723)
                  ·
                    refine ⟨838057937971479600694085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558705291980986400462723 838057937971479600694085)
                    ·
                      refine ⟨157135863369652425130141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 838057937971479600694085 157135863369652425130141)
                      ·
                        rfl

theorem cell23_306021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_306021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306021 prefixEnd_306021 := by exact prefixLift 306021
  have htrace : WordTrace (prefixWord ++ tailWord_306021) baseStart_306021 baseEnd_306021 := by
    simpa [prefixWord, tailWord_306021, baseEnd_306021] using wordTrace_append hprefix tailTrace_306021
  have hstable : (prefixWord ++ tailWord_306021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306021).length < 2 ^ (prefixWord ++ tailWord_306021).sum := by decide
  have hdescent : baseEnd_306021 < baseStart_306021 := by decide
  rcases family_descends (prefixWord ++ tailWord_306021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306041 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_306041 : Nat := 118140960795 + 306041 * 2 ^ 59
def prefixEnd_306041 : Nat := 4983230072969 + 3 ^ 40 * 306041 * 2
def baseEnd_306041 : Nat := 157146132982742346880049

theorem tailTrace_306041 : CollatzResearch.WordTrace tailWord_306041 prefixEnd_306041 157146132982742346880049 := by
  unfold tailWord_306041
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162232284273199486669977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441488189515466324446651 11162232284273199486669977)
  ·
    refine ⟨8371674213204899615002483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11162232284273199486669977 8371674213204899615002483)
    ·
      refine ⟨12557511319807349422503725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371674213204899615002483 12557511319807349422503725)
      ·
        refine ⟨4709066744927756033438897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12557511319807349422503725 4709066744927756033438897)
        ·
          refine ⟨3531800058695817025079173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4709066744927756033438897 3531800058695817025079173)
          ·
            refine ⟨662212511005465692202345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3531800058695817025079173 662212511005465692202345)
            ·
              refine ⟨496659383254099269151759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662212511005465692202345 496659383254099269151759)
              ·
                refine ⟨744989074881148903727639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496659383254099269151759 744989074881148903727639)
                ·
                  refine ⟨1117483612321723355591459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744989074881148903727639 1117483612321723355591459)
                  ·
                    refine ⟨1676225418482585033387189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1117483612321723355591459 1676225418482585033387189)
                    ·
                      refine ⟨157146132982742346880049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1676225418482585033387189 157146132982742346880049)
                      ·
                        rfl

theorem cell23_306041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_306041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306041 prefixEnd_306041 := by exact prefixLift 306041
  have htrace : WordTrace (prefixWord ++ tailWord_306041) baseStart_306041 baseEnd_306041 := by
    simpa [prefixWord, tailWord_306041, baseEnd_306041] using wordTrace_append hprefix tailTrace_306041
  have hstable : (prefixWord ++ tailWord_306041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306041).length < 2 ^ (prefixWord ++ tailWord_306041).sum := by decide
  have hdescent : baseEnd_306041 < baseStart_306041 := by decide
  rcases family_descends (prefixWord ++ tailWord_306041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306055 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_306055 : Nat := 118140960795 + 306055 * 2 ^ 59
def prefixEnd_306055 : Nat := 4983230072969 + 3 ^ 40 * 306055 * 2
def baseEnd_306055 : Nat := 157153321711905292104985

theorem tailTrace_306055 : CollatzResearch.WordTrace tailWord_306055 prefixEnd_306055 157153321711905292104985 := by
  unfold tailWord_306055
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162742906222479877679619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441828604148319918453079 11162742906222479877679619)
  ·
    refine ⟨16744114359333719816519429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11162742906222479877679619 16744114359333719816519429)
    ·
      refine ⟨3139521442375072465597393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16744114359333719816519429 3139521442375072465597393)
      ·
        refine ⟨2354641081781304349198045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3139521442375072465597393 2354641081781304349198045)
        ·
          refine ⟨882990405667989130949267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2354641081781304349198045 882990405667989130949267)
          ·
            refine ⟨1324485608501983696423901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882990405667989130949267 1324485608501983696423901)
            ·
              refine ⟨496682103188243886158963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1324485608501983696423901 496682103188243886158963)
              ·
                refine ⟨745023154782365829238445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496682103188243886158963 745023154782365829238445)
                ·
                  refine ⟨279383683043387185964417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745023154782365829238445 279383683043387185964417)
                  ·
                    refine ⟨209537762282540389473313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 279383683043387185964417 209537762282540389473313)
                    ·
                      refine ⟨157153321711905292104985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209537762282540389473313 157153321711905292104985)
                      ·
                        rfl

theorem cell23_306055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_306055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306055 prefixEnd_306055 := by exact prefixLift 306055
  have htrace : WordTrace (prefixWord ++ tailWord_306055) baseStart_306055 baseEnd_306055 := by
    simpa [prefixWord, tailWord_306055, baseEnd_306055] using wordTrace_append hprefix tailTrace_306055
  have hstable : (prefixWord ++ tailWord_306055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306055).length < 2 ^ (prefixWord ++ tailWord_306055).sum := by decide
  have hdescent : baseEnd_306055 < baseStart_306055 := by decide
  rcases family_descends (prefixWord ++ tailWord_306055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306071 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_306071 : Nat := 118140960795 + 306071 * 2 ^ 59
def prefixEnd_306071 : Nat := 4983230072969 + 3 ^ 40 * 306071 * 2
def baseEnd_306071 : Nat := 157161537402377229504911

theorem tailTrace_306071 : CollatzResearch.WordTrace tailWord_306071 prefixEnd_306071 157161537402377229504911 := by
  unfold tailWord_306071
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163326474164514610262067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7442217649443009740174711 11163326474164514610262067)
  ·
    refine ⟨16744989711246771915393101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11163326474164514610262067 16744989711246771915393101)
    ·
      refine ⟨6279371141717539468272413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16744989711246771915393101 6279371141717539468272413)
      ·
        refine ⟨2354764178144077300602155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6279371141717539468272413 2354764178144077300602155)
        ·
          refine ⟨3532146267216115950903233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354764178144077300602155 3532146267216115950903233)
          ·
            refine ⟨2649109700412086963177425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3532146267216115950903233 2649109700412086963177425)
            ·
              refine ⟨1986832275309065222383069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2649109700412086963177425 1986832275309065222383069)
              ·
                refine ⟨745062103240899458393651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1986832275309065222383069 745062103240899458393651)
                ·
                  refine ⟨1117593154861349187590477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745062103240899458393651 1117593154861349187590477)
                  ·
                    refine ⟨419097433073005945346429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117593154861349187590477 419097433073005945346429)
                    ·
                      refine ⟨157161537402377229504911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 419097433073005945346429 157161537402377229504911)
                      ·
                        rfl

theorem cell23_306071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_306071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306071 prefixEnd_306071 := by exact prefixLift 306071
  have htrace : WordTrace (prefixWord ++ tailWord_306071) baseStart_306071 baseEnd_306071 := by
    simpa [prefixWord, tailWord_306071, baseEnd_306071] using wordTrace_append hprefix tailTrace_306071
  have hstable : (prefixWord ++ tailWord_306071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306071).length < 2 ^ (prefixWord ++ tailWord_306071).sum := by decide
  have hdescent : baseEnd_306071 < baseStart_306071 := by decide
  rcases family_descends (prefixWord ++ tailWord_306071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306105 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 3]
def baseStart_306105 : Nat := 118140960795 + 306105 * 2 ^ 59
def prefixEnd_306105 : Nat := 4983230072969 + 3 ^ 40 * 306105 * 2
def baseEnd_306105 : Nat := 157178995744630096479755

theorem tailTrace_306105 : CollatzResearch.WordTrace tailWord_306105 prefixEnd_306105 157178995744630096479755 := by
  unfold tailWord_306105
  simp only [CollatzResearch.WordTrace]
  refine ⟨11164566556041338416999769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7443044370694225611333179 11164566556041338416999769)
  ·
    refine ⟨8373424917031003812749827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11164566556041338416999769 8373424917031003812749827)
    ·
      refine ⟨12560137375546505719124741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8373424917031003812749827 12560137375546505719124741)
      ·
        refine ⟨2355025757914969822335889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12560137375546505719124741 2355025757914969822335889)
        ·
          refine ⟨1766269318436227366751917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2355025757914969822335889 1766269318436227366751917)
          ·
            refine ⟨662350994413585262531969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1766269318436227366751917 662350994413585262531969)
            ·
              refine ⟨496763245810188946898977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662350994413585262531969 496763245810188946898977)
              ·
                refine ⟨372572434357641710174233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496763245810188946898977 372572434357641710174233)
                ·
                  refine ⟨279429325768231282630675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372572434357641710174233 279429325768231282630675)
                  ·
                    refine ⟨419143988652346923946013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 279429325768231282630675 419143988652346923946013)
                    ·
                      refine ⟨157178995744630096479755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 419143988652346923946013 157178995744630096479755)
                      ·
                        rfl

theorem cell23_306105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_306105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306105 prefixEnd_306105 := by exact prefixLift 306105
  have htrace : WordTrace (prefixWord ++ tailWord_306105) baseStart_306105 baseEnd_306105 := by
    simpa [prefixWord, tailWord_306105, baseEnd_306105] using wordTrace_append hprefix tailTrace_306105
  have hstable : (prefixWord ++ tailWord_306105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306105).length < 2 ^ (prefixWord ++ tailWord_306105).sum := by decide
  have hdescent : baseEnd_306105 < baseStart_306105 := by decide
  rcases family_descends (prefixWord ++ tailWord_306105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306128 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 6, 2, 2]
def baseStart_306128 : Nat := 118140960795 + 306128 * 2 ^ 59
def prefixEnd_306128 : Nat := 4983230072969 + 3 ^ 40 * 306128 * 2
def baseEnd_306128 : Nat := 157190805799683506492149

theorem tailTrace_306128 : CollatzResearch.WordTrace tailWord_306128 prefixEnd_306128 157190805799683506492149 := by
  unfold tailWord_306128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582702717479006672543519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7443603623305342230058025 5582702717479006672543519)
  ·
    refine ⟨8374054076218510008815279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5582702717479006672543519 8374054076218510008815279)
    ·
      refine ⟨12561081114327765013222919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8374054076218510008815279 12561081114327765013222919)
      ·
        refine ⟨18841621671491647519834379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12561081114327765013222919 18841621671491647519834379)
        ·
          refine ⟨28262432507237471279751569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18841621671491647519834379 28262432507237471279751569)
          ·
            refine ⟨21196824380428103459813677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28262432507237471279751569 21196824380428103459813677)
            ·
              refine ⟨7948809142660538797430129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21196824380428103459813677 7948809142660538797430129)
              ·
                refine ⟨5961606856995404098072597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7948809142660538797430129 5961606856995404098072597)
                ·
                  refine ⟨279450321421659567097153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5961606856995404098072597 279450321421659567097153)
                  ·
                    refine ⟨209587741066244675322865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 279450321421659567097153 209587741066244675322865)
                    ·
                      refine ⟨157190805799683506492149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209587741066244675322865 157190805799683506492149)
                      ·
                        rfl

theorem cell23_306128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 2, 2].length) (baseStart_306128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306128 prefixEnd_306128 := by exact prefixLift 306128
  have htrace : WordTrace (prefixWord ++ tailWord_306128) baseStart_306128 baseEnd_306128 := by
    simpa [prefixWord, tailWord_306128, baseEnd_306128] using wordTrace_append hprefix tailTrace_306128
  have hstable : (prefixWord ++ tailWord_306128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306128).length < 2 ^ (prefixWord ++ tailWord_306128).sum := by decide
  have hdescent : baseEnd_306128 < baseStart_306128 := by decide
  rcases family_descends (prefixWord ++ tailWord_306128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306144 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_306144 : Nat := 118140960795 + 306144 * 2 ^ 59
def prefixEnd_306144 : Nat := 4983230072969 + 3 ^ 40 * 306144 * 2
def baseEnd_306144 : Nat := 157199021490155443892075

theorem tailTrace_306144 : CollatzResearch.WordTrace tailWord_306144 prefixEnd_306144 157199021490155443892075 := by
  unfold tailWord_306144
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582994501450024038834743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7443992668600032051779657 5582994501450024038834743)
  ·
    refine ⟨8374491752175036058252115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5582994501450024038834743 8374491752175036058252115)
    ·
      refine ⟨12561737628262554087378173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8374491752175036058252115 12561737628262554087378173)
      ·
        refine ⟨4710651610598457782766815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12561737628262554087378173 4710651610598457782766815)
        ·
          refine ⟨7065977415897686674150223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710651610598457782766815 7065977415897686674150223)
          ·
            refine ⟨10598966123846530011225335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065977415897686674150223 10598966123846530011225335)
            ·
              refine ⟨15898449185769795016838003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10598966123846530011225335 15898449185769795016838003)
              ·
                refine ⟨23847673778654692525257005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15898449185769795016838003 23847673778654692525257005)
                ·
                  refine ⟨8942877666995509696971377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23847673778654692525257005 8942877666995509696971377)
                  ·
                    refine ⟨6707158250246632272728533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8942877666995509696971377 6707158250246632272728533)
                    ·
                      refine ⟨157199021490155443892075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6707158250246632272728533 157199021490155443892075)
                      ·
                        rfl

theorem cell23_306144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_306144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306144 prefixEnd_306144 := by exact prefixLift 306144
  have htrace : WordTrace (prefixWord ++ tailWord_306144) baseStart_306144 baseEnd_306144 := by
    simpa [prefixWord, tailWord_306144, baseEnd_306144] using wordTrace_append hprefix tailTrace_306144
  have hstable : (prefixWord ++ tailWord_306144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306144).length < 2 ^ (prefixWord ++ tailWord_306144).sum := by decide
  have hdescent : baseEnd_306144 < baseStart_306144 := by decide
  rcases family_descends (prefixWord ++ tailWord_306144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306201 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_306201 : Nat := 118140960795 + 306201 * 2 ^ 59
def prefixEnd_306201 : Nat := 4983230072969 + 3 ^ 40 * 306201 * 2
def baseEnd_306201 : Nat := 157228289887461720879313

theorem tailTrace_306201 : CollatzResearch.WordTrace tailWord_306201 prefixEnd_306201 157228289887461720879313 := by
  unfold tailWord_306201
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168067963693546812494457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7445378642462364541662971 11168067963693546812494457)
  ·
    refine ⟨8376050972770160109370843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11168067963693546812494457 8376050972770160109370843)
    ·
      refine ⟨12564076459155240164056265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8376050972770160109370843 12564076459155240164056265)
      ·
        refine ⟨9423057344366430123042199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12564076459155240164056265 9423057344366430123042199)
        ·
          refine ⟨14134586016549645184563299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9423057344366430123042199 14134586016549645184563299)
          ·
            refine ⟨21201879024824467776844949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14134586016549645184563299 21201879024824467776844949)
            ·
              refine ⟨993838079288646927039607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21201879024824467776844949 993838079288646927039607)
              ·
                refine ⟨1490757118932970390559411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993838079288646927039607 1490757118932970390559411)
                ·
                  refine ⟨2236135678399455585839117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490757118932970390559411 2236135678399455585839117)
                  ·
                    refine ⟨838550879399795844689669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2236135678399455585839117 838550879399795844689669)
                    ·
                      refine ⟨157228289887461720879313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 838550879399795844689669 157228289887461720879313)
                      ·
                        rfl

theorem cell23_306201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_306201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306201 prefixEnd_306201 := by exact prefixLift 306201
  have htrace : WordTrace (prefixWord ++ tailWord_306201) baseStart_306201 baseEnd_306201 := by
    simpa [prefixWord, tailWord_306201, baseEnd_306201] using wordTrace_append hprefix tailTrace_306201
  have hstable : (prefixWord ++ tailWord_306201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306201).length < 2 ^ (prefixWord ++ tailWord_306201).sum := by decide
  have hdescent : baseEnd_306201 < baseStart_306201 := by decide
  rcases family_descends (prefixWord ++ tailWord_306201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306215 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 2, 5]
def baseStart_306215 : Nat := 118140960795 + 306215 * 2 ^ 59
def prefixEnd_306215 : Nat := 4983230072969 + 3 ^ 40 * 306215 * 2
def baseEnd_306215 : Nat := 52411826205541555368083

theorem tailTrace_306215 : CollatzResearch.WordTrace tailWord_306215 prefixEnd_306215 52411826205541555368083 := by
  unfold tailWord_306215
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168578585642827203504099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7445719057095218135669399 11168578585642827203504099)
  ·
    refine ⟨16752867878464240805256149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11168578585642827203504099 16752867878464240805256149)
    ·
      refine ⟨392645340901505643873191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16752867878464240805256149 392645340901505643873191)
      ·
        refine ⟨588968011352258465809787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392645340901505643873191 588968011352258465809787)
        ·
          refine ⟨883452017028387698714681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588968011352258465809787 883452017028387698714681)
          ·
            refine ⟨662589012771290774036011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883452017028387698714681 662589012771290774036011)
            ·
              refine ⟨993883519156936161054017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662589012771290774036011 993883519156936161054017)
              ·
                refine ⟨745412639367702120790513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993883519156936161054017 745412639367702120790513)
                ·
                  refine ⟨559059479525776590592885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745412639367702120790513 559059479525776590592885)
                  ·
                    refine ⟨52411826205541555368083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 559059479525776590592885 52411826205541555368083)
                    ·
                      rfl

theorem cell23_306215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_306215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306215 prefixEnd_306215 := by exact prefixLift 306215
  have htrace : WordTrace (prefixWord ++ tailWord_306215) baseStart_306215 baseEnd_306215 := by
    simpa [prefixWord, tailWord_306215, baseEnd_306215] using wordTrace_append hprefix tailTrace_306215
  have hstable : (prefixWord ++ tailWord_306215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306215).length < 2 ^ (prefixWord ++ tailWord_306215).sum := by decide
  have hdescent : baseEnd_306215 < baseStart_306215 := by decide
  rcases family_descends (prefixWord ++ tailWord_306215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306279 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 1, 4]
def baseStart_306279 : Nat := 118140960795 + 306279 * 2 ^ 59
def prefixEnd_306279 : Nat := 4983230072969 + 3 ^ 40 * 306279 * 2
def baseEnd_306279 : Nat := 52422780459504138567985

theorem tailTrace_306279 : CollatzResearch.WordTrace tailWord_306279 prefixEnd_306279 52422780459504138567985 := by
  unfold tailWord_306279
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170912857410966133833891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7447275238273977422555927 11170912857410966133833891)
  ·
    refine ⟨16756369286116449200750837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11170912857410966133833891 16756369286116449200750837)
    ·
      refine ⟨1570909620573417112570391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16756369286116449200750837 1570909620573417112570391)
      ·
        refine ⟨2356364430860125668855587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570909620573417112570391 2356364430860125668855587)
        ·
          refine ⟨3534546646290188503283381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356364430860125668855587 3534546646290188503283381)
          ·
            refine ⟨331363748089705172182817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3534546646290188503283381 331363748089705172182817)
            ·
              refine ⟨248522811067278879137113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331363748089705172182817 248522811067278879137113)
              ·
                refine ⟨186392108300459159352835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248522811067278879137113 186392108300459159352835)
                ·
                  refine ⟨279588162450688739029253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186392108300459159352835 279588162450688739029253)
                  ·
                    refine ⟨52422780459504138567985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 279588162450688739029253 52422780459504138567985)
                    ·
                      rfl

theorem cell23_306279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_306279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306279 prefixEnd_306279 := by exact prefixLift 306279
  have htrace : WordTrace (prefixWord ++ tailWord_306279) baseStart_306279 baseEnd_306279 := by
    simpa [prefixWord, tailWord_306279, baseEnd_306279] using wordTrace_append hprefix tailTrace_306279
  have hstable : (prefixWord ++ tailWord_306279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306279).length < 2 ^ (prefixWord ++ tailWord_306279).sum := by decide
  have hdescent : baseEnd_306279 < baseStart_306279 := by decide
  rcases family_descends (prefixWord ++ tailWord_306279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306312 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_306312 : Nat := 118140960795 + 306312 * 2 ^ 59
def prefixEnd_306312 : Nat := 4983230072969 + 3 ^ 40 * 306312 * 2
def baseEnd_306312 : Nat := 157285286240110786591303

theorem tailTrace_306312 : CollatzResearch.WordTrace tailWord_306312 prefixEnd_306312 157285286240110786591303 := by
  unfold tailWord_306312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586058233145706384892595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7448077644194275179856793 5586058233145706384892595)
  ·
    refine ⟨8379087349718559577338893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5586058233145706384892595 8379087349718559577338893)
    ·
      refine ⟨3142157756144459841502085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8379087349718559577338893 3142157756144459841502085)
      ·
        refine ⟨589154579277086220281641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3142157756144459841502085 589154579277086220281641)
        ·
          refine ⟨441865934457814665211231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589154579277086220281641 441865934457814665211231)
          ·
            refine ⟨662798901686721997816847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441865934457814665211231 662798901686721997816847)
            ·
              refine ⟨994198352530082996725271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662798901686721997816847 994198352530082996725271)
              ·
                refine ⟨1491297528795124495087907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994198352530082996725271 1491297528795124495087907)
                ·
                  refine ⟨2236946293192686742631861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491297528795124495087907 2236946293192686742631861)
                  ·
                    refine ⟨209713714986814382121737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2236946293192686742631861 209713714986814382121737)
                    ·
                      refine ⟨157285286240110786591303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209713714986814382121737 157285286240110786591303)
                      ·
                        rfl

theorem cell23_306312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_306312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306312 prefixEnd_306312 := by exact prefixLift 306312
  have htrace : WordTrace (prefixWord ++ tailWord_306312) baseStart_306312 baseEnd_306312 := by
    simpa [prefixWord, tailWord_306312, baseEnd_306312] using wordTrace_append hprefix tailTrace_306312
  have hstable : (prefixWord ++ tailWord_306312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306312).length < 2 ^ (prefixWord ++ tailWord_306312).sum := by decide
  have hdescent : baseEnd_306312 < baseStart_306312 := by decide
  rcases family_descends (prefixWord ++ tailWord_306312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306322 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_306322 : Nat := 118140960795 + 306322 * 2 ^ 59
def prefixEnd_306322 : Nat := 4983230072969 + 3 ^ 40 * 306322 * 2
def baseEnd_306322 : Nat := 52430140348885249155419

theorem tailTrace_306322 : CollatzResearch.WordTrace tailWord_306322 prefixEnd_306322 52430140348885249155419 := by
  unfold tailWord_306322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793120299063796119412305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7448320797503456318432813 2793120299063796119412305)
  ·
    refine ⟨2094840224297847089559229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2793120299063796119412305 2094840224297847089559229)
    ·
      refine ⟨785565084111692658584711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2094840224297847089559229 785565084111692658584711)
      ·
        refine ⟨1178347626167538987877067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785565084111692658584711 1178347626167538987877067)
        ·
          refine ⟨1767521439251308481815601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178347626167538987877067 1767521439251308481815601)
          ·
            refine ⟨1325641079438481361361701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767521439251308481815601 1325641079438481361361701)
            ·
              refine ⟨248557702394715255255319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1325641079438481361361701 248557702394715255255319)
              ·
                refine ⟨372836553592072882882979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248557702394715255255319 372836553592072882882979)
                ·
                  refine ⟨559254830388109324324469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372836553592072882882979 559254830388109324324469)
                  ·
                    refine ⟨52430140348885249155419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 559254830388109324324469 52430140348885249155419)
                    ·
                      rfl

theorem cell23_306322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_306322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306322 prefixEnd_306322 := by exact prefixLift 306322
  have htrace : WordTrace (prefixWord ++ tailWord_306322) baseStart_306322 baseEnd_306322 := by
    simpa [prefixWord, tailWord_306322, baseEnd_306322] using wordTrace_append hprefix tailTrace_306322
  have hstable : (prefixWord ++ tailWord_306322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306322).length < 2 ^ (prefixWord ++ tailWord_306322).sum := by decide
  have hdescent : baseEnd_306322 < baseStart_306322 := by decide
  rcases family_descends (prefixWord ++ tailWord_306322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306370 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_306370 : Nat := 118140960795 + 306370 * 2 ^ 59
def prefixEnd_306370 : Nat := 4983230072969 + 3 ^ 40 * 306370 * 2
def baseEnd_306370 : Nat := 157315068118071559666037

theorem tailTrace_306370 : CollatzResearch.WordTrace tailWord_306370 prefixEnd_306370 157315068118071559666037 := by
  unfold tailWord_306370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793557975020322168849141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7449487933387525783597709 2793557975020322168849141)
  ·
    refine ⟨261896060158155203329607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2793557975020322168849141 261896060158155203329607)
    ·
      refine ⟨392844090237232804994411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261896060158155203329607 392844090237232804994411)
      ·
        refine ⟨589266135355849207491617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392844090237232804994411 589266135355849207491617)
        ·
          refine ⟨441949601516886905618713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589266135355849207491617 441949601516886905618713)
          ·
            refine ⟨331462201137665179214035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441949601516886905618713 331462201137665179214035)
            ·
              refine ⟨497193301706497768821053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331462201137665179214035 497193301706497768821053)
              ·
                refine ⟨186447488139936663307895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497193301706497768821053 186447488139936663307895)
                ·
                  refine ⟨279671232209904994961843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186447488139936663307895 279671232209904994961843)
                  ·
                    refine ⟨419506848314857492442765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 279671232209904994961843 419506848314857492442765)
                    ·
                      refine ⟨157315068118071559666037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 419506848314857492442765 157315068118071559666037)
                      ·
                        rfl

theorem cell23_306370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_306370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306370 prefixEnd_306370 := by exact prefixLift 306370
  have htrace : WordTrace (prefixWord ++ tailWord_306370) baseStart_306370 baseEnd_306370 := by
    simpa [prefixWord, tailWord_306370, baseEnd_306370] using wordTrace_append hprefix tailTrace_306370
  have hstable : (prefixWord ++ tailWord_306370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306370).length < 2 ^ (prefixWord ++ tailWord_306370).sum := by decide
  have hdescent : baseEnd_306370 < baseStart_306370 := by decide
  rcases family_descends (prefixWord ++ tailWord_306370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306385 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 5, 3, 2]
def baseStart_306385 : Nat := 118140960795 + 306385 * 2 ^ 59
def prefixEnd_306385 : Nat := 4983230072969 + 3 ^ 40 * 306385 * 2
def baseEnd_306385 : Nat := 157322770327889000978467

theorem tailTrace_306385 : CollatzResearch.WordTrace tailWord_306385 prefixEnd_306385 157322770327889000978467 := by
  unfold tailWord_306385
  simp only [CollatzResearch.WordTrace]
  refine ⟨11174778995026946237192609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7449852663351297491461739 11174778995026946237192609)
  ·
    refine ⟨8381084246270209677894457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11174778995026946237192609 8381084246270209677894457)
    ·
      refine ⟨6285813184702657258420843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8381084246270209677894457 6285813184702657258420843)
      ·
        refine ⟨9428719777053985887631265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6285813184702657258420843 9428719777053985887631265)
        ·
          refine ⟨7071539832790489415723449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9428719777053985887631265 7071539832790489415723449)
          ·
            refine ⟨5303654874592867061792587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071539832790489415723449 5303654874592867061792587)
            ·
              refine ⟨7955482311889300592688881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303654874592867061792587 7955482311889300592688881)
              ·
                refine ⟨5966611733916975444516661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7955482311889300592688881 5966611733916975444516661)
                ·
                  refine ⟨559369850054716447923437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5966611733916975444516661 559369850054716447923437)
                  ·
                    refine ⟨209763693770518667971289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559369850054716447923437 209763693770518667971289)
                    ·
                      refine ⟨157322770327889000978467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209763693770518667971289 157322770327889000978467)
                      ·
                        rfl

theorem cell23_306385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_306385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306385 prefixEnd_306385 := by exact prefixLift 306385
  have htrace : WordTrace (prefixWord ++ tailWord_306385) baseStart_306385 baseEnd_306385 := by
    simpa [prefixWord, tailWord_306385, baseEnd_306385] using wordTrace_append hprefix tailTrace_306385
  have hstable : (prefixWord ++ tailWord_306385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306385).length < 2 ^ (prefixWord ++ tailWord_306385).sum := by decide
  have hdescent : baseEnd_306385 < baseStart_306385 := by decide
  rcases family_descends (prefixWord ++ tailWord_306385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306408 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_306408 : Nat := 118140960795 + 306408 * 2 ^ 59
def prefixEnd_306408 : Nat := 4983230072969 + 3 ^ 40 * 306408 * 2
def baseEnd_306408 : Nat := 52444860127647470330287

theorem tailTrace_306408 : CollatzResearch.WordTrace tailWord_306408 prefixEnd_306408 52444860127647470330287 := by
  unfold tailWord_306408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587808936971810582639939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7450411915962414110186585 5587808936971810582639939)
  ·
    refine ⟨8381713405457715873959909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5587808936971810582639939 8381713405457715873959909)
    ·
      refine ⟨1571571263523321726367483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8381713405457715873959909 1571571263523321726367483)
      ·
        refine ⟨2357356895284982589551225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571571263523321726367483 2357356895284982589551225)
        ·
          refine ⟨1768017671463736942163419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2357356895284982589551225 1768017671463736942163419)
          ·
            refine ⟨2652026507195605413245129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768017671463736942163419 2652026507195605413245129)
            ·
              refine ⟨1989019880396704059933847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652026507195605413245129 1989019880396704059933847)
              ·
                refine ⟨2983529820595056089900771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989019880396704059933847 2983529820595056089900771)
                ·
                  refine ⟨4475294730892584134851157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983529820595056089900771 4475294730892584134851157)
                  ·
                    refine ⟨52444860127647470330287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4475294730892584134851157 52444860127647470330287)
                    ·
                      rfl

theorem cell23_306408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_306408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306408 prefixEnd_306408 := by exact prefixLift 306408
  have htrace : WordTrace (prefixWord ++ tailWord_306408) baseStart_306408 baseEnd_306408 := by
    simpa [prefixWord, tailWord_306408, baseEnd_306408] using wordTrace_append hprefix tailTrace_306408
  have hstable : (prefixWord ++ tailWord_306408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306408).length < 2 ^ (prefixWord ++ tailWord_306408).sum := by decide
  have hdescent : baseEnd_306408 < baseStart_306408 := by decide
  rcases family_descends (prefixWord ++ tailWord_306408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306419 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 1, 3, 2]
def baseStart_306419 : Nat := 118140960795 + 306419 * 2 ^ 59
def prefixEnd_306419 : Nat := 4983230072969 + 3 ^ 40 * 306419 * 2
def baseEnd_306419 : Nat := 157340228670141867953311

theorem tailTrace_306419 : CollatzResearch.WordTrace tailWord_306419 prefixEnd_306419 157340228670141867953311 := by
  unfold tailWord_306419
  simp only [CollatzResearch.WordTrace]
  refine ⟨11176019076903770043930311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7450679384602513362620207 11176019076903770043930311)
  ·
    refine ⟨16764028615355655065895467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11176019076903770043930311 16764028615355655065895467)
    ·
      refine ⟨25146042923033482598843201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16764028615355655065895467 25146042923033482598843201)
      ·
        refine ⟨18859532192275111949132401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25146042923033482598843201 18859532192275111949132401)
        ·
          refine ⟨14144649144206333961849301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18859532192275111949132401 14144649144206333961849301)
          ·
            refine ⟨331515214317335952230843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14144649144206333961849301 331515214317335952230843)
            ·
              refine ⟨497272821476003928346265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331515214317335952230843 497272821476003928346265)
              ·
                refine ⟨372954616107002946259699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497272821476003928346265 372954616107002946259699)
                ·
                  refine ⟨559431924160504419389549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372954616107002946259699 559431924160504419389549)
                  ·
                    refine ⟨209786971560189157271081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559431924160504419389549 209786971560189157271081)
                    ·
                      refine ⟨157340228670141867953311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209786971560189157271081 157340228670141867953311)
                      ·
                        rfl

theorem cell23_306419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 3, 2].length) (baseStart_306419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306419 prefixEnd_306419 := by exact prefixLift 306419
  have htrace : WordTrace (prefixWord ++ tailWord_306419) baseStart_306419 baseEnd_306419 := by
    simpa [prefixWord, tailWord_306419, baseEnd_306419] using wordTrace_append hprefix tailTrace_306419
  have hstable : (prefixWord ++ tailWord_306419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306419).length < 2 ^ (prefixWord ++ tailWord_306419).sum := by decide
  have hdescent : baseEnd_306419 < baseStart_306419 := by decide
  rcases family_descends (prefixWord ++ tailWord_306419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306436 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_306436 : Nat := 118140960795 + 306436 * 2 ^ 59
def prefixEnd_306436 : Nat := 4983230072969 + 3 ^ 40 * 306436 * 2
def baseEnd_306436 : Nat := 157348957841268301440733

theorem tailTrace_306436 : CollatzResearch.WordTrace tailWord_306436 prefixEnd_306436 157348957841268301440733 := by
  unfold tailWord_306436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588319558921090973649581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7451092745228121298199441 5588319558921090973649581)
  ·
    refine ⟨2095619834595409115118593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5588319558921090973649581 2095619834595409115118593)
    ·
      refine ⟨1571714875946556836338945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2095619834595409115118593 1571714875946556836338945)
      ·
        refine ⟨1178786156959917627254209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1571714875946556836338945 1178786156959917627254209)
        ·
          refine ⟨884089617719938220440657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178786156959917627254209 884089617719938220440657)
          ·
            refine ⟨663067213289953665330493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884089617719938220440657 663067213289953665330493)
            ·
              refine ⟨248650204983732624498935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663067213289953665330493 248650204983732624498935)
              ·
                refine ⟨372975307475598936748403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248650204983732624498935 372975307475598936748403)
                ·
                  refine ⟨559462961213398405122605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372975307475598936748403 559462961213398405122605)
                  ·
                    refine ⟨209798610455024401920977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559462961213398405122605 209798610455024401920977)
                    ·
                      refine ⟨157348957841268301440733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209798610455024401920977 157348957841268301440733)
                      ·
                        rfl

theorem cell23_306436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_306436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306436 prefixEnd_306436 := by exact prefixLift 306436
  have htrace : WordTrace (prefixWord ++ tailWord_306436) baseStart_306436 baseEnd_306436 := by
    simpa [prefixWord, tailWord_306436, baseEnd_306436] using wordTrace_append hprefix tailTrace_306436
  have hstable : (prefixWord ++ tailWord_306436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306436).length < 2 ^ (prefixWord ++ tailWord_306436).sum := by decide
  have hdescent : baseEnd_306436 < baseStart_306436 := by decide
  rcases family_descends (prefixWord ++ tailWord_306436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306449 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 2, 2, 2]
def baseStart_306449 : Nat := 118140960795 + 306449 * 2 ^ 59
def prefixEnd_306449 : Nat := 4983230072969 + 3 ^ 40 * 306449 * 2
def baseEnd_306449 : Nat := 157355633089776750578173

theorem tailTrace_306449 : CollatzResearch.WordTrace tailWord_306449 prefixEnd_306449 157355633089776750578173 := by
  unfold tailWord_306449
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177113266795085167522401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7451408844530056778348267 11177113266795085167522401)
  ·
    refine ⟨8382834950096313875641801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11177113266795085167522401 8382834950096313875641801)
    ·
      refine ⟨6287126212572235406731351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8382834950096313875641801 6287126212572235406731351)
      ·
        refine ⟨9430689318858353110097027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287126212572235406731351 9430689318858353110097027)
        ·
          refine ⟨14146033978287529665145541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9430689318858353110097027 14146033978287529665145541)
          ·
            refine ⟨2652381370928911812214789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14146033978287529665145541 2652381370928911812214789)
            ·
              refine ⟨497321507049170964790273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2652381370928911812214789 497321507049170964790273)
              ·
                refine ⟨372991130286878223592705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497321507049170964790273 372991130286878223592705)
                ·
                  refine ⟨279743347715158667694529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372991130286878223592705 279743347715158667694529)
                  ·
                    refine ⟨209807510786369000770897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 279743347715158667694529 209807510786369000770897)
                    ·
                      refine ⟨157355633089776750578173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209807510786369000770897 157355633089776750578173)
                      ·
                        rfl

theorem cell23_306449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_306449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306449 prefixEnd_306449 := by exact prefixLift 306449
  have htrace : WordTrace (prefixWord ++ tailWord_306449) baseStart_306449 baseEnd_306449 := by
    simpa [prefixWord, tailWord_306449, baseEnd_306449] using wordTrace_append hprefix tailTrace_306449
  have hstable : (prefixWord ++ tailWord_306449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306449).length < 2 ^ (prefixWord ++ tailWord_306449).sum := by decide
  have hdescent : baseEnd_306449 < baseStart_306449 := by decide
  rcases family_descends (prefixWord ++ tailWord_306449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306485 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_306485 : Nat := 118140960795 + 306485 * 2 ^ 59
def prefixEnd_306485 : Nat := 4983230072969 + 3 ^ 40 * 306485 * 2
def baseEnd_306485 : Nat := 52458039464446203242669

theorem tailTrace_306485 : CollatzResearch.WordTrace tailWord_306485 prefixEnd_306485 52458039464446203242669 := by
  unfold tailWord_306485
  simp only [CollatzResearch.WordTrace]
  refine ⟨11178426294664663315832909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7452284196443108877221939 11178426294664663315832909)
  ·
    refine ⟨4191909860499248743437341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11178426294664663315832909 4191909860499248743437341)
    ·
      refine ⟨1571966197687218278789003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4191909860499248743437341 1571966197687218278789003)
      ·
        refine ⟨2357949296530827418183505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571966197687218278789003 2357949296530827418183505)
        ·
          refine ⟨1768461972398120563637629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2357949296530827418183505 1768461972398120563637629)
          ·
            refine ⟨663173239649295211364111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1768461972398120563637629 663173239649295211364111)
            ·
              refine ⟨994759859473942817046167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663173239649295211364111 994759859473942817046167)
              ·
                refine ⟨1492139789210914225569251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994759859473942817046167 1492139789210914225569251)
                ·
                  refine ⟨2238209683816371338353877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492139789210914225569251 2238209683816371338353877)
                  ·
                    refine ⟨52458039464446203242669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2238209683816371338353877 52458039464446203242669)
                    ·
                      rfl

theorem cell23_306485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_306485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306485 prefixEnd_306485 := by exact prefixLift 306485
  have htrace : WordTrace (prefixWord ++ tailWord_306485) baseStart_306485 baseEnd_306485 := by
    simpa [prefixWord, tailWord_306485, baseEnd_306485] using wordTrace_append hprefix tailTrace_306485
  have hstable : (prefixWord ++ tailWord_306485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306485).length < 2 ^ (prefixWord ++ tailWord_306485).sum := by decide
  have hdescent : baseEnd_306485 < baseStart_306485 := by decide
  rcases family_descends (prefixWord ++ tailWord_306485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306489 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 5]
def baseStart_306489 : Nat := 118140960795 + 306489 * 2 ^ 59
def prefixEnd_306489 : Nat := 4983230072969 + 3 ^ 40 * 306489 * 2
def baseEnd_306489 : Nat := 17486241368439621564221

theorem tailTrace_306489 : CollatzResearch.WordTrace tailWord_306489 prefixEnd_306489 17486241368439621564221 := by
  unfold tailWord_306489
  simp only [CollatzResearch.WordTrace]
  refine ⟨11178572186650171998978521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7452381457766781332652347 11178572186650171998978521)
  ·
    refine ⟨8383929139987628999233891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11178572186650171998978521 8383929139987628999233891)
    ·
      refine ⟨12575893709981443498850837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8383929139987628999233891 12575893709981443498850837)
      ·
        refine ⟨589495017655380164008633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12575893709981443498850837 589495017655380164008633)
        ·
          refine ⟨442121263241535123006475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589495017655380164008633 442121263241535123006475)
          ·
            refine ⟨663181894862302684509713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442121263241535123006475 663181894862302684509713)
            ·
              refine ⟨497386421146727013382285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663181894862302684509713 497386421146727013382285)
              ·
                refine ⟨186519907930022630018357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497386421146727013382285 186519907930022630018357)
                ·
                  refine ⟨17486241368439621564221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186519907930022630018357 17486241368439621564221)
                  ·
                    rfl

theorem cell23_306489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 5].length) (baseStart_306489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306489 prefixEnd_306489 := by exact prefixLift 306489
  have htrace : WordTrace (prefixWord ++ tailWord_306489) baseStart_306489 baseEnd_306489 := by
    simpa [prefixWord, tailWord_306489, baseEnd_306489] using wordTrace_append hprefix tailTrace_306489
  have hstable : (prefixWord ++ tailWord_306489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306489).length < 2 ^ (prefixWord ++ tailWord_306489).sum := by decide
  have hdescent : baseEnd_306489 < baseStart_306489 := by decide
  rcases family_descends (prefixWord ++ tailWord_306489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306505 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_306505 : Nat := 118140960795 + 306505 * 2 ^ 59
def prefixEnd_306505 : Nat := 4983230072969 + 3 ^ 40 * 306505 * 2
def baseEnd_306505 : Nat := 157384388006428531477915

theorem tailTrace_306505 : CollatzResearch.WordTrace tailWord_306505 prefixEnd_306505 157384388006428531477915 := by
  unfold tailWord_306505
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179155754592206731560969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7452770503061471154373979 11179155754592206731560969)
  ·
    refine ⟨8384366815944155048670727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11179155754592206731560969 8384366815944155048670727)
    ·
      refine ⟨12576550223916232573006091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8384366815944155048670727 12576550223916232573006091)
      ·
        refine ⟨18864825335874348859509137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12576550223916232573006091 18864825335874348859509137)
        ·
          refine ⟨14148619001905761644631853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18864825335874348859509137 14148619001905761644631853)
          ·
            refine ⟨5305732125714660616736945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14148619001905761644631853 5305732125714660616736945)
            ·
              refine ⟨3979299094285995462552709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305732125714660616736945 3979299094285995462552709)
              ·
                refine ⟨746118580178624149228633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3979299094285995462552709 746118580178624149228633)
                ·
                  refine ⟨559588935133968111921475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 746118580178624149228633 559588935133968111921475)
                  ·
                    refine ⟨839383402700952167882213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 559588935133968111921475 839383402700952167882213)
                    ·
                      refine ⟨157384388006428531477915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 839383402700952167882213 157384388006428531477915)
                      ·
                        rfl

theorem cell23_306505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_306505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306505 prefixEnd_306505 := by exact prefixLift 306505
  have htrace : WordTrace (prefixWord ++ tailWord_306505) baseStart_306505 baseEnd_306505 := by
    simpa [prefixWord, tailWord_306505, baseEnd_306505] using wordTrace_append hprefix tailTrace_306505
  have hstable : (prefixWord ++ tailWord_306505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306505).length < 2 ^ (prefixWord ++ tailWord_306505).sum := by decide
  have hdescent : baseEnd_306505 < baseStart_306505 := by decide
  rcases family_descends (prefixWord ++ tailWord_306505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306522 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2]
def baseStart_306522 : Nat := 118140960795 + 306522 * 2 ^ 59
def prefixEnd_306522 : Nat := 4983230072969 + 3 ^ 40 * 306522 * 2
def baseEnd_306522 : Nat := 157393117177554964965337

theorem tailTrace_306522 : CollatzResearch.WordTrace tailWord_306522 prefixEnd_306522 157393117177554964965337 := by
  unfold tailWord_306522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794943948882654658732455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7453183863687079089953213 2794943948882654658732455)
  ·
    refine ⟨4192415923323981988098683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794943948882654658732455 4192415923323981988098683)
    ·
      refine ⟨6288623884985972982148025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192415923323981988098683 6288623884985972982148025)
      ·
        refine ⟨4716467913739479736611019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6288623884985972982148025 4716467913739479736611019)
        ·
          refine ⟨7074701870609219604916529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716467913739479736611019 7074701870609219604916529)
          ·
            refine ⟨5306026402956914703687397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7074701870609219604916529 5306026402956914703687397)
            ·
              refine ⟨994879950554421506941387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5306026402956914703687397 994879950554421506941387)
              ·
                refine ⟨1492319925831632260412081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994879950554421506941387 1492319925831632260412081)
                ·
                  refine ⟨1119239944373724195309061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1492319925831632260412081 1119239944373724195309061)
                  ·
                    refine ⟨209857489570073286620449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119239944373724195309061 209857489570073286620449)
                    ·
                      refine ⟨157393117177554964965337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209857489570073286620449 157393117177554964965337)
                      ·
                        rfl

theorem cell23_306522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_306522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306522 prefixEnd_306522 := by exact prefixLift 306522
  have htrace : WordTrace (prefixWord ++ tailWord_306522) baseStart_306522 baseEnd_306522 := by
    simpa [prefixWord, tailWord_306522, baseEnd_306522] using wordTrace_append hprefix tailTrace_306522
  have hstable : (prefixWord ++ tailWord_306522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306522).length < 2 ^ (prefixWord ++ tailWord_306522).sum := by decide
  have hdescent : baseEnd_306522 < baseStart_306522 := by decide
  rcases family_descends (prefixWord ++ tailWord_306522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306532 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_306532 : Nat := 118140960795 + 306532 * 2 ^ 59
def prefixEnd_306532 : Nat := 4983230072969 + 3 ^ 40 * 306532 * 2
def baseEnd_306532 : Nat := 52466083994699975280097

theorem tailTrace_306532 : CollatzResearch.WordTrace tailWord_306532 prefixEnd_306532 52466083994699975280097 := by
  unfold tailWord_306532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5590070262747195171396925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7453427016996260228529233 5590070262747195171396925)
  ·
    refine ⟨2096276348530198189273847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5590070262747195171396925 2096276348530198189273847)
    ·
      refine ⟨3144414522795297283910771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096276348530198189273847 3144414522795297283910771)
      ·
        refine ⟨4716621784192945925866157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144414522795297283910771 4716621784192945925866157)
        ·
          refine ⟨1768733169072354722199809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4716621784192945925866157 1768733169072354722199809)
          ·
            refine ⟨1326549876804266041649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1768733169072354722199809 1326549876804266041649857)
            ·
              refine ⟨994912407603199531237393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326549876804266041649857 994912407603199531237393)
              ·
                refine ⟨746184305702399648428045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994912407603199531237393 746184305702399648428045)
                ·
                  refine ⟨279819114638399868160517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746184305702399648428045 279819114638399868160517)
                  ·
                    refine ⟨52466083994699975280097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 279819114638399868160517 52466083994699975280097)
                    ·
                      rfl

theorem cell23_306532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_306532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306532 prefixEnd_306532 := by exact prefixLift 306532
  have htrace : WordTrace (prefixWord ++ tailWord_306532) baseStart_306532 baseEnd_306532 := by
    simpa [prefixWord, tailWord_306532, baseEnd_306532] using wordTrace_append hprefix tailTrace_306532
  have hstable : (prefixWord ++ tailWord_306532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306532).length < 2 ^ (prefixWord ++ tailWord_306532).sum := by decide
  have hdescent : baseEnd_306532 < baseStart_306532 := by decide
  rcases family_descends (prefixWord ++ tailWord_306532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306609 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 1, 5]
def baseStart_306609 : Nat := 118140960795 + 306609 * 2 ^ 59
def prefixEnd_306609 : Nat := 4983230072969 + 3 ^ 40 * 306609 * 2
def baseEnd_306609 : Nat := 52479263331498708192479

theorem tailTrace_306609 : CollatzResearch.WordTrace tailWord_306609 prefixEnd_306609 52479263331498708192479 := by
  unfold tailWord_306609
  simp only [CollatzResearch.WordTrace]
  refine ⟨11182948946215432493346881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7455299297476954995564587 11182948946215432493346881)
  ·
    refine ⟨8387211709661574370010161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11182948946215432493346881 8387211709661574370010161)
    ·
      refine ⟨6290408782246180777507621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8387211709661574370010161 6290408782246180777507621)
      ·
        refine ⟨1179451646671158895782679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6290408782246180777507621 1179451646671158895782679)
        ·
          refine ⟨1769177470006738343674019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179451646671158895782679 1769177470006738343674019)
          ·
            refine ⟨2653766205010107515511029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769177470006738343674019 2653766205010107515511029)
            ·
              refine ⟨248790581719697579579159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2653766205010107515511029 248790581719697579579159)
              ·
                refine ⟨373185872579546369368739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248790581719697579579159 373185872579546369368739)
                ·
                  refine ⟨559778808869319554053109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373185872579546369368739 559778808869319554053109)
                  ·
                    refine ⟨52479263331498708192479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 559778808869319554053109 52479263331498708192479)
                    ·
                      rfl

theorem cell23_306609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_306609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306609 prefixEnd_306609 := by exact prefixLift 306609
  have htrace : WordTrace (prefixWord ++ tailWord_306609) baseStart_306609 baseEnd_306609 := by
    simpa [prefixWord, tailWord_306609, baseEnd_306609] using wordTrace_append hprefix tailTrace_306609
  have hstable : (prefixWord ++ tailWord_306609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306609).length < 2 ^ (prefixWord ++ tailWord_306609).sum := by decide
  have hdescent : baseEnd_306609 < baseStart_306609 := by decide
  rcases family_descends (prefixWord ++ tailWord_306609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306632 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_306632 : Nat := 118140960795 + 306632 * 2 ^ 59
def prefixEnd_306632 : Nat := 4983230072969 + 3 ^ 40 * 306632 * 2
def baseEnd_306632 : Nat := 157449600049549534589831

theorem tailTrace_306632 : CollatzResearch.WordTrace tailWord_306632 prefixEnd_306632 157449600049549534589831 := by
  unfold tailWord_306632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591893912566053710717075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7455858550088071614289433 5591893912566053710717075)
  ·
    refine ⟨8387840868849080566075613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5591893912566053710717075 8387840868849080566075613)
    ·
      refine ⟨3145440325818405212278355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8387840868849080566075613 3145440325818405212278355)
      ·
        refine ⟨4718160488727607818417533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145440325818405212278355 4718160488727607818417533)
        ·
          refine ⟨1769310183272852931906575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4718160488727607818417533 1769310183272852931906575)
          ·
            refine ⟨2653965274909279397859863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769310183272852931906575 2653965274909279397859863)
            ·
              refine ⟨3980947912363919096789795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653965274909279397859863 3980947912363919096789795)
              ·
                refine ⟨5971421868545878645184693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980947912363919096789795 5971421868545878645184693)
                ·
                  refine ⟨559820800176176122986065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5971421868545878645184693 559820800176176122986065)
                  ·
                    refine ⟨419865600132132092239549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559820800176176122986065 419865600132132092239549)
                    ·
                      refine ⟨157449600049549534589831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 419865600132132092239549 157449600049549534589831)
                      ·
                        rfl

theorem cell23_306632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_306632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306632 prefixEnd_306632 := by exact prefixLift 306632
  have htrace : WordTrace (prefixWord ++ tailWord_306632) baseStart_306632 baseEnd_306632 := by
    simpa [prefixWord, tailWord_306632, baseEnd_306632] using wordTrace_append hprefix tailTrace_306632
  have hstable : (prefixWord ++ tailWord_306632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306632).length < 2 ^ (prefixWord ++ tailWord_306632).sum := by decide
  have hdescent : baseEnd_306632 < baseStart_306632 := by decide
  rcases family_descends (prefixWord ++ tailWord_306632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306635 : List Nat := [1, 1, 1, 1, 3, 3, 5, 8]
def baseStart_306635 : Nat := 118140960795 + 306635 * 2 ^ 59
def prefixEnd_306635 : Nat := 4983230072969 + 3 ^ 40 * 306635 * 2
def baseEnd_306635 : Nat := 5831523721907889735271

theorem tailTrace_306635 : CollatzResearch.WordTrace tailWord_306635 prefixEnd_306635 5831523721907889735271 := by
  unfold tailWord_306635
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183897244121238933793359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7455931496080825955862239 11183897244121238933793359)
  ·
    refine ⟨16775845866181858400690039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11183897244121238933793359 16775845866181858400690039)
    ·
      refine ⟨25163768799272787601035059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16775845866181858400690039 25163768799272787601035059)
      ·
        refine ⟨37745653198909181401552589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25163768799272787601035059 37745653198909181401552589)
        ·
          refine ⟨14154619949590943025582221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37745653198909181401552589 14154619949590943025582221)
          ·
            refine ⟨5307982481096603634593333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14154619949590943025582221 5307982481096603634593333)
            ·
              refine ⟨497623357602806590743125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5307982481096603634593333 497623357602806590743125)
              ·
                refine ⟨5831523721907889735271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 497623357602806590743125 5831523721907889735271)
                ·
                  rfl

theorem cell23_306635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 8].length) (baseStart_306635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306635 prefixEnd_306635 := by exact prefixLift 306635
  have htrace : WordTrace (prefixWord ++ tailWord_306635) baseStart_306635 baseEnd_306635 := by
    simpa [prefixWord, tailWord_306635, baseEnd_306635] using wordTrace_append hprefix tailTrace_306635
  have hstable : (prefixWord ++ tailWord_306635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306635).length < 2 ^ (prefixWord ++ tailWord_306635).sum := by decide
  have hdescent : baseEnd_306635 < baseStart_306635 := by decide
  rcases family_descends (prefixWord ++ tailWord_306635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306663 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_306663 : Nat := 118140960795 + 306663 * 2 ^ 59
def prefixEnd_306663 : Nat := 4983230072969 + 3 ^ 40 * 306663 * 2
def baseEnd_306663 : Nat := 157465517949838913302189

theorem tailTrace_306663 : CollatzResearch.WordTrace tailWord_306663 prefixEnd_306663 157465517949838913302189 := by
  unfold tailWord_306663
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184918488019799715812643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7456612325346533143875095 11184918488019799715812643)
  ·
    refine ⟨16777377732029699573718965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11184918488019799715812643 16777377732029699573718965)
    ·
      refine ⟨1572879162377784335036153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16777377732029699573718965 1572879162377784335036153)
      ·
        refine ⟨1179659371783338251277115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1572879162377784335036153 1179659371783338251277115)
        ·
          refine ⟨1769489057675007376915673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179659371783338251277115 1769489057675007376915673)
          ·
            refine ⟨1327116793256255532686755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1769489057675007376915673 1327116793256255532686755)
            ·
              refine ⟨1990675189884383299030133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1327116793256255532686755 1990675189884383299030133)
              ·
                refine ⟨186625799051660934284075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1990675189884383299030133 186625799051660934284075)
                ·
                  refine ⟨279938698577491401426113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186625799051660934284075 279938698577491401426113)
                  ·
                    refine ⟨209954023933118551069585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 279938698577491401426113 209954023933118551069585)
                    ·
                      refine ⟨157465517949838913302189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209954023933118551069585 157465517949838913302189)
                      ·
                        rfl

theorem cell23_306663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_306663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306663 prefixEnd_306663 := by exact prefixLift 306663
  have htrace : WordTrace (prefixWord ++ tailWord_306663) baseStart_306663 baseEnd_306663 := by
    simpa [prefixWord, tailWord_306663, baseEnd_306663] using wordTrace_append hprefix tailTrace_306663
  have hstable : (prefixWord ++ tailWord_306663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306663).length < 2 ^ (prefixWord ++ tailWord_306663).sum := by decide
  have hdescent : baseEnd_306663 < baseStart_306663 := by decide
  rcases family_descends (prefixWord ++ tailWord_306663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306666 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_306666 : Nat := 118140960795 + 306666 * 2 ^ 59
def prefixEnd_306666 : Nat := 4983230072969 + 3 ^ 40 * 306666 * 2
def baseEnd_306666 : Nat := 157467058391802401564675

theorem tailTrace_306666 : CollatzResearch.WordTrace tailWord_306666 prefixEnd_306666 157467058391802401564675 := by
  unfold tailWord_306666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796256976752232807042963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7456685271339287485447901 2796256976752232807042963)
  ·
    refine ⟨4194385465128349210564445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2796256976752232807042963 4194385465128349210564445)
    ·
      refine ⟨1572894549423130953961667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4194385465128349210564445 1572894549423130953961667)
      ·
        refine ⟨2359341824134696430942501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572894549423130953961667 2359341824134696430942501)
        ·
          refine ⟨442376592025255580801719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2359341824134696430942501 442376592025255580801719)
          ·
            refine ⟨663564888037883371202579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442376592025255580801719 663564888037883371202579)
            ·
              refine ⟨995347332056825056803869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663564888037883371202579 995347332056825056803869)
              ·
                refine ⟨373255249521309396301451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995347332056825056803869 373255249521309396301451)
                ·
                  refine ⟨559882874281964094452177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373255249521309396301451 559882874281964094452177)
                  ·
                    refine ⟨419912155711473070839133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559882874281964094452177 419912155711473070839133)
                    ·
                      refine ⟨157467058391802401564675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 419912155711473070839133 157467058391802401564675)
                      ·
                        rfl

theorem cell23_306666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_306666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306666 prefixEnd_306666 := by exact prefixLift 306666
  have htrace : WordTrace (prefixWord ++ tailWord_306666) baseStart_306666 baseEnd_306666 := by
    simpa [prefixWord, tailWord_306666, baseEnd_306666] using wordTrace_append hprefix tailTrace_306666
  have hstable : (prefixWord ++ tailWord_306666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306666).length < 2 ^ (prefixWord ++ tailWord_306666).sum := by decide
  have hdescent : baseEnd_306666 < baseStart_306666 := by decide
  rcases family_descends (prefixWord ++ tailWord_306666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306675 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_306675 : Nat := 118140960795 + 306675 * 2 ^ 59
def prefixEnd_306675 : Nat := 4983230072969 + 3 ^ 40 * 306675 * 2
def baseEnd_306675 : Nat := 157471679717692866352133

theorem tailTrace_306675 : CollatzResearch.WordTrace tailWord_306675 prefixEnd_306675 157471679717692866352133 := by
  unfold tailWord_306675
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185356163976325765249479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7456904109317550510166319 11185356163976325765249479)
  ·
    refine ⟨16778034245964488647874219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11185356163976325765249479 16778034245964488647874219)
    ·
      refine ⟨25167051368946732971811329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16778034245964488647874219 25167051368946732971811329)
      ·
        refine ⟨18875288526710049728858497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25167051368946732971811329 18875288526710049728858497)
        ·
          refine ⟨14156466395032537296643873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18875288526710049728858497 14156466395032537296643873)
          ·
            refine ⟨10617349796274402972482905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14156466395032537296643873 10617349796274402972482905)
            ·
              refine ⟨7963012347205802229362179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10617349796274402972482905 7963012347205802229362179)
              ·
                refine ⟨11944518520808703344043269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7963012347205802229362179 11944518520808703344043269)
                ·
                  refine ⟨2239597222651631877008113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11944518520808703344043269 2239597222651631877008113)
                  ·
                    refine ⟨1679697916988723907756085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2239597222651631877008113 1679697916988723907756085)
                    ·
                      refine ⟨157471679717692866352133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1679697916988723907756085 157471679717692866352133)
                      ·
                        rfl

theorem cell23_306675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_306675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306675 prefixEnd_306675 := by exact prefixLift 306675
  have htrace : WordTrace (prefixWord ++ tailWord_306675) baseStart_306675 baseEnd_306675 := by
    simpa [prefixWord, tailWord_306675, baseEnd_306675] using wordTrace_append hprefix tailTrace_306675
  have hstable : (prefixWord ++ tailWord_306675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306675).length < 2 ^ (prefixWord ++ tailWord_306675).sum := by decide
  have hdescent : baseEnd_306675 < baseStart_306675 := by decide
  rcases family_descends (prefixWord ++ tailWord_306675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306679 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_306679 : Nat := 118140960795 + 306679 * 2 ^ 59
def prefixEnd_306679 : Nat := 4983230072969 + 3 ^ 40 * 306679 * 2
def baseEnd_306679 : Nat := 157473733640310850702115

theorem tailTrace_306679 : CollatzResearch.WordTrace tailWord_306679 prefixEnd_306679 157473733640310850702115 := by
  unfold tailWord_306679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185502055961834448395091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7457001370641222965596727 11185502055961834448395091)
  ·
    refine ⟨16778253083942751672592637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11185502055961834448395091 16778253083942751672592637)
    ·
      refine ⟨6291844906478531877222239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16778253083942751672592637 6291844906478531877222239)
      ·
        refine ⟨9437767359717797815833359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6291844906478531877222239 9437767359717797815833359)
        ·
          refine ⟨14156651039576696723750039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9437767359717797815833359 14156651039576696723750039)
          ·
            refine ⟨21234976559365045085625059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14156651039576696723750039 21234976559365045085625059)
            ·
              refine ⟨31852464839047567628437589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21234976559365045085625059 31852464839047567628437589)
              ·
                refine ⟨373271072332588683145753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 31852464839047567628437589 373271072332588683145753)
                ·
                  refine ⟨279953304249441512359315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373271072332588683145753 279953304249441512359315)
                  ·
                    refine ⟨419929956374162268538973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 279953304249441512359315 419929956374162268538973)
                    ·
                      refine ⟨157473733640310850702115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 419929956374162268538973 157473733640310850702115)
                      ·
                        rfl

theorem cell23_306679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_306679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306679 prefixEnd_306679 := by exact prefixLift 306679
  have htrace : WordTrace (prefixWord ++ tailWord_306679) baseStart_306679 baseEnd_306679 := by
    simpa [prefixWord, tailWord_306679, baseEnd_306679] using wordTrace_append hprefix tailTrace_306679
  have hstable : (prefixWord ++ tailWord_306679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306679).length < 2 ^ (prefixWord ++ tailWord_306679).sum := by decide
  have hdescent : baseEnd_306679 < baseStart_306679 := by decide
  rcases family_descends (prefixWord ++ tailWord_306679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306719 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 1, 4, 2]
def baseStart_306719 : Nat := 118140960795 + 306719 * 2 ^ 59
def prefixEnd_306719 : Nat := 4983230072969 + 3 ^ 40 * 306719 * 2
def baseEnd_306719 : Nat := 157494272866490694201931

theorem tailTrace_306719 : CollatzResearch.WordTrace tailWord_306719 prefixEnd_306719 157494272866490694201931 := by
  unfold tailWord_306719
  simp only [CollatzResearch.WordTrace]
  refine ⟨11186960975816921279851211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7457973983877947519900807 11186960975816921279851211)
  ·
    refine ⟨16780441463725381919776817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11186960975816921279851211 16780441463725381919776817)
    ·
      refine ⟨12585331097794036439832613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16780441463725381919776817 12585331097794036439832613)
      ·
        refine ⟨2359749580836381832468615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12585331097794036439832613 2359749580836381832468615)
        ·
          refine ⟨3539624371254572748702923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359749580836381832468615 3539624371254572748702923)
          ·
            refine ⟨5309436556881859123054385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539624371254572748702923 5309436556881859123054385)
            ·
              refine ⟨3982077417661394342290789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5309436556881859123054385 3982077417661394342290789)
              ·
                refine ⟨746639515811511439179523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3982077417661394342290789 746639515811511439179523)
                ·
                  refine ⟨1119959273717267158769285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746639515811511439179523 1119959273717267158769285)
                  ·
                    refine ⟨209992363821987592269241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119959273717267158769285 209992363821987592269241)
                    ·
                      refine ⟨157494272866490694201931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 209992363821987592269241 157494272866490694201931)
                      ·
                        rfl

theorem cell23_306719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_306719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306719 prefixEnd_306719 := by exact prefixLift 306719
  have htrace : WordTrace (prefixWord ++ tailWord_306719) baseStart_306719 baseEnd_306719 := by
    simpa [prefixWord, tailWord_306719, baseEnd_306719] using wordTrace_append hprefix tailTrace_306719
  have hstable : (prefixWord ++ tailWord_306719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306719).length < 2 ^ (prefixWord ++ tailWord_306719).sum := by decide
  have hdescent : baseEnd_306719 < baseStart_306719 := by decide
  rcases family_descends (prefixWord ++ tailWord_306719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306722 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_306722 : Nat := 118140960795 + 306722 * 2 ^ 59
def prefixEnd_306722 : Nat := 4983230072969 + 3 ^ 40 * 306722 * 2
def baseEnd_306722 : Nat := 157495813308454182464417

theorem tailTrace_306722 : CollatzResearch.WordTrace tailWord_306722 prefixEnd_306722 157495813308454182464417 := by
  unfold tailWord_306722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796767598701513198052605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7458046929870701861473613 2796767598701513198052605)
  ·
    refine ⟨1048787849513067449269727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2796767598701513198052605 1048787849513067449269727)
    ·
      refine ⟨1573181774269601173904591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1048787849513067449269727 1573181774269601173904591)
      ·
        refine ⟨2359772661404401760856887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573181774269601173904591 2359772661404401760856887)
        ·
          refine ⟨3539658992106602641285331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359772661404401760856887 3539658992106602641285331)
          ·
            refine ⟨5309488488159903961927997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539658992106602641285331 5309488488159903961927997)
            ·
              refine ⟨1991058183059963985722999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5309488488159903961927997 1991058183059963985722999)
              ·
                refine ⟨2986587274589945978584499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991058183059963985722999 2986587274589945978584499)
                ·
                  refine ⟨4479880911884918967876749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986587274589945978584499 4479880911884918967876749)
                  ·
                    refine ⟨1679955341956844612953781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4479880911884918967876749 1679955341956844612953781)
                    ·
                      refine ⟨157495813308454182464417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1679955341956844612953781 157495813308454182464417)
                      ·
                        rfl

theorem cell23_306722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_306722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306722 prefixEnd_306722 := by exact prefixLift 306722
  have htrace : WordTrace (prefixWord ++ tailWord_306722) baseStart_306722 baseEnd_306722 := by
    simpa [prefixWord, tailWord_306722, baseEnd_306722] using wordTrace_append hprefix tailTrace_306722
  have hstable : (prefixWord ++ tailWord_306722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306722).length < 2 ^ (prefixWord ++ tailWord_306722).sum := by decide
  have hdescent : baseEnd_306722 < baseStart_306722 := by decide
  rcases family_descends (prefixWord ++ tailWord_306722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306736 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 2, 2, 2]
def baseStart_306736 : Nat := 118140960795 + 306736 * 2 ^ 59
def prefixEnd_306736 : Nat := 4983230072969 + 3 ^ 40 * 306736 * 2
def baseEnd_306736 : Nat := 157503002037617127689353

theorem tailTrace_306736 : CollatzResearch.WordTrace tailWord_306736 prefixEnd_306736 157503002037617127689353 := by
  unfold tailWord_306736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5593790508377666591610031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7458387344503555455480041 5593790508377666591610031)
  ·
    refine ⟨8390685762566499887415047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5593790508377666591610031 8390685762566499887415047)
    ·
      refine ⟨12586028643849749831122571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8390685762566499887415047 12586028643849749831122571)
      ·
        refine ⟨18879042965774624746683857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12586028643849749831122571 18879042965774624746683857)
        ·
          refine ⟨14159282224330968560012893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18879042965774624746683857 14159282224330968560012893)
          ·
            refine ⟨5309730834124113210004835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14159282224330968560012893 5309730834124113210004835)
            ·
              refine ⟨7964596251186169815007253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309730834124113210004835 7964596251186169815007253)
              ·
                refine ⟨373340449274351710078465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7964596251186169815007253 373340449274351710078465)
                ·
                  refine ⟨280005336955763782558849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373340449274351710078465 280005336955763782558849)
                  ·
                    refine ⟨210004002716822836919137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280005336955763782558849 210004002716822836919137)
                    ·
                      refine ⟨157503002037617127689353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210004002716822836919137 157503002037617127689353)
                      ·
                        rfl

theorem cell23_306736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 2, 2].length) (baseStart_306736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306736 prefixEnd_306736 := by exact prefixLift 306736
  have htrace : WordTrace (prefixWord ++ tailWord_306736) baseStart_306736 baseEnd_306736 := by
    simpa [prefixWord, tailWord_306736, baseEnd_306736] using wordTrace_append hprefix tailTrace_306736
  have hstable : (prefixWord ++ tailWord_306736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306736).length < 2 ^ (prefixWord ++ tailWord_306736).sum := by decide
  have hdescent : baseEnd_306736 < baseStart_306736 := by decide
  rcases family_descends (prefixWord ++ tailWord_306736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306752 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_306752 : Nat := 118140960795 + 306752 * 2 ^ 59
def prefixEnd_306752 : Nat := 4983230072969 + 3 ^ 40 * 306752 * 2
def baseEnd_306752 : Nat := 157511217728089065089279

theorem tailTrace_306752 : CollatzResearch.WordTrace tailWord_306752 prefixEnd_306752 157511217728089065089279 := by
  unfold tailWord_306752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594082292348683957901255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7458776389798245277201673 5594082292348683957901255)
  ·
    refine ⟨8391123438523025936851883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5594082292348683957901255 8391123438523025936851883)
    ·
      refine ⟨12586685157784538905277825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8391123438523025936851883 12586685157784538905277825)
      ·
        refine ⟨9440013868338404178958369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12586685157784538905277825 9440013868338404178958369)
        ·
          refine ⟨7080010401253803134218777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9440013868338404178958369 7080010401253803134218777)
          ·
            refine ⟨5310007800940352350664083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7080010401253803134218777 5310007800940352350664083)
            ·
              refine ⟨7965011701410528525996125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310007800940352350664083 7965011701410528525996125)
              ·
                refine ⟨2986879388028948197248547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7965011701410528525996125 2986879388028948197248547)
                ·
                  refine ⟨4480319082043422295872821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986879388028948197248547 4480319082043422295872821)
                  ·
                    refine ⟨420029913941570840238077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4480319082043422295872821 420029913941570840238077)
                    ·
                      refine ⟨157511217728089065089279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 420029913941570840238077 157511217728089065089279)
                      ·
                        rfl

theorem cell23_306752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_306752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306752 prefixEnd_306752 := by exact prefixLift 306752
  have htrace : WordTrace (prefixWord ++ tailWord_306752) baseStart_306752 baseEnd_306752 := by
    simpa [prefixWord, tailWord_306752, baseEnd_306752] using wordTrace_append hprefix tailTrace_306752
  have hstable : (prefixWord ++ tailWord_306752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306752).length < 2 ^ (prefixWord ++ tailWord_306752).sum := by decide
  have hdescent : baseEnd_306752 < baseStart_306752 := by decide
  rcases family_descends (prefixWord ++ tailWord_306752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306753 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_306753 : Nat := 118140960795 + 306753 * 2 ^ 59
def prefixEnd_306753 : Nat := 4983230072969 + 3 ^ 40 * 306753 * 2
def baseEnd_306753 : Nat := 157511731208743561176775

theorem tailTrace_306753 : CollatzResearch.WordTrace tailWord_306753 prefixEnd_306753 157511731208743561176775 := by
  unfold tailWord_306753
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188201057693745086588913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7458800705129163391059275 11188201057693745086588913)
  ·
    refine ⟨8391150793270308814941685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11188201057693745086588913 8391150793270308814941685)
    ·
      refine ⟨786670386869091451400783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8391150793270308814941685 786670386869091451400783)
      ·
        refine ⟨1180005580303637177101175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786670386869091451400783 1180005580303637177101175)
        ·
          refine ⟨1770008370455455765651763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180005580303637177101175 1770008370455455765651763)
          ·
            refine ⟨2655012555683183648477645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770008370455455765651763 2655012555683183648477645)
            ·
              refine ⟨995629708381193868179117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2655012555683183648477645 995629708381193868179117)
              ·
                refine ⟨373361140642947700567169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995629708381193868179117 373361140642947700567169)
                ·
                  refine ⟨280020855482210775425377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373361140642947700567169 280020855482210775425377)
                  ·
                    refine ⟨210015641611658081569033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280020855482210775425377 210015641611658081569033)
                    ·
                      refine ⟨157511731208743561176775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210015641611658081569033 157511731208743561176775)
                      ·
                        rfl

theorem cell23_306753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_306753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306753 prefixEnd_306753 := by exact prefixLift 306753
  have htrace : WordTrace (prefixWord ++ tailWord_306753) baseStart_306753 baseEnd_306753 := by
    simpa [prefixWord, tailWord_306753, baseEnd_306753] using wordTrace_append hprefix tailTrace_306753
  have hstable : (prefixWord ++ tailWord_306753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306753).length < 2 ^ (prefixWord ++ tailWord_306753).sum := by decide
  have hdescent : baseEnd_306753 < baseStart_306753 := by decide
  rcases family_descends (prefixWord ++ tailWord_306753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306774 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_306774 : Nat := 118140960795 + 306774 * 2 ^ 59
def prefixEnd_306774 : Nat := 4983230072969 + 3 ^ 40 * 306774 * 2
def baseEnd_306774 : Nat := 157522514302487979014179

theorem tailTrace_306774 : CollatzResearch.WordTrace tailWord_306774 prefixEnd_306774 157522514302487979014179 := by
  unfold tailWord_306774
  simp only [CollatzResearch.WordTrace]
  refine ⟨699310436913604104568961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7459311327078443782068917 699310436913604104568961)
  ·
    refine ⟨524482827685203078426721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 699310436913604104568961 524482827685203078426721)
    ·
      refine ⟨393362120763902308820041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524482827685203078426721 393362120763902308820041)
      ·
        refine ⟨295021590572926731615031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393362120763902308820041 295021590572926731615031)
        ·
          refine ⟨442532385859390097422547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295021590572926731615031 442532385859390097422547)
          ·
            refine ⟨663798578789085146133821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442532385859390097422547 663798578789085146133821)
            ·
              refine ⟨248924467045906929800183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663798578789085146133821 248924467045906929800183)
              ·
                refine ⟨373386700568860394700275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248924467045906929800183 373386700568860394700275)
                ·
                  refine ⟨560080050853290592050413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373386700568860394700275 560080050853290592050413)
                  ·
                    refine ⟨210030019069983972018905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560080050853290592050413 210030019069983972018905)
                    ·
                      refine ⟨157522514302487979014179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210030019069983972018905 157522514302487979014179)
                      ·
                        rfl

theorem cell23_306774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_306774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306774 prefixEnd_306774 := by exact prefixLift 306774
  have htrace : WordTrace (prefixWord ++ tailWord_306774) baseStart_306774 baseEnd_306774 := by
    simpa [prefixWord, tailWord_306774, baseEnd_306774] using wordTrace_append hprefix tailTrace_306774
  have hstable : (prefixWord ++ tailWord_306774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306774).length < 2 ^ (prefixWord ++ tailWord_306774).sum := by decide
  have hdescent : baseEnd_306774 < baseStart_306774 := by decide
  rcases family_descends (prefixWord ++ tailWord_306774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306789 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_306789 : Nat := 118140960795 + 306789 * 2 ^ 59
def prefixEnd_306789 : Nat := 4983230072969 + 3 ^ 40 * 306789 * 2
def baseEnd_306789 : Nat := 52510072170768473442203

theorem tailTrace_306789 : CollatzResearch.WordTrace tailWord_306789 prefixEnd_306789 52510072170768473442203 := by
  unfold tailWord_306789
  simp only [CollatzResearch.WordTrace]
  refine ⟨11189514085563323234899421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7459676057042215489932947 11189514085563323234899421)
  ·
    refine ⟨4196067782086246213087283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11189514085563323234899421 4196067782086246213087283)
    ·
      refine ⟨6294101673129369319630925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196067782086246213087283 6294101673129369319630925)
      ·
        refine ⟨2360288127423513494861597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6294101673129369319630925 2360288127423513494861597)
        ·
          refine ⟨885108047783817560573099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2360288127423513494861597 885108047783817560573099)
          ·
            refine ⟨1327662071675726340859649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885108047783817560573099 1327662071675726340859649)
            ·
              refine ⟨995746553756794755644737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327662071675726340859649 995746553756794755644737)
              ·
                refine ⟨746809915317596066733553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995746553756794755644737 746809915317596066733553)
                ·
                  refine ⟨560107436488197050050165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 746809915317596066733553 560107436488197050050165)
                  ·
                    refine ⟨52510072170768473442203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 560107436488197050050165 52510072170768473442203)
                    ·
                      rfl

theorem cell23_306789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_306789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306789 prefixEnd_306789 := by exact prefixLift 306789
  have htrace : WordTrace (prefixWord ++ tailWord_306789) baseStart_306789 baseEnd_306789 := by
    simpa [prefixWord, tailWord_306789, baseEnd_306789] using wordTrace_append hprefix tailTrace_306789
  have hstable : (prefixWord ++ tailWord_306789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306789).length < 2 ^ (prefixWord ++ tailWord_306789).sum := by decide
  have hdescent : baseEnd_306789 < baseStart_306789 := by decide
  rcases family_descends (prefixWord ++ tailWord_306789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306826 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_306826 : Nat := 118140960795 + 306826 * 2 ^ 59
def prefixEnd_306826 : Nat := 4983230072969 + 3 ^ 40 * 306826 * 2
def baseEnd_306826 : Nat := 157549215296521775563939

theorem tailTrace_306826 : CollatzResearch.WordTrace tailWord_306826 prefixEnd_306826 157549215296521775563939 := by
  unfold tailWord_306826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797715896607319638499083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7460575724286185702664221 2797715896607319638499083)
  ·
    refine ⟨4196573844910979457748625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2797715896607319638499083 4196573844910979457748625)
    ·
      refine ⟨3147430383683234593311469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4196573844910979457748625 3147430383683234593311469)
      ·
        refine ⟨1180286393881212972491801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3147430383683234593311469 1180286393881212972491801)
        ·
          refine ⟨885214795410909729368851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180286393881212972491801 885214795410909729368851)
          ·
            refine ⟨1327822193116364594053277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885214795410909729368851 1327822193116364594053277)
            ·
              refine ⟨497933322418636722769979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1327822193116364594053277 497933322418636722769979)
              ·
                refine ⟨746899983627955084154969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497933322418636722769979 746899983627955084154969)
                ·
                  refine ⟨560174987720966313116227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 746899983627955084154969 560174987720966313116227)
                  ·
                    refine ⟨840262481581449469674341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 560174987720966313116227 840262481581449469674341)
                    ·
                      refine ⟨157549215296521775563939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 840262481581449469674341 157549215296521775563939)
                      ·
                        rfl

theorem cell23_306826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_306826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306826 prefixEnd_306826 := by exact prefixLift 306826
  have htrace : WordTrace (prefixWord ++ tailWord_306826) baseStart_306826 baseEnd_306826 := by
    simpa [prefixWord, tailWord_306826, baseEnd_306826] using wordTrace_append hprefix tailTrace_306826
  have hstable : (prefixWord ++ tailWord_306826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306826).length < 2 ^ (prefixWord ++ tailWord_306826).sum := by decide
  have hdescent : baseEnd_306826 < baseStart_306826 := by decide
  rcases family_descends (prefixWord ++ tailWord_306826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306849 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 8]
def baseStart_306849 : Nat := 118140960795 + 306849 * 2 ^ 59
def prefixEnd_306849 : Nat := 4983230072969 + 3 ^ 40 * 306849 * 2
def baseEnd_306849 : Nat := 17506780594619465064037

theorem tailTrace_306849 : CollatzResearch.WordTrace tailWord_306849 prefixEnd_306849 17506780594619465064037 := by
  unfold tailWord_306849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11191702465345953482083601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7461134976897302321389067 11191702465345953482083601)
  ·
    refine ⟨8393776849009465111562701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11191702465345953482083601 8393776849009465111562701)
    ·
      refine ⟨3147666318378549416836013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8393776849009465111562701 3147666318378549416836013)
      ·
        refine ⟨1180374869391956031313505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3147666318378549416836013 1180374869391956031313505)
        ·
          refine ⟨885281152043967023485129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180374869391956031313505 885281152043967023485129)
          ·
            refine ⟨663960864032975267613847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885281152043967023485129 663960864032975267613847)
            ·
              refine ⟨995941296049462901420771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663960864032975267613847 995941296049462901420771)
              ·
                refine ⟨1493911944074194352131157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995941296049462901420771 1493911944074194352131157)
                ·
                  refine ⟨17506780594619465064037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1493911944074194352131157 17506780594619465064037)
                  ·
                    rfl

theorem cell23_306849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_306849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306849 prefixEnd_306849 := by exact prefixLift 306849
  have htrace : WordTrace (prefixWord ++ tailWord_306849) baseStart_306849 baseEnd_306849 := by
    simpa [prefixWord, tailWord_306849, baseEnd_306849] using wordTrace_append hprefix tailTrace_306849
  have hstable : (prefixWord ++ tailWord_306849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306849).length < 2 ^ (prefixWord ++ tailWord_306849).sum := by decide
  have hdescent : baseEnd_306849 < baseStart_306849 := by decide
  rcases family_descends (prefixWord ++ tailWord_306849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306872 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_306872 : Nat := 118140960795 + 306872 * 2 ^ 59
def prefixEnd_306872 : Nat := 4983230072969 + 3 ^ 40 * 306872 * 2
def baseEnd_306872 : Nat := 157572835406628595588727

theorem tailTrace_306872 : CollatzResearch.WordTrace tailWord_306872 prefixEnd_306872 157572835406628595588727 := by
  unfold tailWord_306872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596270672131314205085435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7461694229508418940113913 5596270672131314205085435)
  ·
    refine ⟨8394406008196971307628153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5596270672131314205085435 8394406008196971307628153)
    ·
      refine ⟨6295804506147728480721115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8394406008196971307628153 6295804506147728480721115)
      ·
        refine ⟨9443706759221592721081673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6295804506147728480721115 9443706759221592721081673)
        ·
          refine ⟨7082780069416194540811255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9443706759221592721081673 7082780069416194540811255)
          ·
            refine ⟨10624170104124291811216883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082780069416194540811255 10624170104124291811216883)
            ·
              refine ⟨15936255156186437716825325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10624170104124291811216883 15936255156186437716825325)
              ·
                refine ⟨5976095683569914143809497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15936255156186437716825325 5976095683569914143809497)
                ·
                  refine ⟨4482071762677435607857123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5976095683569914143809497 4482071762677435607857123)
                  ·
                    refine ⟨6723107644016153411785685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4482071762677435607857123 6723107644016153411785685)
                    ·
                      refine ⟨157572835406628595588727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6723107644016153411785685 157572835406628595588727)
                      ·
                        rfl

theorem cell23_306872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_306872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306872 prefixEnd_306872 := by exact prefixLift 306872
  have htrace : WordTrace (prefixWord ++ tailWord_306872) baseStart_306872 baseEnd_306872 := by
    simpa [prefixWord, tailWord_306872, baseEnd_306872] using wordTrace_append hprefix tailTrace_306872
  have hstable : (prefixWord ++ tailWord_306872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306872).length < 2 ^ (prefixWord ++ tailWord_306872).sum := by decide
  have hdescent : baseEnd_306872 < baseStart_306872 := by decide
  rcases family_descends (prefixWord ++ tailWord_306872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306929 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_306929 : Nat := 118140960795 + 306929 * 2 ^ 59
def prefixEnd_306929 : Nat := 4983230072969 + 3 ^ 40 * 306929 * 2
def baseEnd_306929 : Nat := 157602103803934872575965

theorem tailTrace_306929 : CollatzResearch.WordTrace tailWord_306929 prefixEnd_306929 157602103803934872575965 := by
  unfold tailWord_306929
  simp only [CollatzResearch.WordTrace]
  refine ⟨11194620305056127144995841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7463080203370751429997227 11194620305056127144995841)
  ·
    refine ⟨8395965228792095358746881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11194620305056127144995841 8395965228792095358746881)
    ·
      refine ⟨6296973921594071519060161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8395965228792095358746881 6296973921594071519060161)
      ·
        refine ⟨4722730441195553639295121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6296973921594071519060161 4722730441195553639295121)
        ·
          refine ⟨3542047830896665229471341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4722730441195553639295121 3542047830896665229471341)
          ·
            refine ⟨1328267936586249461051753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3542047830896665229471341 1328267936586249461051753)
            ·
              refine ⟨996200952439687095788815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328267936586249461051753 996200952439687095788815)
              ·
                refine ⟨1494301428659530643683223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996200952439687095788815 1494301428659530643683223)
                ·
                  refine ⟨2241452142989295965524835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494301428659530643683223 2241452142989295965524835)
                  ·
                    refine ⟨3362178214483943948287253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2241452142989295965524835 3362178214483943948287253)
                    ·
                      refine ⟨157602103803934872575965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3362178214483943948287253 157602103803934872575965)
                      ·
                        rfl

theorem cell23_306929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_306929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306929 prefixEnd_306929 := by exact prefixLift 306929
  have htrace : WordTrace (prefixWord ++ tailWord_306929) baseStart_306929 baseEnd_306929 := by
    simpa [prefixWord, tailWord_306929, baseEnd_306929] using wordTrace_append hprefix tailTrace_306929
  have hstable : (prefixWord ++ tailWord_306929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306929).length < 2 ^ (prefixWord ++ tailWord_306929).sum := by decide
  have hdescent : baseEnd_306929 < baseStart_306929 := by decide
  rcases family_descends (prefixWord ++ tailWord_306929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306936 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_306936 : Nat := 118140960795 + 306936 * 2 ^ 59
def prefixEnd_306936 : Nat := 4983230072969 + 3 ^ 40 * 306936 * 2
def baseEnd_306936 : Nat := 157605698168516345188433

theorem tailTrace_306936 : CollatzResearch.WordTrace tailWord_306936 prefixEnd_306936 157605698168516345188433 := by
  unfold tailWord_306936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597437808015383670250331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7463250410687178227000441 5597437808015383670250331)
  ·
    refine ⟨8396156712023075505375497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5597437808015383670250331 8396156712023075505375497)
    ·
      refine ⟨6297117534017306629031623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8396156712023075505375497 6297117534017306629031623)
      ·
        refine ⟨9445676301025959943547435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297117534017306629031623 9445676301025959943547435)
        ·
          refine ⟨14168514451538939915321153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9445676301025959943547435 14168514451538939915321153)
          ·
            refine ⟨10626385838654204936490865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14168514451538939915321153 10626385838654204936490865)
            ·
              refine ⟨7969789378990653702368149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10626385838654204936490865 7969789378990653702368149)
              ·
                refine ⟨373583877140186892298507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7969789378990653702368149 373583877140186892298507)
                ·
                  refine ⟨560375815710280338447761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373583877140186892298507 560375815710280338447761)
                  ·
                    refine ⟨420281861782710253835821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 560375815710280338447761 420281861782710253835821)
                    ·
                      refine ⟨157605698168516345188433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 420281861782710253835821 157605698168516345188433)
                      ·
                        rfl

theorem cell23_306936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_306936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306936 prefixEnd_306936 := by exact prefixLift 306936
  have htrace : WordTrace (prefixWord ++ tailWord_306936) baseStart_306936 baseEnd_306936 := by
    simpa [prefixWord, tailWord_306936, baseEnd_306936] using wordTrace_append hprefix tailTrace_306936
  have hstable : (prefixWord ++ tailWord_306936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306936).length < 2 ^ (prefixWord ++ tailWord_306936).sum := by decide
  have hdescent : baseEnd_306936 < baseStart_306936 := by decide
  rcases family_descends (prefixWord ++ tailWord_306936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306967 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 1, 2, 2]
def baseStart_306967 : Nat := 118140960795 + 306967 * 2 ^ 59
def prefixEnd_306967 : Nat := 4983230072969 + 3 ^ 40 * 306967 * 2
def baseEnd_306967 : Nat := 157621616068805723900791

theorem tailTrace_306967 : CollatzResearch.WordTrace tailWord_306967 prefixEnd_306967 157621616068805723900791 := by
  unfold tailWord_306967
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196006278918459634879155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7464004185945639756586103 11196006278918459634879155)
  ·
    refine ⟨16794009418377689452318733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11196006278918459634879155 16794009418377689452318733)
    ·
      refine ⟨6297753531891633544619525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16794009418377689452318733 6297753531891633544619525)
      ·
        refine ⟨1180828787229681289616161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6297753531891633544619525 1180828787229681289616161)
        ·
          refine ⟨885621590422260967212121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180828787229681289616161 885621590422260967212121)
          ·
            refine ⟨664216192816695725409091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885621590422260967212121 664216192816695725409091)
            ·
              refine ⟨996324289225043588113637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664216192816695725409091 996324289225043588113637)
              ·
                refine ⟨186810804229695672771307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 996324289225043588113637 186810804229695672771307)
                ·
                  refine ⟨280216206344543509156961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186810804229695672771307 280216206344543509156961)
                  ·
                    refine ⟨210162154758407631867721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280216206344543509156961 210162154758407631867721)
                    ·
                      refine ⟨157621616068805723900791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210162154758407631867721 157621616068805723900791)
                      ·
                        rfl

theorem cell23_306967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_306967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306967 prefixEnd_306967 := by exact prefixLift 306967
  have htrace : WordTrace (prefixWord ++ tailWord_306967) baseStart_306967 baseEnd_306967 := by
    simpa [prefixWord, tailWord_306967, baseEnd_306967] using wordTrace_append hprefix tailTrace_306967
  have hstable : (prefixWord ++ tailWord_306967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306967).length < 2 ^ (prefixWord ++ tailWord_306967).sum := by decide
  have hdescent : baseEnd_306967 < baseStart_306967 := by decide
  rcases family_descends (prefixWord ++ tailWord_306967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306993 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 3, 3, 2]
def baseStart_306993 : Nat := 118140960795 + 306993 * 2 ^ 59
def prefixEnd_306993 : Nat := 4983230072969 + 3 ^ 40 * 306993 * 2
def baseEnd_306993 : Nat := 157634966565822622175671

theorem tailTrace_306993 : CollatzResearch.WordTrace tailWord_306993 prefixEnd_306993 157634966565822622175671 := by
  unfold tailWord_306993
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196954576824266075325633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7464636384549510716883755 11196954576824266075325633)
  ·
    refine ⟨8397715932618199556494225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11196954576824266075325633 8397715932618199556494225)
    ·
      refine ⟨6298286949463649667370669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8397715932618199556494225 6298286949463649667370669)
      ·
        refine ⟨2361857606048868625264001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6298286949463649667370669 2361857606048868625264001)
        ·
          refine ⟨1771393204536651468948001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2361857606048868625264001 1771393204536651468948001)
          ·
            refine ⟨1328544903402488601711001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771393204536651468948001 1328544903402488601711001)
            ·
              refine ⟨996408677551866451283251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328544903402488601711001 996408677551866451283251)
              ·
                refine ⟨1494613016327799676924877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996408677551866451283251 1494613016327799676924877)
                ·
                  refine ⟨560479881122924878846829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1494613016327799676924877 560479881122924878846829)
                  ·
                    refine ⟨210179955421096829567561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560479881122924878846829 210179955421096829567561)
                    ·
                      refine ⟨157634966565822622175671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210179955421096829567561 157634966565822622175671)
                      ·
                        rfl

theorem cell23_306993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_306993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_306993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_306993 prefixEnd_306993 := by exact prefixLift 306993
  have htrace : WordTrace (prefixWord ++ tailWord_306993) baseStart_306993 baseEnd_306993 := by
    simpa [prefixWord, tailWord_306993, baseEnd_306993] using wordTrace_append hprefix tailTrace_306993
  have hstable : (prefixWord ++ tailWord_306993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306993).length < 2 ^ (prefixWord ++ tailWord_306993).sum := by decide
  have hdescent : baseEnd_306993 < baseStart_306993 := by decide
  rcases family_descends (prefixWord ++ tailWord_306993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307040 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 1, 4, 2]
def baseStart_307040 : Nat := 118140960795 + 307040 * 2 ^ 59
def prefixEnd_307040 : Nat := 4983230072969 + 3 ^ 40 * 307040 * 2
def baseEnd_307040 : Nat := 157659100156583938287955

theorem tailTrace_307040 : CollatzResearch.WordTrace tailWord_307040 prefixEnd_307040 157659100156583938287955 := by
  unfold tailWord_307040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599334403826996551143287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7465779205102662068191049 5599334403826996551143287)
  ·
    refine ⟨8399001605740494826714931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5599334403826996551143287 8399001605740494826714931)
    ·
      refine ⟨12598502408610742240072397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8399001605740494826714931 12598502408610742240072397)
      ·
        refine ⟨4724438403229028340027149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12598502408610742240072397 4724438403229028340027149)
        ·
          refine ⟨1771664401210885627510181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4724438403229028340027149 1771664401210885627510181)
          ·
            refine ⟨332187075227041055158159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1771664401210885627510181 332187075227041055158159)
            ·
              refine ⟨498280612840561582737239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332187075227041055158159 498280612840561582737239)
              ·
                refine ⟨747420919260842374105859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498280612840561582737239 747420919260842374105859)
                ·
                  refine ⟨1121131378891263561158789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747420919260842374105859 1121131378891263561158789)
                  ·
                    refine ⟨210212133542111917717273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121131378891263561158789 210212133542111917717273)
                    ·
                      refine ⟨157659100156583938287955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210212133542111917717273 157659100156583938287955)
                      ·
                        rfl

theorem cell23_307040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_307040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307040 prefixEnd_307040 := by exact prefixLift 307040
  have htrace : WordTrace (prefixWord ++ tailWord_307040) baseStart_307040 baseEnd_307040 := by
    simpa [prefixWord, tailWord_307040, baseEnd_307040] using wordTrace_append hprefix tailTrace_307040
  have hstable : (prefixWord ++ tailWord_307040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307040).length < 2 ^ (prefixWord ++ tailWord_307040).sum := by decide
  have hdescent : baseEnd_307040 < baseStart_307040 := by decide
  rcases family_descends (prefixWord ++ tailWord_307040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307076 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_307076 : Nat := 118140960795 + 307076 * 2 ^ 59
def prefixEnd_307076 : Nat := 4983230072969 + 3 ^ 40 * 307076 * 2
def baseEnd_307076 : Nat := 52559195153381932479263

theorem tailTrace_307076 : CollatzResearch.WordTrace tailWord_307076 prefixEnd_307076 52559195153381932479263 := by
  unfold tailWord_307076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599990917761785625298541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7466654557015714167064721 5599990917761785625298541)
  ·
    refine ⟨2099996594160669609486953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5599990917761785625298541 2099996594160669609486953)
    ·
      refine ⟨1574997445620502207115215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2099996594160669609486953 1574997445620502207115215)
      ·
        refine ⟨2362496168430753310672823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574997445620502207115215 2362496168430753310672823)
        ·
          refine ⟨3543744252646129966009235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362496168430753310672823 3543744252646129966009235)
          ·
            refine ⟨5315616378969194949013853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543744252646129966009235 5315616378969194949013853)
            ·
              refine ⟨1993356142113448105880195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5315616378969194949013853 1993356142113448105880195)
              ·
                refine ⟨2990034213170172158820293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993356142113448105880195 2990034213170172158820293)
                ·
                  refine ⟨560631414969407279778805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2990034213170172158820293 560631414969407279778805)
                  ·
                    refine ⟨52559195153381932479263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 560631414969407279778805 52559195153381932479263)
                    ·
                      rfl

theorem cell23_307076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_307076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307076 prefixEnd_307076 := by exact prefixLift 307076
  have htrace : WordTrace (prefixWord ++ tailWord_307076) baseStart_307076 baseEnd_307076 := by
    simpa [prefixWord, tailWord_307076, baseEnd_307076] using wordTrace_append hprefix tailTrace_307076
  have hstable : (prefixWord ++ tailWord_307076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307076).length < 2 ^ (prefixWord ++ tailWord_307076).sum := by decide
  have hdescent : baseEnd_307076 < baseStart_307076 := by decide
  rcases family_descends (prefixWord ++ tailWord_307076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307080 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 7]
def baseStart_307080 : Nat := 118140960795 + 307080 * 2 ^ 59
def prefixEnd_307080 : Nat := 4983230072969 + 3 ^ 40 * 307080 * 2
def baseEnd_307080 : Nat := 17519959931418197976419

theorem tailTrace_307080 : CollatzResearch.WordTrace tailWord_307080 prefixEnd_307080 17519959931418197976419 := by
  unfold tailWord_307080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600063863754539966871347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7466751818339386622495129 5600063863754539966871347)
  ·
    refine ⟨8400095795631809950307021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600063863754539966871347 8400095795631809950307021)
    ·
      refine ⟨3150035923361928731365133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8400095795631809950307021 3150035923361928731365133)
      ·
        refine ⟨1181263471260723274261925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3150035923361928731365133 1181263471260723274261925)
        ·
          refine ⟨221486900861385613924111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1181263471260723274261925 221486900861385613924111)
          ·
            refine ⟨332230351292078420886167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221486900861385613924111 332230351292078420886167)
            ·
              refine ⟨498345526938117631329251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332230351292078420886167 498345526938117631329251)
              ·
                refine ⟨747518290407176446993877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498345526938117631329251 747518290407176446993877)
                ·
                  refine ⟨17519959931418197976419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 747518290407176446993877 17519959931418197976419)
                  ·
                    rfl

theorem cell23_307080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 7].length) (baseStart_307080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307080 prefixEnd_307080 := by exact prefixLift 307080
  have htrace : WordTrace (prefixWord ++ tailWord_307080) baseStart_307080 baseEnd_307080 := by
    simpa [prefixWord, tailWord_307080, baseEnd_307080] using wordTrace_append hprefix tailTrace_307080
  have hstable : (prefixWord ++ tailWord_307080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307080).length < 2 ^ (prefixWord ++ tailWord_307080).sum := by decide
  have hdescent : baseEnd_307080 < baseStart_307080 := by decide
  rcases family_descends (prefixWord ++ tailWord_307080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307176 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_307176 : Nat := 118140960795 + 307176 * 2 ^ 59
def prefixEnd_307176 : Nat := 4983230072969 + 3 ^ 40 * 307176 * 2
def baseEnd_307176 : Nat := 157728933525595406187329

theorem tailTrace_307176 : CollatzResearch.WordTrace tailWord_307176 prefixEnd_307176 157728933525595406187329 := by
  unfold tailWord_307176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5601814567580644164618691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7469086090107525552824921 5601814567580644164618691)
  ·
    refine ⟨8402721851370966246928037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5601814567580644164618691 8402721851370966246928037)
    ·
      refine ⟨1575510347132056171299007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8402721851370966246928037 1575510347132056171299007)
      ·
        refine ⟨2363265520698084256948511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575510347132056171299007 2363265520698084256948511)
        ·
          refine ⟨3544898281047126385422767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363265520698084256948511 3544898281047126385422767)
          ·
            refine ⟨5317347421570689578134151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544898281047126385422767 5317347421570689578134151)
            ·
              refine ⟨7976021132356034367201227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317347421570689578134151 7976021132356034367201227)
              ·
                refine ⟨11964031698534051550801841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7976021132356034367201227 11964031698534051550801841)
                ·
                  refine ⟨8973023773900538663101381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11964031698534051550801841 8973023773900538663101381)
                  ·
                    refine ⟨1682441957606350999331509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8973023773900538663101381 1682441957606350999331509)
                    ·
                      refine ⟨157728933525595406187329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1682441957606350999331509 157728933525595406187329)
                      ·
                        rfl

theorem cell23_307176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_307176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307176 prefixEnd_307176 := by exact prefixLift 307176
  have htrace : WordTrace (prefixWord ++ tailWord_307176) baseStart_307176 baseEnd_307176 := by
    simpa [prefixWord, tailWord_307176, baseEnd_307176] using wordTrace_append hprefix tailTrace_307176
  have hstable : (prefixWord ++ tailWord_307176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307176).length < 2 ^ (prefixWord ++ tailWord_307176).sum := by decide
  have hdescent : baseEnd_307176 < baseStart_307176 := by decide
  rcases family_descends (prefixWord ++ tailWord_307176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307183 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 1, 5]
def baseStart_307183 : Nat := 118140960795 + 307183 * 2 ^ 59
def prefixEnd_307183 : Nat := 4983230072969 + 3 ^ 40 * 307183 * 2
def baseEnd_307183 : Nat := 52577509296725626266599

theorem tailTrace_307183 : CollatzResearch.WordTrace tailWord_307183 prefixEnd_307183 52577509296725626266599 := by
  unfold tailWord_307183
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203884446135928524742203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7469256297423952349828135 11203884446135928524742203)
  ·
    refine ⟨16805826669203892787113305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11203884446135928524742203 16805826669203892787113305)
    ·
      refine ⟨12604370001902919590334979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16805826669203892787113305 12604370001902919590334979)
      ·
        refine ⟨18906555002854379385502469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12604370001902919590334979 18906555002854379385502469)
        ·
          refine ⟨3544979063035196134781713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18906555002854379385502469 3544979063035196134781713)
          ·
            refine ⟨2658734297276397101086285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3544979063035196134781713 2658734297276397101086285)
            ·
              refine ⟨997025361478648912907357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2658734297276397101086285 997025361478648912907357)
              ·
                refine ⟨373884510554493342340259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997025361478648912907357 373884510554493342340259)
                ·
                  refine ⟨560826765831740013510389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373884510554493342340259 560826765831740013510389)
                  ·
                    refine ⟨52577509296725626266599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 560826765831740013510389 52577509296725626266599)
                    ·
                      rfl

theorem cell23_307183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_307183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307183 prefixEnd_307183 := by exact prefixLift 307183
  have htrace : WordTrace (prefixWord ++ tailWord_307183) baseStart_307183 baseEnd_307183 := by
    simpa [prefixWord, tailWord_307183, baseEnd_307183] using wordTrace_append hprefix tailTrace_307183
  have hstable : (prefixWord ++ tailWord_307183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307183).length < 2 ^ (prefixWord ++ tailWord_307183).sum := by decide
  have hdescent : baseEnd_307183 < baseStart_307183 := by decide
  rcases family_descends (prefixWord ++ tailWord_307183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307197 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_307197 : Nat := 118140960795 + 307197 * 2 ^ 59
def prefixEnd_307197 : Nat := 4983230072969 + 3 ^ 40 * 307197 * 2
def baseEnd_307197 : Nat := 157739716619339824024733

theorem tailTrace_307197 : CollatzResearch.WordTrace tailWord_307197 prefixEnd_307197 157739716619339824024733 := by
  unfold tailWord_307197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11204395068085208915751845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7469596712056805943834563 11204395068085208915751845)
  ·
    refine ⟨2100824075265976671703471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11204395068085208915751845 2100824075265976671703471)
    ·
      refine ⟨3151236112898965007555207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2100824075265976671703471 3151236112898965007555207)
      ·
        refine ⟨4726854169348447511332811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151236112898965007555207 4726854169348447511332811)
        ·
          refine ⟨7090281254022671266999217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726854169348447511332811 7090281254022671266999217)
          ·
            refine ⟨5317710940517003450249413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7090281254022671266999217 5317710940517003450249413)
            ·
              refine ⟨997070801346938146921765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5317710940517003450249413 997070801346938146921765)
              ·
                refine ⟨186950775252550902547831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 997070801346938146921765 186950775252550902547831)
                ·
                  refine ⟨280426162878826353821747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186950775252550902547831 280426162878826353821747)
                  ·
                    refine ⟨420639244318239530732621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 280426162878826353821747 420639244318239530732621)
                    ·
                      refine ⟨157739716619339824024733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 420639244318239530732621 157739716619339824024733)
                      ·
                        rfl

theorem cell23_307197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_307197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307197 prefixEnd_307197 := by exact prefixLift 307197
  have htrace : WordTrace (prefixWord ++ tailWord_307197) baseStart_307197 baseEnd_307197 := by
    simpa [prefixWord, tailWord_307197, baseEnd_307197] using wordTrace_append hprefix tailTrace_307197
  have hstable : (prefixWord ++ tailWord_307197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307197).length < 2 ^ (prefixWord ++ tailWord_307197).sum := by decide
  have hdescent : baseEnd_307197 < baseStart_307197 := by decide
  rcases family_descends (prefixWord ++ tailWord_307197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307216 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_307216 : Nat := 118140960795 + 307216 * 2 ^ 59
def prefixEnd_307216 : Nat := 4983230072969 + 3 ^ 40 * 307216 * 2
def baseEnd_307216 : Nat := 157749472751775249687145

theorem tailTrace_307216 : CollatzResearch.WordTrace tailWord_307216 prefixEnd_307216 157749472751775249687145 := by
  unfold tailWord_307216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602544027508187580346751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7470058703344250107129001 5602544027508187580346751)
  ·
    refine ⟨8403816041262281370520127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5602544027508187580346751 8403816041262281370520127)
    ·
      refine ⟨12605724061893422055780191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403816041262281370520127 12605724061893422055780191)
      ·
        refine ⟨18908586092840133083670287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12605724061893422055780191 18908586092840133083670287)
        ·
          refine ⟨28362879139260199625505431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18908586092840133083670287 28362879139260199625505431)
          ·
            refine ⟨42544318708890299438258147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28362879139260199625505431 42544318708890299438258147)
            ·
              refine ⟨63816478063335449157387221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42544318708890299438258147 63816478063335449157387221)
              ·
                refine ⟨1495698704609424589626263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63816478063335449157387221 1495698704609424589626263)
                ·
                  refine ⟨2243548056914136884439395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495698704609424589626263 2243548056914136884439395)
                  ·
                    refine ⟨3365322085371205326659093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2243548056914136884439395 3365322085371205326659093)
                    ·
                      refine ⟨157749472751775249687145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3365322085371205326659093 157749472751775249687145)
                      ·
                        rfl

theorem cell23_307216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_307216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307216 prefixEnd_307216 := by exact prefixLift 307216
  have htrace : WordTrace (prefixWord ++ tailWord_307216) baseStart_307216 baseEnd_307216 := by
    simpa [prefixWord, tailWord_307216, baseEnd_307216] using wordTrace_append hprefix tailTrace_307216
  have hstable : (prefixWord ++ tailWord_307216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307216).length < 2 ^ (prefixWord ++ tailWord_307216).sum := by decide
  have hdescent : baseEnd_307216 < baseStart_307216 := by decide
  rcases family_descends (prefixWord ++ tailWord_307216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307303 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 2, 6]
def baseStart_307303 : Nat := 118140960795 + 307303 * 2 ^ 59
def prefixEnd_307303 : Nat := 4983230072969 + 3 ^ 40 * 307303 * 2
def baseEnd_307303 : Nat := 52598048522905469766415

theorem tailTrace_307303 : CollatzResearch.WordTrace tailWord_307303 prefixEnd_307303 52598048522905469766415 := by
  unfold tailWord_307303
  simp only [CollatzResearch.WordTrace]
  refine ⟨11208261205701189019110563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7472174137134126012740375 11208261205701189019110563)
  ·
    refine ⟨16812391808551783528665845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11208261205701189019110563 16812391808551783528665845)
    ·
      refine ⟨1576161732051729705812423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16812391808551783528665845 1576161732051729705812423)
      ·
        refine ⟨2364242598077594558718635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576161732051729705812423 2364242598077594558718635)
        ·
          refine ⟨3546363897116391838077953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364242598077594558718635 3546363897116391838077953)
          ·
            refine ⟨2659772922837293878558465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546363897116391838077953 2659772922837293878558465)
            ·
              refine ⟨1994829692127970408918849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659772922837293878558465 1994829692127970408918849)
              ·
                refine ⟨1496122269095977806689137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994829692127970408918849 1496122269095977806689137)
                ·
                  refine ⟨1122091701821983355016853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496122269095977806689137 1122091701821983355016853)
                  ·
                    refine ⟨52598048522905469766415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1122091701821983355016853 52598048522905469766415)
                    ·
                      rfl

theorem cell23_307303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_307303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307303 prefixEnd_307303 := by exact prefixLift 307303
  have htrace : WordTrace (prefixWord ++ tailWord_307303) baseStart_307303 baseEnd_307303 := by
    simpa [prefixWord, tailWord_307303, baseEnd_307303] using wordTrace_append hprefix tailTrace_307303
  have hstable : (prefixWord ++ tailWord_307303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307303).length < 2 ^ (prefixWord ++ tailWord_307303).sum := by decide
  have hdescent : baseEnd_307303 < baseStart_307303 := by decide
  rcases family_descends (prefixWord ++ tailWord_307303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307313 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_307313 : Nat := 118140960795 + 307313 * 2 ^ 59
def prefixEnd_307313 : Nat := 4983230072969 + 3 ^ 40 * 307313 * 2
def baseEnd_307313 : Nat := 157799280375261370174199

theorem tailTrace_307313 : CollatzResearch.WordTrace tailWord_307313 prefixEnd_307313 157799280375261370174199 := by
  unfold tailWord_307313
  simp only [CollatzResearch.WordTrace]
  refine ⟨11208625935664960726974593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7472417290443307151316395 11208625935664960726974593)
  ·
    refine ⟨8406469451748720545230945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11208625935664960726974593 8406469451748720545230945)
    ·
      refine ⟨6304852088811540408923209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8406469451748720545230945 6304852088811540408923209)
      ·
        refine ⟨4728639066608655306692407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6304852088811540408923209 4728639066608655306692407)
        ·
          refine ⟨7092958599912982960038611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728639066608655306692407 7092958599912982960038611)
          ·
            refine ⟨10639437899869474440057917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7092958599912982960038611 10639437899869474440057917)
            ·
              refine ⟨3989789212451052915021719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10639437899869474440057917 3989789212451052915021719)
              ·
                refine ⟨5984683818676579372532579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989789212451052915021719 5984683818676579372532579)
                ·
                  refine ⟨8977025728014869058798869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5984683818676579372532579 8977025728014869058798869)
                  ·
                    refine ⟨420798081000696987131197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8977025728014869058798869 420798081000696987131197)
                    ·
                      refine ⟨157799280375261370174199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 420798081000696987131197 157799280375261370174199)
                      ·
                        rfl

theorem cell23_307313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_307313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307313 prefixEnd_307313 := by exact prefixLift 307313
  have htrace : WordTrace (prefixWord ++ tailWord_307313) baseStart_307313 baseEnd_307313 := by
    simpa [prefixWord, tailWord_307313, baseEnd_307313] using wordTrace_append hprefix tailTrace_307313
  have hstable : (prefixWord ++ tailWord_307313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307313).length < 2 ^ (prefixWord ++ tailWord_307313).sum := by decide
  have hdescent : baseEnd_307313 < baseStart_307313 := by decide
  rcases family_descends (prefixWord ++ tailWord_307313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307333 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 9]
def baseStart_307333 : Nat := 118140960795 + 307333 * 2 ^ 59
def prefixEnd_307333 : Nat := 4983230072969 + 3 ^ 40 * 307333 * 2
def baseEnd_307333 : Nat := 17534394443150143547123

theorem tailTrace_307333 : CollatzResearch.WordTrace tailWord_307333 prefixEnd_307333 17534394443150143547123 := by
  unfold tailWord_307333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11209355395592504142702653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7472903597061669428468435 11209355395592504142702653)
  ·
    refine ⟨4203508273347189053513495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11209355395592504142702653 4203508273347189053513495)
    ·
      refine ⟨6305262410020783580270243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203508273347189053513495 6305262410020783580270243)
      ·
        refine ⟨9457893615031175370405365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305262410020783580270243 9457893615031175370405365)
        ·
          refine ⟨886677526409172690975503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9457893615031175370405365 886677526409172690975503)
          ·
            refine ⟨1330016289613759036463255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886677526409172690975503 1330016289613759036463255)
            ·
              refine ⟨1995024434420638554694883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330016289613759036463255 1995024434420638554694883)
              ·
                refine ⟨2992536651630957832042325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995024434420638554694883 2992536651630957832042325)
                ·
                  refine ⟨17534394443150143547123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2992536651630957832042325 17534394443150143547123)
                  ·
                    rfl

theorem cell23_307333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_307333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307333 prefixEnd_307333 := by exact prefixLift 307333
  have htrace : WordTrace (prefixWord ++ tailWord_307333) baseStart_307333 baseEnd_307333 := by
    simpa [prefixWord, tailWord_307333, baseEnd_307333] using wordTrace_append hprefix tailTrace_307333
  have hstable : (prefixWord ++ tailWord_307333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307333).length < 2 ^ (prefixWord ++ tailWord_307333).sum := by decide
  have hdescent : baseEnd_307333 < baseStart_307333 := by decide
  rcases family_descends (prefixWord ++ tailWord_307333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307360 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_307360 : Nat := 118140960795 + 307360 * 2 ^ 59
def prefixEnd_307360 : Nat := 4983230072969 + 3 ^ 40 * 307360 * 2
def baseEnd_307360 : Nat := 157823413966022686286483

theorem tailTrace_307360 : CollatzResearch.WordTrace tailWord_307360 prefixEnd_307360 157823413966022686286483 := by
  unfold tailWord_307360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605170083247343876967767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7473560110996458502623689 5605170083247343876967767)
  ·
    refine ⟨8407755124871015815451651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5605170083247343876967767 8407755124871015815451651)
    ·
      refine ⟨12611632687306523723177477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8407755124871015815451651 12611632687306523723177477)
      ·
        refine ⟨2364681128869973198095777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12611632687306523723177477 2364681128869973198095777)
        ·
          refine ⟨1773510846652479898571833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364681128869973198095777 1773510846652479898571833)
          ·
            refine ⟨1330133134989359923928875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773510846652479898571833 1330133134989359923928875)
            ·
              refine ⟨1995199702484039885893313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330133134989359923928875 1995199702484039885893313)
              ·
                refine ⟨1496399776863029914419985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995199702484039885893313 1496399776863029914419985)
                ·
                  refine ⟨1122299832647272435814989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496399776863029914419985 1122299832647272435814989)
                  ·
                    refine ⟨420862437242727163430621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122299832647272435814989 420862437242727163430621)
                    ·
                      refine ⟨157823413966022686286483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 420862437242727163430621 157823413966022686286483)
                      ·
                        rfl

theorem cell23_307360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_307360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307360 prefixEnd_307360 := by exact prefixLift 307360
  have htrace : WordTrace (prefixWord ++ tailWord_307360) baseStart_307360 baseEnd_307360 := by
    simpa [prefixWord, tailWord_307360, baseEnd_307360] using wordTrace_append hprefix tailTrace_307360
  have hstable : (prefixWord ++ tailWord_307360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307360).length < 2 ^ (prefixWord ++ tailWord_307360).sum := by decide
  have hdescent : baseEnd_307360 < baseStart_307360 := by decide
  rcases family_descends (prefixWord ++ tailWord_307360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307361 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_307361 : Nat := 118140960795 + 307361 * 2 ^ 59
def prefixEnd_307361 : Nat := 4983230072969 + 3 ^ 40 * 307361 * 2
def baseEnd_307361 : Nat := 157823927446677182373979

theorem tailTrace_307361 : CollatzResearch.WordTrace tailWord_307361 prefixEnd_307361 157823927446677182373979 := by
  unfold tailWord_307361
  simp only [CollatzResearch.WordTrace]
  refine ⟨11210376639491064924721937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7473584426327376616481291 11210376639491064924721937)
  ·
    refine ⟨8407782479618298693541453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11210376639491064924721937 8407782479618298693541453)
    ·
      refine ⟨3152918429856862010078045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8407782479618298693541453 3152918429856862010078045)
      ·
        refine ⟨1182344411196323253779267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3152918429856862010078045 1182344411196323253779267)
        ·
          refine ⟨1773516616794484880668901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182344411196323253779267 1773516616794484880668901)
          ·
            refine ⟨332534365648965915125419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1773516616794484880668901 332534365648965915125419)
            ·
              refine ⟨498801548473448872688129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332534365648965915125419 498801548473448872688129)
              ·
                refine ⟨374101161355086654516097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498801548473448872688129 374101161355086654516097)
                ·
                  refine ⟨280575871016314990887073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374101161355086654516097 280575871016314990887073)
                  ·
                    refine ⟨210431903262236243165305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280575871016314990887073 210431903262236243165305)
                    ·
                      refine ⟨157823927446677182373979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210431903262236243165305 157823927446677182373979)
                      ·
                        rfl

theorem cell23_307361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_307361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307361 prefixEnd_307361 := by exact prefixLift 307361
  have htrace : WordTrace (prefixWord ++ tailWord_307361) baseStart_307361 baseEnd_307361 := by
    simpa [prefixWord, tailWord_307361, baseEnd_307361] using wordTrace_append hprefix tailTrace_307361
  have hstable : (prefixWord ++ tailWord_307361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307361).length < 2 ^ (prefixWord ++ tailWord_307361).sum := by decide
  have hdescent : baseEnd_307361 < baseStart_307361 := by decide
  rcases family_descends (prefixWord ++ tailWord_307361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307367 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 7]
def baseStart_307367 : Nat := 118140960795 + 307367 * 2 ^ 59
def prefixEnd_307367 : Nat := 4983230072969 + 3 ^ 40 * 307367 * 2
def baseEnd_307367 : Nat := 17536334258956017655439

theorem tailTrace_307367 : CollatzResearch.WordTrace tailWord_307367 prefixEnd_307367 17536334258956017655439 := by
  unfold tailWord_307367
  simp only [CollatzResearch.WordTrace]
  refine ⟨11210595477469327949440355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7473730318312885299626903 11210595477469327949440355)
  ·
    refine ⟨16815893216203991924160533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11210595477469327949440355 16815893216203991924160533)
    ·
      refine ⟨788244994509562121445025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16815893216203991924160533 788244994509562121445025)
      ·
        refine ⟨591183745882171591083769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788244994509562121445025 591183745882171591083769)
        ·
          refine ⟨443387809411628693312827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591183745882171591083769 443387809411628693312827)
          ·
            refine ⟨665081714117443039969241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443387809411628693312827 665081714117443039969241)
            ·
              refine ⟨498811285588082279976931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665081714117443039969241 498811285588082279976931)
              ·
                refine ⟨748216928382123419965397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498811285588082279976931 748216928382123419965397)
                ·
                  refine ⟨17536334258956017655439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 748216928382123419965397 17536334258956017655439)
                  ·
                    rfl

theorem cell23_307367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 7].length) (baseStart_307367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307367 prefixEnd_307367 := by exact prefixLift 307367
  have htrace : WordTrace (prefixWord ++ tailWord_307367) baseStart_307367 baseEnd_307367 := by
    simpa [prefixWord, tailWord_307367, baseEnd_307367] using wordTrace_append hprefix tailTrace_307367
  have hstable : (prefixWord ++ tailWord_307367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307367).length < 2 ^ (prefixWord ++ tailWord_307367).sum := by decide
  have hdescent : baseEnd_307367 < baseStart_307367 := by decide
  rcases family_descends (prefixWord ++ tailWord_307367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307400 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_307400 : Nat := 118140960795 + 307400 * 2 ^ 59
def prefixEnd_307400 : Nat := 4983230072969 + 3 ^ 40 * 307400 * 2
def baseEnd_307400 : Nat := 157843953192202529786299

theorem tailTrace_307400 : CollatzResearch.WordTrace tailWord_307400 prefixEnd_307400 157843953192202529786299 := by
  unfold tailWord_307400
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605899543174887292695827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7474532724233183056927769 5605899543174887292695827)
  ·
    refine ⟨8408849314762330939043741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5605899543174887292695827 8408849314762330939043741)
    ·
      refine ⟨3153318493035874102141403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8408849314762330939043741 3153318493035874102141403)
      ·
        refine ⟨4729977739553811153212105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153318493035874102141403 4729977739553811153212105)
        ·
          refine ⟨3547483304665358364909079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729977739553811153212105 3547483304665358364909079)
          ·
            refine ⟨5321224956998037547363619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547483304665358364909079 5321224956998037547363619)
            ·
              refine ⟨7981837435497056321045429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5321224956998037547363619 7981837435497056321045429)
              ·
                refine ⟨748297259577849030098009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7981837435497056321045429 748297259577849030098009)
                ·
                  refine ⟨561222944683386772573507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748297259577849030098009 561222944683386772573507)
                  ·
                    refine ⟨841834417025080158860261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 561222944683386772573507 841834417025080158860261)
                    ·
                      refine ⟨157843953192202529786299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 841834417025080158860261 157843953192202529786299)
                      ·
                        rfl

theorem cell23_307400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_307400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307400 prefixEnd_307400 := by exact prefixLift 307400
  have htrace : WordTrace (prefixWord ++ tailWord_307400) baseStart_307400 baseEnd_307400 := by
    simpa [prefixWord, tailWord_307400, baseEnd_307400] using wordTrace_append hprefix tailTrace_307400
  have hstable : (prefixWord ++ tailWord_307400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307400).length < 2 ^ (prefixWord ++ tailWord_307400).sum := by decide
  have hdescent : baseEnd_307400 < baseStart_307400 := by decide
  rcases family_descends (prefixWord ++ tailWord_307400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307414 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_307414 : Nat := 118140960795 + 307414 * 2 ^ 59
def prefixEnd_307414 : Nat := 4983230072969 + 3 ^ 40 * 307414 * 2
def baseEnd_307414 : Nat := 52617047307121825003745

theorem tailTrace_307414 : CollatzResearch.WordTrace tailWord_307414 prefixEnd_307414 52617047307121825003745 := by
  unfold tailWord_307414
  simp only [CollatzResearch.WordTrace]
  refine ⟨700769356768690936025081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7474873138866036650934197 700769356768690936025081)
  ·
    refine ⟨525577017576518202018811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 700769356768690936025081 525577017576518202018811)
    ·
      refine ⟨788365526364777303028217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525577017576518202018811 788365526364777303028217)
      ·
        refine ⟨591274144773582977271163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788365526364777303028217 591274144773582977271163)
        ·
          refine ⟨886911217160374465906745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591274144773582977271163 886911217160374465906745)
          ·
            refine ⟨665183412870280849430059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886911217160374465906745 665183412870280849430059)
            ·
              refine ⟨997775119305421274145089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665183412870280849430059 997775119305421274145089)
              ·
                refine ⟨748331339479065955608817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997775119305421274145089 748331339479065955608817)
                ·
                  refine ⟨561248504609299466706613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748331339479065955608817 561248504609299466706613)
                  ·
                    refine ⟨52617047307121825003745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 561248504609299466706613 52617047307121825003745)
                    ·
                      rfl

theorem cell23_307414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_307414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307414 prefixEnd_307414 := by exact prefixLift 307414
  have htrace : WordTrace (prefixWord ++ tailWord_307414) baseStart_307414 baseEnd_307414 := by
    simpa [prefixWord, tailWord_307414, baseEnd_307414] using wordTrace_append hprefix tailTrace_307414
  have hstable : (prefixWord ++ tailWord_307414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307414).length < 2 ^ (prefixWord ++ tailWord_307414).sum := by decide
  have hdescent : baseEnd_307414 < baseStart_307414 := by decide
  rcases family_descends (prefixWord ++ tailWord_307414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307454 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_307454 : Nat := 118140960795 + 307454 * 2 ^ 59
def prefixEnd_307454 : Nat := 4983230072969 + 3 ^ 40 * 307454 * 2
def baseEnd_307454 : Nat := 157871681147545318511051

theorem tailTrace_307454 : CollatzResearch.WordTrace tailWord_307454 prefixEnd_307454 157871681147545318511051 := by
  unfold tailWord_307454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401721078519267725982177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7475845752102761205238277 1401721078519267725982177)
  ·
    refine ⟨1051290808889450794486633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1401721078519267725982177 1051290808889450794486633)
    ·
      refine ⟨788468106667088095864975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1051290808889450794486633 788468106667088095864975)
      ·
        refine ⟨1182702160000632143797463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788468106667088095864975 1182702160000632143797463)
        ·
          refine ⟨1774053240000948215696195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182702160000632143797463 1774053240000948215696195)
          ·
            refine ⟨2661079860001422323544293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774053240000948215696195 2661079860001422323544293)
            ·
              refine ⟨498952473750266685664555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2661079860001422323544293 498952473750266685664555)
              ·
                refine ⟨748428710625400028496833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498952473750266685664555 748428710625400028496833)
                ·
                  refine ⟨561321532969050021372625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748428710625400028496833 561321532969050021372625)
                  ·
                    refine ⟨420991149726787516029469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 561321532969050021372625 420991149726787516029469)
                    ·
                      refine ⟨157871681147545318511051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 420991149726787516029469 157871681147545318511051)
                      ·
                        rfl

theorem cell23_307454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_307454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307454 prefixEnd_307454 := by exact prefixLift 307454
  have htrace : WordTrace (prefixWord ++ tailWord_307454) baseStart_307454 baseEnd_307454 := by
    simpa [prefixWord, tailWord_307454, baseEnd_307454] using wordTrace_append hprefix tailTrace_307454
  have hstable : (prefixWord ++ tailWord_307454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307454).length < 2 ^ (prefixWord ++ tailWord_307454).sum := by decide
  have hdescent : baseEnd_307454 < baseStart_307454 := by decide
  rcases family_descends (prefixWord ++ tailWord_307454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307500 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_307500 : Nat := 118140960795 + 307500 * 2 ^ 59
def prefixEnd_307500 : Nat := 4983230072969 + 3 ^ 40 * 307500 * 2
def baseEnd_307500 : Nat := 52631767085884046178613

theorem tailTrace_307500 : CollatzResearch.WordTrace tailWord_307500 prefixEnd_307500 52631767085884046178613 := by
  unfold tailWord_307500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607723192993745832015977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7476964257324994442687969 5607723192993745832015977)
  ·
    refine ⟨4205792394745309374011983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5607723192993745832015977 4205792394745309374011983)
    ·
      refine ⟨6308688592117964061017975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205792394745309374011983 6308688592117964061017975)
      ·
        refine ⟨9463032888176946091526963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6308688592117964061017975 9463032888176946091526963)
        ·
          refine ⟨14194549332265419137290445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9463032888176946091526963 14194549332265419137290445)
          ·
            refine ⟨5322955999599532176483917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14194549332265419137290445 5322955999599532176483917)
            ·
              refine ⟨1996108499849824566181469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5322955999599532176483917 1996108499849824566181469)
              ·
                refine ⟨748540687443684212318051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1996108499849824566181469 748540687443684212318051)
                ·
                  refine ⟨1122811031165526318477077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748540687443684212318051 1122811031165526318477077)
                  ·
                    refine ⟨52631767085884046178613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1122811031165526318477077 52631767085884046178613)
                    ·
                      rfl

theorem cell23_307500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_307500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307500 prefixEnd_307500 := by exact prefixLift 307500
  have htrace : WordTrace (prefixWord ++ tailWord_307500) baseStart_307500 baseEnd_307500 := by
    simpa [prefixWord, tailWord_307500, baseEnd_307500] using wordTrace_append hprefix tailTrace_307500
  have hstable : (prefixWord ++ tailWord_307500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307500).length < 2 ^ (prefixWord ++ tailWord_307500).sum := by decide
  have hdescent : baseEnd_307500 < baseStart_307500 := by decide
  rcases family_descends (prefixWord ++ tailWord_307500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
