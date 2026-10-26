import V185TrunkScan23Chunk0232

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1378538 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_1378538 : Nat := 118140960795 + 1378538 * 2 ^ 59
def prefixEnd_1378538 : Nat := 4983230072969 + 3 ^ 40 * 1378538 * 2
def baseEnd_1378538 : Nat := 707852594487832697435225

theorem tailTrace_1378538 : CollatzResearch.WordTrace tailWord_1378538 prefixEnd_1378538 707852594487832697435225 := by
  unfold tailWord_1378538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569852869949934097882067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33519607653199824261018845 12569852869949934097882067)
  ·
    refine ⟨18854779304924901146823101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12569852869949934097882067 18854779304924901146823101)
    ·
      refine ⟨7070542239346837930058663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18854779304924901146823101 7070542239346837930058663)
      ·
        refine ⟨10605813359020256895087995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7070542239346837930058663 10605813359020256895087995)
        ·
          refine ⟨15908720038530385342631993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10605813359020256895087995 15908720038530385342631993)
          ·
            refine ⟨11931540028897789006973995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15908720038530385342631993 11931540028897789006973995)
            ·
              refine ⟨17897310043346683510460993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11931540028897789006973995 17897310043346683510460993)
              ·
                refine ⟨13422982532510012632845745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17897310043346683510460993 13422982532510012632845745)
                ·
                  refine ⟨10067236899382509474634309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13422982532510012632845745 10067236899382509474634309)
                  ·
                    refine ⟨1887606918634220526493933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10067236899382509474634309 1887606918634220526493933)
                    ·
                      refine ⟨707852594487832697435225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887606918634220526493933 707852594487832697435225)
                      ·
                        rfl

theorem cell23_1378538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_1378538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378538 prefixEnd_1378538 := by exact prefixLift 1378538
  have htrace : WordTrace (prefixWord ++ tailWord_1378538) baseStart_1378538 baseEnd_1378538 := by
    simpa [prefixWord, tailWord_1378538, baseEnd_1378538] using wordTrace_append hprefix tailTrace_1378538
  have hstable : (prefixWord ++ tailWord_1378538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378538).length < 2 ^ (prefixWord ++ tailWord_1378538).sum := by decide
  have hdescent : baseEnd_1378538 < baseStart_1378538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378558 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_1378558 : Nat := 118140960795 + 1378558 * 2 ^ 59
def prefixEnd_1378558 : Nat := 4983230072969 + 3 ^ 40 * 1378558 * 2
def baseEnd_1378558 : Nat := 78651429344546957687237

theorem tailTrace_1378558 : CollatzResearch.WordTrace tailWord_1378558 prefixEnd_1378558 78651429344546957687237 := by
  unfold tailWord_1378558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285017617465909975907041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33520093959818186538170885 6285017617465909975907041)
  ·
    refine ⟨4713763213099432481930281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6285017617465909975907041 4713763213099432481930281)
    ·
      refine ⟨3535322409824574361447711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4713763213099432481930281 3535322409824574361447711)
      ·
        refine ⟨5302983614736861542171567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3535322409824574361447711 5302983614736861542171567)
        ·
          refine ⟨7954475422105292313257351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5302983614736861542171567 7954475422105292313257351)
          ·
            refine ⟨11931713133157938469886027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7954475422105292313257351 11931713133157938469886027)
            ·
              refine ⟨17897569699736907704829041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11931713133157938469886027 17897569699736907704829041)
              ·
                refine ⟨13423177274802680778621781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17897569699736907704829041 13423177274802680778621781)
                ·
                  refine ⟨78651429344546957687237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13423177274802680778621781 78651429344546957687237)
                  ·
                    rfl

theorem cell23_1378558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_1378558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378558 prefixEnd_1378558 := by exact prefixLift 1378558
  have htrace : WordTrace (prefixWord ++ tailWord_1378558) baseStart_1378558 baseEnd_1378558 := by
    simpa [prefixWord, tailWord_1378558, baseEnd_1378558] using wordTrace_append hprefix tailTrace_1378558
  have hstable : (prefixWord ++ tailWord_1378558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378558).length < 2 ^ (prefixWord ++ tailWord_1378558).sum := by decide
  have hdescent : baseEnd_1378558 < baseStart_1378558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378569 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 2, 2, 2]
def baseStart_1378569 : Nat := 118140960795 + 1378569 * 2 ^ 59
def prefixEnd_1378569 : Nat := 4983230072969 + 3 ^ 40 * 1378569 * 2
def baseEnd_1378569 : Nat := 707868512388122076147583

theorem tailTrace_1378569 : CollatzResearch.WordTrace tailWord_1378569 prefixEnd_1378569 707868512388122076147583 := by
  unfold tailWord_1378569
  simp only [CollatzResearch.WordTrace]
  refine ⟨50280542142687428685906761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33520361428458285790604507 50280542142687428685906761)
  ·
    refine ⟨37710406607015571514430071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50280542142687428685906761 37710406607015571514430071)
    ·
      refine ⟨56565609910523357271645107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37710406607015571514430071 56565609910523357271645107)
      ·
        refine ⟨84848414865785035907467661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56565609910523357271645107 84848414865785035907467661)
        ·
          refine ⟨31818155574669388465300373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84848414865785035907467661 31818155574669388465300373)
          ·
            refine ⟨1491476042562627584310955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31818155574669388465300373 1491476042562627584310955)
            ·
              refine ⟨2237214063843941376466433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491476042562627584310955 2237214063843941376466433)
              ·
                refine ⟨1677910547882956032349825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237214063843941376466433 1677910547882956032349825)
                ·
                  refine ⟨1258432910912217024262369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677910547882956032349825 1258432910912217024262369)
                  ·
                    refine ⟨943824683184162768196777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258432910912217024262369 943824683184162768196777)
                    ·
                      refine ⟨707868512388122076147583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943824683184162768196777 707868512388122076147583)
                      ·
                        rfl

theorem cell23_1378569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 2, 2].length) (baseStart_1378569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378569 prefixEnd_1378569 := by exact prefixLift 1378569
  have htrace : WordTrace (prefixWord ++ tailWord_1378569) baseStart_1378569 baseEnd_1378569 := by
    simpa [prefixWord, tailWord_1378569, baseEnd_1378569] using wordTrace_append hprefix tailTrace_1378569
  have hstable : (prefixWord ++ tailWord_1378569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378569).length < 2 ^ (prefixWord ++ tailWord_1378569).sum := by decide
  have hdescent : baseEnd_1378569 < baseStart_1378569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378586 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2]
def baseStart_1378586 : Nat := 118140960795 + 1378586 * 2 ^ 59
def prefixEnd_1378586 : Nat := 4983230072969 + 3 ^ 40 * 1378586 * 2
def baseEnd_1378586 : Nat := 707877241559248509635005

theorem tailTrace_1378586 : CollatzResearch.WordTrace tailWord_1378586 prefixEnd_1378586 707877241559248509635005 := by
  unfold tailWord_1378586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570290545906460147318903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33520774789083893726183741 12570290545906460147318903)
  ·
    refine ⟨18855435818859690220978355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12570290545906460147318903 18855435818859690220978355)
    ·
      refine ⟨28283153728289535331467533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18855435818859690220978355 28283153728289535331467533)
      ·
        refine ⟨10606182648108575749300325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28283153728289535331467533 10606182648108575749300325)
        ·
          refine ⟨1988659246520357952993811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10606182648108575749300325 1988659246520357952993811)
          ·
            refine ⟨2982988869780536929490717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988659246520357952993811 2982988869780536929490717)
            ·
              refine ⟨1118620826167701348559019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2982988869780536929490717 1118620826167701348559019)
              ·
                refine ⟨1677931239251552022838529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118620826167701348559019 1677931239251552022838529)
                ·
                  refine ⟨1258448429438664017128897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677931239251552022838529 1258448429438664017128897)
                  ·
                    refine ⟨943836322078998012846673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258448429438664017128897 943836322078998012846673)
                    ·
                      refine ⟨707877241559248509635005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943836322078998012846673 707877241559248509635005)
                      ·
                        rfl

theorem cell23_1378586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_1378586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378586 prefixEnd_1378586 := by exact prefixLift 1378586
  have htrace : WordTrace (prefixWord ++ tailWord_1378586) baseStart_1378586 baseEnd_1378586 := by
    simpa [prefixWord, tailWord_1378586, baseEnd_1378586] using wordTrace_append hprefix tailTrace_1378586
  have hstable : (prefixWord ++ tailWord_1378586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378586).length < 2 ^ (prefixWord ++ tailWord_1378586).sum := by decide
  have hdescent : baseEnd_1378586 < baseStart_1378586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378609 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 5]
def baseStart_1378609 : Nat := 118140960795 + 1378609 * 2 ^ 59
def prefixEnd_1378609 : Nat := 4983230072969 + 3 ^ 40 * 1378609 * 2
def baseEnd_1378609 : Nat := 78654339068255768849711

theorem tailTrace_1378609 : CollatzResearch.WordTrace tailWord_1378609 prefixEnd_1378609 78654339068255768849711 := by
  unfold tailWord_1378609
  simp only [CollatzResearch.WordTrace]
  refine ⟨50282001062542515517362881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33521334041695010344908587 50282001062542515517362881)
  ·
    refine ⟨37711500796906886638022161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50282001062542515517362881 37711500796906886638022161)
    ·
      refine ⟨28283625597680164978516621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37711500796906886638022161 28283625597680164978516621)
      ·
        refine ⟨10606359599130061866943733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28283625597680164978516621 10606359599130061866943733)
        ·
          refine ⟨994346212418443300025975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10606359599130061866943733 994346212418443300025975)
          ·
            refine ⟨1491519318627664950038963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994346212418443300025975 1491519318627664950038963)
            ·
              refine ⟨2237278977941497425058445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491519318627664950038963 2237278977941497425058445)
              ·
                refine ⟨838979616728061534396917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2237278977941497425058445 838979616728061534396917)
                ·
                  refine ⟨78654339068255768849711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838979616728061534396917 78654339068255768849711)
                  ·
                    rfl

theorem cell23_1378609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 5].length) (baseStart_1378609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378609 prefixEnd_1378609 := by exact prefixLift 1378609
  have htrace : WordTrace (prefixWord ++ tailWord_1378609) baseStart_1378609 baseEnd_1378609 := by
    simpa [prefixWord, tailWord_1378609, baseEnd_1378609] using wordTrace_append hprefix tailTrace_1378609
  have hstable : (prefixWord ++ tailWord_1378609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378609).length < 2 ^ (prefixWord ++ tailWord_1378609).sum := by decide
  have hdescent : baseEnd_1378609 < baseStart_1378609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378638 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1378638 : Nat := 118140960795 + 1378638 * 2 ^ 59
def prefixEnd_1378638 : Nat := 4983230072969 + 3 ^ 40 * 1378638 * 2
def baseEnd_1378638 : Nat := 707903942553282306184765

theorem tailTrace_1378638 : CollatzResearch.WordTrace tailWord_1378638 prefixEnd_1378638 707903942553282306184765 := by
  unfold tailWord_1378638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285382347429681683771071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33522039186291635646779045 6285382347429681683771071)
  ·
    refine ⟨9428073521144522525656607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6285382347429681683771071 9428073521144522525656607)
    ·
      refine ⟨14142110281716783788484911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9428073521144522525656607 14142110281716783788484911)
      ·
        refine ⟨21213165422575175682727367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14142110281716783788484911 21213165422575175682727367)
        ·
          refine ⟨31819748133862763524091051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21213165422575175682727367 31819748133862763524091051)
          ·
            refine ⟨47729622200794145286136577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31819748133862763524091051 47729622200794145286136577)
            ·
              refine ⟨35797216650595608964602433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47729622200794145286136577 35797216650595608964602433)
              ·
                refine ⟨26847912487946706723451825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35797216650595608964602433 26847912487946706723451825)
                ·
                  refine ⟨20135934365960030042588869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26847912487946706723451825 20135934365960030042588869)
                  ·
                    refine ⟨3775487693617505632985413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20135934365960030042588869 3775487693617505632985413)
                    ·
                      refine ⟨707903942553282306184765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3775487693617505632985413 707903942553282306184765)
                      ·
                        rfl

theorem cell23_1378638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1378638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378638 prefixEnd_1378638 := by exact prefixLift 1378638
  have htrace : WordTrace (prefixWord ++ tailWord_1378638) baseStart_1378638 baseEnd_1378638 := by
    simpa [prefixWord, tailWord_1378638, baseEnd_1378638] using wordTrace_append hprefix tailTrace_1378638
  have hstable : (prefixWord ++ tailWord_1378638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378638).length < 2 ^ (prefixWord ++ tailWord_1378638).sum := by decide
  have hdescent : baseEnd_1378638 < baseStart_1378638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378675 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 3]
def baseStart_1378675 : Nat := 118140960795 + 1378675 * 2 ^ 59
def prefixEnd_1378675 : Nat := 4983230072969 + 3 ^ 40 * 1378675 * 2
def baseEnd_1378675 : Nat := 707922941337498661422095

theorem tailTrace_1378675 : CollatzResearch.WordTrace tailWord_1378675 prefixEnd_1378675 707922941337498661422095 := by
  unfold tailWord_1378675
  simp only [CollatzResearch.WordTrace]
  refine ⟨50284408280303408789265479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33522938853535605859510319 50284408280303408789265479)
  ·
    refine ⟨75426612420455113183898219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50284408280303408789265479 75426612420455113183898219)
    ·
      refine ⟨113139918630682669775847329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75426612420455113183898219 113139918630682669775847329)
      ·
        refine ⟨84854938973012002331885497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113139918630682669775847329 84854938973012002331885497)
        ·
          refine ⟨63641204229759001748914123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84854938973012002331885497 63641204229759001748914123)
          ·
            refine ⟨95461806344638502623371185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63641204229759001748914123 95461806344638502623371185)
            ·
              refine ⟨71596354758478876967528389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95461806344638502623371185 71596354758478876967528389)
              ·
                refine ⟨13424316517214789431411573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71596354758478876967528389 13424316517214789431411573)
                ·
                  refine ⟨1258529673488886509194835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13424316517214789431411573 1258529673488886509194835)
                  ·
                    refine ⟨1887794510233329763792253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258529673488886509194835 1887794510233329763792253)
                    ·
                      refine ⟨707922941337498661422095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887794510233329763792253 707922941337498661422095)
                      ·
                        rfl

theorem cell23_1378675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_1378675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378675 prefixEnd_1378675 := by exact prefixLift 1378675
  have htrace : WordTrace (prefixWord ++ tailWord_1378675) baseStart_1378675 baseEnd_1378675 := by
    simpa [prefixWord, tailWord_1378675, baseEnd_1378675] using wordTrace_append hprefix tailTrace_1378675
  have hstable : (prefixWord ++ tailWord_1378675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378675).length < 2 ^ (prefixWord ++ tailWord_1378675).sum := by decide
  have hdescent : baseEnd_1378675 < baseStart_1378675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378692 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1378692 : Nat := 118140960795 + 1378692 * 2 ^ 59
def prefixEnd_1378692 : Nat := 4983230072969 + 3 ^ 40 * 1378692 * 2
def baseEnd_1378692 : Nat := 707931670508625094909517

theorem tailTrace_1378692 : CollatzResearch.WordTrace tailWord_1378692 prefixEnd_1378692 707931670508625094909517 := by
  unfold tailWord_1378692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25142514160620910346317165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33523352214161213795089553 25142514160620910346317165)
  ·
    refine ⟨9428442810232841379868937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25142514160620910346317165 9428442810232841379868937)
    ·
      refine ⟨7071332107674631034901703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9428442810232841379868937 7071332107674631034901703)
      ·
        refine ⟨10606998161511946552352555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071332107674631034901703 10606998161511946552352555)
        ·
          refine ⟨15910497242267919828528833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10606998161511946552352555 15910497242267919828528833)
          ·
            refine ⟨11932872931700939871396625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15910497242267919828528833 11932872931700939871396625)
            ·
              refine ⟨8949654698775704903547469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11932872931700939871396625 8949654698775704903547469)
              ·
                refine ⟨3356120512040889338830301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8949654698775704903547469 3356120512040889338830301)
                ·
                  refine ⟨1258545192015333502061363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3356120512040889338830301 1258545192015333502061363)
                  ·
                    refine ⟨1887817788023000253092045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258545192015333502061363 1887817788023000253092045)
                    ·
                      refine ⟨707931670508625094909517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887817788023000253092045 707931670508625094909517)
                      ·
                        rfl

theorem cell23_1378692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1378692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378692 prefixEnd_1378692 := by exact prefixLift 1378692
  have htrace : WordTrace (prefixWord ++ tailWord_1378692) baseStart_1378692 baseEnd_1378692 := by
    simpa [prefixWord, tailWord_1378692, baseEnd_1378692] using wordTrace_append hprefix tailTrace_1378692
  have hstable : (prefixWord ++ tailWord_1378692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378692).length < 2 ^ (prefixWord ++ tailWord_1378692).sum := by decide
  have hdescent : baseEnd_1378692 < baseStart_1378692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378710 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1378710 : Nat := 118140960795 + 1378710 * 2 ^ 59
def prefixEnd_1378710 : Nat := 4983230072969 + 3 ^ 40 * 1378710 * 2
def baseEnd_1378710 : Nat := 707940913160406024484435

theorem tailTrace_1378710 : CollatzResearch.WordTrace tailWord_1378710 prefixEnd_1378710 707940913160406024484435 := by
  unfold tailWord_1378710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142855302198538110424349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33523789890117739844526389 3142855302198538110424349)
  ·
    refine ⟨1178570738324451791409131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3142855302198538110424349 1178570738324451791409131)
    ·
      refine ⟨1767856107486677687113697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178570738324451791409131 1767856107486677687113697)
      ·
        refine ⟨1325892080615008265335273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1767856107486677687113697 1325892080615008265335273)
        ·
          refine ⟨994419060461256199001455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1325892080615008265335273 994419060461256199001455)
          ·
            refine ⟨1491628590691884298502183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994419060461256199001455 1491628590691884298502183)
            ·
              refine ⟨2237442886037826447753275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491628590691884298502183 2237442886037826447753275)
              ·
                refine ⟨3356164329056739671629913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237442886037826447753275 3356164329056739671629913)
                ·
                  refine ⟨2517123246792554753722435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356164329056739671629913 2517123246792554753722435)
                  ·
                    refine ⟨3775684870188832130583653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517123246792554753722435 3775684870188832130583653)
                    ·
                      refine ⟨707940913160406024484435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3775684870188832130583653 707940913160406024484435)
                      ·
                        rfl

theorem cell23_1378710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1378710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378710 prefixEnd_1378710 := by exact prefixLift 1378710
  have htrace : WordTrace (prefixWord ++ tailWord_1378710) baseStart_1378710 baseEnd_1378710 := by
    simpa [prefixWord, tailWord_1378710, baseEnd_1378710] using wordTrace_append hprefix tailTrace_1378710
  have hstable : (prefixWord ++ tailWord_1378710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378710).length < 2 ^ (prefixWord ++ tailWord_1378710).sum := by decide
  have hdescent : baseEnd_1378710 < baseStart_1378710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378725 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_1378725 : Nat := 118140960795 + 1378725 * 2 ^ 59
def prefixEnd_1378725 : Nat := 4983230072969 + 3 ^ 40 * 1378725 * 2
def baseEnd_1378725 : Nat := 235982871790074488598955

theorem tailTrace_1378725 : CollatzResearch.WordTrace tailWord_1378725 prefixEnd_1378725 235982871790074488598955 := by
  unfold tailWord_1378725
  simp only [CollatzResearch.WordTrace]
  refine ⟨50286231930122267328585629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33524154620081511552390419 50286231930122267328585629)
  ·
    refine ⟨18857336973795850248219611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50286231930122267328585629 18857336973795850248219611)
    ·
      refine ⟨28286005460693775372329417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18857336973795850248219611 28286005460693775372329417)
      ·
        refine ⟨21214504095520331529247063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28286005460693775372329417 21214504095520331529247063)
        ·
          refine ⟨31821756143280497293870595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21214504095520331529247063 31821756143280497293870595)
          ·
            refine ⟨47732634214920745940805893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31821756143280497293870595 47732634214920745940805893)
            ·
              refine ⟨8949868915297639863901105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47732634214920745940805893 8949868915297639863901105)
              ·
                refine ⟨6712401686473229897925829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8949868915297639863901105 6712401686473229897925829)
                ·
                  refine ⟨1258575316213730605861093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6712401686473229897925829 1258575316213730605861093)
                  ·
                    refine ⟨235982871790074488598955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1258575316213730605861093 235982871790074488598955)
                    ·
                      rfl

theorem cell23_1378725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_1378725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378725 prefixEnd_1378725 := by exact prefixLift 1378725
  have htrace : WordTrace (prefixWord ++ tailWord_1378725) baseStart_1378725 baseEnd_1378725 := by
    simpa [prefixWord, tailWord_1378725, baseEnd_1378725] using wordTrace_append hprefix tailTrace_1378725
  have hstable : (prefixWord ++ tailWord_1378725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378725).length < 2 ^ (prefixWord ++ tailWord_1378725).sum := by decide
  have hdescent : baseEnd_1378725 < baseStart_1378725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378732 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 7, 2, 2]
def baseStart_1378732 : Nat := 118140960795 + 1378732 * 2 ^ 59
def prefixEnd_1378732 : Nat := 4983230072969 + 3 ^ 40 * 1378732 * 2
def baseEnd_1378732 : Nat := 707952209734804938409333

theorem tailTrace_1378732 : CollatzResearch.WordTrace tailWord_1378732 prefixEnd_1378732 707952209734804938409333 := by
  unfold tailWord_1378732
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143243620548453762045225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33524324827397938349393633 25143243620548453762045225)
  ·
    refine ⟨18857432715411340321533919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25143243620548453762045225 18857432715411340321533919)
    ·
      refine ⟨28286149073117010482300879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18857432715411340321533919 28286149073117010482300879)
      ·
        refine ⟨42429223609675515723451319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28286149073117010482300879 42429223609675515723451319)
        ·
          refine ⟨63643835414513273585176979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42429223609675515723451319 63643835414513273585176979)
          ·
            refine ⟨95465753121769910377765469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63643835414513273585176979 95465753121769910377765469)
            ·
              refine ⟨35799657420663716391662051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95465753121769910377765469 35799657420663716391662051)
              ·
                refine ⟨53699486130995574587493077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35799657420663716391662051 53699486130995574587493077)
                ·
                  refine ⟨1258581706195208779394369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53699486130995574587493077 1258581706195208779394369)
                  ·
                    refine ⟨943936279646406584545777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258581706195208779394369 943936279646406584545777)
                    ·
                      refine ⟨707952209734804938409333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943936279646406584545777 707952209734804938409333)
                      ·
                        rfl

theorem cell23_1378732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_1378732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378732 prefixEnd_1378732 := by exact prefixLift 1378732
  have htrace : WordTrace (prefixWord ++ tailWord_1378732) baseStart_1378732 baseEnd_1378732 := by
    simpa [prefixWord, tailWord_1378732, baseEnd_1378732] using wordTrace_append hprefix tailTrace_1378732
  have hstable : (prefixWord ++ tailWord_1378732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378732).length < 2 ^ (prefixWord ++ tailWord_1378732).sum := by decide
  have hdescent : baseEnd_1378732 < baseStart_1378732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378738 : List Nat := [3, 2, 1, 1, 1, 1, 14]
def baseStart_1378738 : Nat := 118140960795 + 1378738 * 2 ^ 59
def prefixEnd_1378738 : Nat := 4983230072969 + 3 ^ 40 * 1378738 * 2
def baseEnd_1378738 : Nat := 8740188773070764381905

theorem tailTrace_1378738 : CollatzResearch.WordTrace tailWord_1378738 prefixEnd_1378738 8740188773070764381905 := by
  unfold tailWord_1378738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571676519768792637202217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33524470719383447032539245 12571676519768792637202217)
  ·
    refine ⟨9428757389826594477901663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12571676519768792637202217 9428757389826594477901663)
    ·
      refine ⟨14143136084739891716852495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9428757389826594477901663 14143136084739891716852495)
      ·
        refine ⟨21214704127109837575278743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14143136084739891716852495 21214704127109837575278743)
        ·
          refine ⟨31822056190664756362918115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21214704127109837575278743 31822056190664756362918115)
          ·
            refine ⟨47733084285997134544377173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31822056190664756362918115 47733084285997134544377173)
            ·
              refine ⟨8740188773070764381905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 47733084285997134544377173 8740188773070764381905)
              ·
                rfl

theorem cell23_1378738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 14].length) (baseStart_1378738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378738 prefixEnd_1378738 := by exact prefixLift 1378738
  have htrace : WordTrace (prefixWord ++ tailWord_1378738) baseStart_1378738 baseEnd_1378738 := by
    simpa [prefixWord, tailWord_1378738, baseEnd_1378738] using wordTrace_append hprefix tailTrace_1378738
  have hstable : (prefixWord ++ tailWord_1378738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378738).length < 2 ^ (prefixWord ++ tailWord_1378738).sum := by decide
  have hdescent : baseEnd_1378738 < baseStart_1378738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378749 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_1378749 : Nat := 118140960795 + 1378749 * 2 ^ 59
def prefixEnd_1378749 : Nat := 4983230072969 + 3 ^ 40 * 1378749 * 2
def baseEnd_1378749 : Nat := 707960938905931371896755

theorem tailTrace_1378749 : CollatzResearch.WordTrace tailWord_1378749 prefixEnd_1378749 707960938905931371896755 := by
  unfold tailWord_1378749
  simp only [CollatzResearch.WordTrace]
  refine ⟨50287107282035319427459301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33524738188023546284972867 50287107282035319427459301)
  ·
    refine ⟨9428832615381622392648619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50287107282035319427459301 9428832615381622392648619)
    ·
      refine ⟨14143248923072433588972929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9428832615381622392648619 14143248923072433588972929)
      ·
        refine ⟨10607436692304325191729697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14143248923072433588972929 10607436692304325191729697)
        ·
          refine ⟨7955577519228243893797273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10607436692304325191729697 7955577519228243893797273)
          ·
            refine ⟨5966683139421182920347955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7955577519228243893797273 5966683139421182920347955)
            ·
              refine ⟨8950024709131774380521933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5966683139421182920347955 8950024709131774380521933)
              ·
                refine ⟨3356259265924415392695725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8950024709131774380521933 3356259265924415392695725)
                ·
                  refine ⟨1258597224721655772260897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3356259265924415392695725 1258597224721655772260897)
                  ·
                    refine ⟨943947918541241829195673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258597224721655772260897 943947918541241829195673)
                    ·
                      refine ⟨707960938905931371896755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943947918541241829195673 707960938905931371896755)
                      ·
                        rfl

theorem cell23_1378749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_1378749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378749 prefixEnd_1378749 := by exact prefixLift 1378749
  have htrace : WordTrace (prefixWord ++ tailWord_1378749) baseStart_1378749 baseEnd_1378749 := by
    simpa [prefixWord, tailWord_1378749, baseEnd_1378749] using wordTrace_append hprefix tailTrace_1378749
  have hstable : (prefixWord ++ tailWord_1378749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378749).length < 2 ^ (prefixWord ++ tailWord_1378749).sum := by decide
  have hdescent : baseEnd_1378749 < baseStart_1378749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378759 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 2, 4]
def baseStart_1378759 : Nat := 118140960795 + 1378759 * 2 ^ 59
def prefixEnd_1378759 : Nat := 4983230072969 + 3 ^ 40 * 1378759 * 2
def baseEnd_1378759 : Nat := 235988691237492110923903

theorem tailTrace_1378759 : CollatzResearch.WordTrace tailWord_1378759 prefixEnd_1378759 235988691237492110923903 := by
  unfold tailWord_1378759
  simp only [CollatzResearch.WordTrace]
  refine ⟨50287472011999091135323331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33524981341332727423548887 50287472011999091135323331)
  ·
    refine ⟨75431208017998636702984997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50287472011999091135323331 75431208017998636702984997)
    ·
      refine ⟨14143351503374744381809687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75431208017998636702984997 14143351503374744381809687)
      ·
        refine ⟨21215027255062116572714531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14143351503374744381809687 21215027255062116572714531)
        ·
          refine ⟨31822540882593174859071797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21215027255062116572714531 31822540882593174859071797)
          ·
            refine ⟨2983363207743110143037981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31822540882593174859071797 2983363207743110143037981)
            ·
              refine ⟨1118761202903666303639243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2983363207743110143037981 1118761202903666303639243)
              ·
                refine ⟨1678141804355499455458865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118761202903666303639243 1678141804355499455458865)
                ·
                  refine ⟨1258606353266624591594149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1678141804355499455458865 1258606353266624591594149)
                  ·
                    refine ⟨235988691237492110923903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1258606353266624591594149 235988691237492110923903)
                    ·
                      rfl

theorem cell23_1378759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_1378759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378759 prefixEnd_1378759 := by exact prefixLift 1378759
  have htrace : WordTrace (prefixWord ++ tailWord_1378759) baseStart_1378759 baseEnd_1378759 := by
    simpa [prefixWord, tailWord_1378759, baseEnd_1378759] using wordTrace_append hprefix tailTrace_1378759
  have hstable : (prefixWord ++ tailWord_1378759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378759).length < 2 ^ (prefixWord ++ tailWord_1378759).sum := by decide
  have hdescent : baseEnd_1378759 < baseStart_1378759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378772 : List Nat := [2, 4, 1, 2, 2, 1, 4, 7]
def baseStart_1378772 : Nat := 118140960795 + 1378772 * 2 ^ 59
def prefixEnd_1378772 : Nat := 4983230072969 + 3 ^ 40 * 1378772 * 2
def baseEnd_1378772 : Nat := 26221212924480917848487

theorem tailTrace_1378772 : CollatzResearch.WordTrace tailWord_1378772 prefixEnd_1378772 26221212924480917848487 := by
  unfold tailWord_1378772
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143973080475997177773285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33525297440634662903697713 25143973080475997177773285)
  ·
    refine ⟨4714494952589249470832491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25143973080475997177773285 4714494952589249470832491)
    ·
      refine ⟨7071742428883874206248737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714494952589249470832491 7071742428883874206248737)
      ·
        refine ⟨5303806821662905654686553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7071742428883874206248737 5303806821662905654686553)
        ·
          refine ⟨3977855116247179241014915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5303806821662905654686553 3977855116247179241014915)
          ·
            refine ⟨5966782674370768861522373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977855116247179241014915 5966782674370768861522373)
            ·
              refine ⟨1118771751444519161535445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5966782674370768861522373 1118771751444519161535445)
              ·
                refine ⟨26221212924480917848487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1118771751444519161535445 26221212924480917848487)
                ·
                  rfl

theorem cell23_1378772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 7].length) (baseStart_1378772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378772 prefixEnd_1378772 := by exact prefixLift 1378772
  have htrace : WordTrace (prefixWord ++ tailWord_1378772) baseStart_1378772 baseEnd_1378772 := by
    simpa [prefixWord, tailWord_1378772, baseEnd_1378772] using wordTrace_append hprefix tailTrace_1378772
  have hstable : (prefixWord ++ tailWord_1378772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378772).length < 2 ^ (prefixWord ++ tailWord_1378772).sum := by decide
  have hdescent : baseEnd_1378772 < baseStart_1378772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378783 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 1, 2, 2]
def baseStart_1378783 : Nat := 118140960795 + 1378783 * 2 ^ 59
def prefixEnd_1378783 : Nat := 4983230072969 + 3 ^ 40 * 1378783 * 2
def baseEnd_1378783 : Nat := 707978397248184238871599

theorem tailTrace_1378783 : CollatzResearch.WordTrace tailWord_1378783 prefixEnd_1378783 707978397248184238871599 := by
  unfold tailWord_1378783
  simp only [CollatzResearch.WordTrace]
  refine ⟨50288347363912143234197003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33525564909274762156131335 50288347363912143234197003)
  ·
    refine ⟨75432521045868214851295505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50288347363912143234197003 75432521045868214851295505)
    ·
      refine ⟨56574390784401161138471629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75432521045868214851295505 56574390784401161138471629)
      ·
        refine ⟨21215396544150435426926861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56574390784401161138471629 21215396544150435426926861)
        ·
          refine ⟨7955773704056413285097573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21215396544150435426926861 7955773704056413285097573)
          ·
            refine ⟨1491707569510577490955795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7955773704056413285097573 1491707569510577490955795)
            ·
              refine ⟨2237561354265866236433693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491707569510577490955795 2237561354265866236433693)
              ·
                refine ⟨839085507849699838662635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2237561354265866236433693 839085507849699838662635)
                ·
                  refine ⟨1258628261774549757993953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839085507849699838662635 1258628261774549757993953)
                  ·
                    refine ⟨943971196330912318495465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258628261774549757993953 943971196330912318495465)
                    ·
                      refine ⟨707978397248184238871599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 943971196330912318495465 707978397248184238871599)
                      ·
                        rfl

theorem cell23_1378783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_1378783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378783 prefixEnd_1378783 := by exact prefixLift 1378783
  have htrace : WordTrace (prefixWord ++ tailWord_1378783) baseStart_1378783 baseEnd_1378783 := by
    simpa [prefixWord, tailWord_1378783, baseEnd_1378783] using wordTrace_append hprefix tailTrace_1378783
  have hstable : (prefixWord ++ tailWord_1378783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378783).length < 2 ^ (prefixWord ++ tailWord_1378783).sum := by decide
  have hdescent : baseEnd_1378783 < baseStart_1378783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378786 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1378786 : Nat := 118140960795 + 1378786 * 2 ^ 59
def prefixEnd_1378786 : Nat := 4983230072969 + 3 ^ 40 * 1378786 * 2
def baseEnd_1378786 : Nat := 707979937690147727134085

theorem tailTrace_1378786 : CollatzResearch.WordTrace tailWord_1378786 prefixEnd_1378786 707979937690147727134085 := by
  unfold tailWord_1378786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572114195725318686639053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33525637855267516497704141 12572114195725318686639053)
  ·
    refine ⟨4714542823396994507489645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12572114195725318686639053 4714542823396994507489645)
    ·
      refine ⟨1767953558773872940308617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4714542823396994507489645 1767953558773872940308617)
      ·
        refine ⟨1325965169080404705231463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1767953558773872940308617 1325965169080404705231463)
        ·
          refine ⟨1988947753620607057847195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325965169080404705231463 1988947753620607057847195)
          ·
            refine ⟨2983421630430910586770793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988947753620607057847195 2983421630430910586770793)
            ·
              refine ⟨2237566222823182940078095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983421630430910586770793 2237566222823182940078095)
              ·
                refine ⟨3356349334234774410117143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237566222823182940078095 3356349334234774410117143)
                ·
                  refine ⟨5034524001352161615175715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356349334234774410117143 5034524001352161615175715)
                  ·
                    refine ⟨7551786002028242422763573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5034524001352161615175715 7551786002028242422763573)
                    ·
                      refine ⟨707979937690147727134085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7551786002028242422763573 707979937690147727134085)
                      ·
                        rfl

theorem cell23_1378786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1378786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378786 prefixEnd_1378786 := by exact prefixLift 1378786
  have htrace : WordTrace (prefixWord ++ tailWord_1378786) baseStart_1378786 baseEnd_1378786 := by
    simpa [prefixWord, tailWord_1378786, baseEnd_1378786] using wordTrace_append hprefix tailTrace_1378786
  have hstable : (prefixWord ++ tailWord_1378786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378786).length < 2 ^ (prefixWord ++ tailWord_1378786).sum := by decide
  have hdescent : baseEnd_1378786 < baseStart_1378786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378825 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_1378825 : Nat := 118140960795 + 1378825 * 2 ^ 59
def prefixEnd_1378825 : Nat := 4983230072969 + 3 ^ 40 * 1378825 * 2
def baseEnd_1378825 : Nat := 707999963435673074546405

theorem tailTrace_1378825 : CollatzResearch.WordTrace tailWord_1378825 prefixEnd_1378825 707999963435673074546405 := by
  unfold tailWord_1378825
  simp only [CollatzResearch.WordTrace]
  refine ⟨50289879229759984407225929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33526586153173322938150619 50289879229759984407225929)
  ·
    refine ⟨37717409422319988305419447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50289879229759984407225929 37717409422319988305419447)
    ·
      refine ⟨56576114133479982458129171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37717409422319988305419447 56576114133479982458129171)
      ·
        refine ⟨84864171200219973687193757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56576114133479982458129171 84864171200219973687193757)
        ·
          refine ⟨31824064200082490132697659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84864171200219973687193757 31824064200082490132697659)
          ·
            refine ⟨47736096300123735199046489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31824064200082490132697659 47736096300123735199046489)
            ·
              refine ⟨35802072225092801399284867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47736096300123735199046489 35802072225092801399284867)
              ·
                refine ⟨53703108337639202098927301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35802072225092801399284867 53703108337639202098927301)
                ·
                  refine ⟨10069332813307350393548869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53703108337639202098927301 10069332813307350393548869)
                  ·
                    refine ⟨1887999902495128198790413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10069332813307350393548869 1887999902495128198790413)
                    ·
                      refine ⟨707999963435673074546405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1887999902495128198790413 707999963435673074546405)
                      ·
                        rfl

theorem cell23_1378825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_1378825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378825 prefixEnd_1378825 := by exact prefixLift 1378825
  have htrace : WordTrace (prefixWord ++ tailWord_1378825) baseStart_1378825 baseEnd_1378825 := by
    simpa [prefixWord, tailWord_1378825, baseEnd_1378825] using wordTrace_append hprefix tailTrace_1378825
  have hstable : (prefixWord ++ tailWord_1378825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378825).length < 2 ^ (prefixWord ++ tailWord_1378825).sum := by decide
  have hdescent : baseEnd_1378825 < baseStart_1378825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378872 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_1378872 : Nat := 118140960795 + 1378872 * 2 ^ 59
def prefixEnd_1378872 : Nat := 4983230072969 + 3 ^ 40 * 1378872 * 2
def baseEnd_1378872 : Nat := 708024097026434390658689

theorem tailTrace_1378872 : CollatzResearch.WordTrace tailWord_1378872 prefixEnd_1378872 708024097026434390658689 := by
  unfold tailWord_1378872
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145796730294855717093435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33527728973726474289457913 25145796730294855717093435)
  ·
    refine ⟨37718695095442283575640153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25145796730294855717093435 37718695095442283575640153)
    ·
      refine ⟨28289021321581712681730115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37718695095442283575640153 28289021321581712681730115)
      ·
        refine ⟨42433531982372569022595173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28289021321581712681730115 42433531982372569022595173)
        ·
          refine ⟨7956287246694856691736595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42433531982372569022595173 7956287246694856691736595)
          ·
            refine ⟨11934430870042285037604893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956287246694856691736595 11934430870042285037604893)
            ·
              refine ⟨4475411576265856889101835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11934430870042285037604893 4475411576265856889101835)
              ·
                refine ⟨6713117364398785333652753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475411576265856889101835 6713117364398785333652753)
                ·
                  refine ⟨5034838023299089000239565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6713117364398785333652753 5034838023299089000239565)
                  ·
                    refine ⟨1888064258737158375089837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5034838023299089000239565 1888064258737158375089837)
                    ·
                      refine ⟨708024097026434390658689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1888064258737158375089837 708024097026434390658689)
                      ·
                        rfl

theorem cell23_1378872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_1378872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378872 prefixEnd_1378872 := by exact prefixLift 1378872
  have htrace : WordTrace (prefixWord ++ tailWord_1378872) baseStart_1378872 baseEnd_1378872 := by
    simpa [prefixWord, tailWord_1378872, baseEnd_1378872] using wordTrace_append hprefix tailTrace_1378872
  have hstable : (prefixWord ++ tailWord_1378872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378872).length < 2 ^ (prefixWord ++ tailWord_1378872).sum := by decide
  have hdescent : baseEnd_1378872 < baseStart_1378872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378912 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1378912 : Nat := 118140960795 + 1378912 * 2 ^ 59
def prefixEnd_1378912 : Nat := 4983230072969 + 3 ^ 40 * 1378912 * 2
def baseEnd_1378912 : Nat := 708044636252614234158505

theorem tailTrace_1378912 : CollatzResearch.WordTrace tailWord_1378912 prefixEnd_1378912 708044636252614234158505 := by
  unfold tailWord_1378912
  simp only [CollatzResearch.WordTrace]
  refine ⟨25146526190222399132821495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33528701586963198843761993 25146526190222399132821495)
  ·
    refine ⟨37719789285333598699232243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25146526190222399132821495 37719789285333598699232243)
    ·
      refine ⟨56579683928000398048848365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37719789285333598699232243 56579683928000398048848365)
      ·
        refine ⟨21217381473000149268318137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56579683928000398048848365 21217381473000149268318137)
        ·
          refine ⟨15913036104750111951238603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21217381473000149268318137 15913036104750111951238603)
          ·
            refine ⟨23869554157125167926857905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15913036104750111951238603 23869554157125167926857905)
            ·
              refine ⟨17902165617843875945143429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23869554157125167926857905 17902165617843875945143429)
              ·
                refine ⟨3356656053345726739714393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17902165617843875945143429 3356656053345726739714393)
                ·
                  refine ⟨2517492040009295054785795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356656053345726739714393 2517492040009295054785795)
                  ·
                    refine ⟨3776238060013942582178693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517492040009295054785795 3776238060013942582178693)
                    ·
                      refine ⟨708044636252614234158505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3776238060013942582178693 708044636252614234158505)
                      ·
                        rfl

theorem cell23_1378912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1378912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378912 prefixEnd_1378912 := by exact prefixLift 1378912
  have htrace : WordTrace (prefixWord ++ tailWord_1378912) baseStart_1378912 baseEnd_1378912 := by
    simpa [prefixWord, tailWord_1378912, baseEnd_1378912] using wordTrace_append hprefix tailTrace_1378912
  have hstable : (prefixWord ++ tailWord_1378912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378912).length < 2 ^ (prefixWord ++ tailWord_1378912).sum := by decide
  have hdescent : baseEnd_1378912 < baseStart_1378912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378955 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_1378955 : Nat := 118140960795 + 1378955 * 2 ^ 59
def prefixEnd_1378955 : Nat := 4983230072969 + 3 ^ 40 * 1378955 * 2
def baseEnd_1378955 : Nat := 708066715920757565920807

theorem tailTrace_1378955 : CollatzResearch.WordTrace tailWord_1378955 prefixEnd_1378955 708066715920757565920807 := by
  unfold tailWord_1378955
  simp only [CollatzResearch.WordTrace]
  refine ⟨50294620719289016609458319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33529747146192677739638879 50294620719289016609458319)
  ·
    refine ⟨75441931078933524914187479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50294620719289016609458319 75441931078933524914187479)
    ·
      refine ⟨113162896618400287371281219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75441931078933524914187479 113162896618400287371281219)
      ·
        refine ⟨169744344927600431056921829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113162896618400287371281219 169744344927600431056921829)
        ·
          refine ⟨31827064673925080823172843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169744344927600431056921829 31827064673925080823172843)
          ·
            refine ⟨47740597010887621234759265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31827064673925080823172843 47740597010887621234759265)
            ·
              refine ⟨35805447758165715926069449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47740597010887621234759265 35805447758165715926069449)
              ·
                refine ⟨26854085818624286944552087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35805447758165715926069449 26854085818624286944552087)
                ·
                  refine ⟨40281128727936430416828131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26854085818624286944552087 40281128727936430416828131)
                  ·
                    refine ⟨60421693091904645625242197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40281128727936430416828131 60421693091904645625242197)
                    ·
                      refine ⟨708066715920757565920807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 60421693091904645625242197 708066715920757565920807)
                      ·
                        rfl

theorem cell23_1378955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_1378955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378955 prefixEnd_1378955 := by exact prefixLift 1378955
  have htrace : WordTrace (prefixWord ++ tailWord_1378955) baseStart_1378955 baseEnd_1378955 := by
    simpa [prefixWord, tailWord_1378955, baseEnd_1378955] using wordTrace_append hprefix tailTrace_1378955
  have hstable : (prefixWord ++ tailWord_1378955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378955).length < 2 ^ (prefixWord ++ tailWord_1378955).sum := by decide
  have hdescent : baseEnd_1378955 < baseStart_1378955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378979 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 3]
def baseStart_1378979 : Nat := 118140960795 + 1378979 * 2 ^ 59
def prefixEnd_1378979 : Nat := 4983230072969 + 3 ^ 40 * 1378979 * 2
def baseEnd_1378979 : Nat := 708079039456465472020697

theorem tailTrace_1378979 : CollatzResearch.WordTrace tailWord_1378979 prefixEnd_1378979 708079039456465472020697 := by
  unfold tailWord_1378979
  simp only [CollatzResearch.WordTrace]
  refine ⟨50295496071202068708331991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33530330714134712472221327 50295496071202068708331991)
  ·
    refine ⟨75443244106803103062497987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50295496071202068708331991 75443244106803103062497987)
    ·
      refine ⟨113164866160204654593746981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75443244106803103062497987 113164866160204654593746981)
      ·
        refine ⟨21218412405038372736327559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113164866160204654593746981 21218412405038372736327559)
        ·
          refine ⟨31827618607557559104491339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21218412405038372736327559 31827618607557559104491339)
          ·
            refine ⟨47741427911336338656737009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31827618607557559104491339 47741427911336338656737009)
            ·
              refine ⟨35806070933502253992552757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47741427911336338656737009 35806070933502253992552757)
              ·
                refine ⟨3356819150015836311801821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35806070933502253992552757 3356819150015836311801821)
                ·
                  refine ⟨1258807181255938616925683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3356819150015836311801821 1258807181255938616925683)
                  ·
                    refine ⟨1888210771883907925388525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258807181255938616925683 1888210771883907925388525)
                    ·
                      refine ⟨708079039456465472020697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1888210771883907925388525 708079039456465472020697)
                      ·
                        rfl

theorem cell23_1378979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_1378979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378979 prefixEnd_1378979 := by exact prefixLift 1378979
  have htrace : WordTrace (prefixWord ++ tailWord_1378979) baseStart_1378979 baseEnd_1378979 := by
    simpa [prefixWord, tailWord_1378979, baseEnd_1378979] using wordTrace_append hprefix tailTrace_1378979
  have hstable : (prefixWord ++ tailWord_1378979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378979).length < 2 ^ (prefixWord ++ tailWord_1378979).sum := by decide
  have hdescent : baseEnd_1378979 < baseStart_1378979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1378999 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 3, 5]
def baseStart_1378999 : Nat := 118140960795 + 1378999 * 2 ^ 59
def prefixEnd_1378999 : Nat := 4983230072969 + 3 ^ 40 * 1378999 * 2
def baseEnd_1378999 : Nat := 236029769689851797923535

theorem tailTrace_1378999 : CollatzResearch.WordTrace tailWord_1378999 prefixEnd_1378999 236029769689851797923535 := by
  unfold tailWord_1378999
  simp only [CollatzResearch.WordTrace]
  refine ⟨50296225531129612124060051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33530817020753074749373367 50296225531129612124060051)
  ·
    refine ⟨75444338296694418186090077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50296225531129612124060051 75444338296694418186090077)
    ·
      refine ⟨28291626861260406819783779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75444338296694418186090077 28291626861260406819783779)
      ·
        refine ⟨42437440291890610229675669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28291626861260406819783779 42437440291890610229675669)
        ·
          refine ⟨1989255013682372354516047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42437440291890610229675669 1989255013682372354516047)
          ·
            refine ⟨2983882520523558531774071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989255013682372354516047 2983882520523558531774071)
            ·
              refine ⟨4475823780785337797661107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983882520523558531774071 4475823780785337797661107)
              ·
                refine ⟨6713735671178006696491661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475823780785337797661107 6713735671178006696491661)
                ·
                  refine ⟨2517650876691752511184373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6713735671178006696491661 2517650876691752511184373)
                  ·
                    refine ⟨236029769689851797923535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2517650876691752511184373 236029769689851797923535)
                    ·
                      rfl

theorem cell23_1378999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_1378999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1378999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1378999 prefixEnd_1378999 := by exact prefixLift 1378999
  have htrace : WordTrace (prefixWord ++ tailWord_1378999) baseStart_1378999 baseEnd_1378999 := by
    simpa [prefixWord, tailWord_1378999, baseEnd_1378999] using wordTrace_append hprefix tailTrace_1378999
  have hstable : (prefixWord ++ tailWord_1378999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1378999).length < 2 ^ (prefixWord ++ tailWord_1378999).sum := by decide
  have hdescent : baseEnd_1378999 < baseStart_1378999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1378999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379016 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 1, 5]
def baseStart_1379016 : Nat := 118140960795 + 1379016 * 2 ^ 59
def prefixEnd_1379016 : Nat := 4983230072969 + 3 ^ 40 * 1379016 * 2
def baseEnd_1379016 : Nat := 236032679413560609086009

theorem tailTrace_1379016 : CollatzResearch.WordTrace tailWord_1379016 prefixEnd_1379016 236032679413560609086009 := by
  unfold tailWord_1379016
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148422786034012013714451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33531230381378682684952601 25148422786034012013714451)
  ·
    refine ⟨37722634179051018020571677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25148422786034012013714451 37722634179051018020571677)
    ·
      refine ⟨14145987817144131757714379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37722634179051018020571677 14145987817144131757714379)
      ·
        refine ⟨21218981725716197636571569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14145987817144131757714379 21218981725716197636571569)
        ·
          refine ⟨15914236294287148227428677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21218981725716197636571569 15914236294287148227428677)
          ·
            refine ⟨2983919305178840292642877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15914236294287148227428677 2983919305178840292642877)
            ·
              refine ⟨1118969739442065109741079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2983919305178840292642877 1118969739442065109741079)
              ·
                refine ⟨1678454609163097664611619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118969739442065109741079 1678454609163097664611619)
                ·
                  refine ⟨2517681913744646496917429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678454609163097664611619 2517681913744646496917429)
                  ·
                    refine ⟨236032679413560609086009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2517681913744646496917429 236032679413560609086009)
                    ·
                      rfl

theorem cell23_1379016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_1379016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379016 prefixEnd_1379016 := by exact prefixLift 1379016
  have htrace : WordTrace (prefixWord ++ tailWord_1379016) baseStart_1379016 baseEnd_1379016 := by
    simpa [prefixWord, tailWord_1379016, baseEnd_1379016] using wordTrace_append hprefix tailTrace_1379016
  have hstable : (prefixWord ++ tailWord_1379016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379016).length < 2 ^ (prefixWord ++ tailWord_1379016).sum := by decide
  have hdescent : baseEnd_1379016 < baseStart_1379016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379036 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1379036 : Nat := 118140960795 + 1379036 * 2 ^ 59
def prefixEnd_1379036 : Nat := 4983230072969 + 3 ^ 40 * 1379036 * 2
def baseEnd_1379036 : Nat := 708108307853771749007935

theorem tailTrace_1379036 : CollatzResearch.WordTrace tailWord_1379036 prefixEnd_1379036 708108307853771749007935 := by
  unfold tailWord_1379036
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148787515997783721578481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33531716687997044962104641 25148787515997783721578481)
  ·
    refine ⟨18861590636998337791183861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25148787515997783721578481 18861590636998337791183861)
    ·
      refine ⟨1768274122218594167923487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18861590636998337791183861 1768274122218594167923487)
      ·
        refine ⟨2652411183327891251885231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768274122218594167923487 2652411183327891251885231)
        ·
          refine ⟨3978616774991836877827847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652411183327891251885231 3978616774991836877827847)
          ·
            refine ⟨5967925162487755316741771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978616774991836877827847 5967925162487755316741771)
            ·
              refine ⟨8951887743731632975112657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967925162487755316741771 8951887743731632975112657)
              ·
                refine ⟨6713915807798724731334493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8951887743731632975112657 6713915807798724731334493)
                ·
                  refine ⟨2517718427924521774250435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6713915807798724731334493 2517718427924521774250435)
                  ·
                    refine ⟨3776577641886782661375653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517718427924521774250435 3776577641886782661375653)
                    ·
                      refine ⟨708108307853771749007935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3776577641886782661375653 708108307853771749007935)
                      ·
                        rfl

theorem cell23_1379036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1379036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379036 prefixEnd_1379036 := by exact prefixLift 1379036
  have htrace : WordTrace (prefixWord ++ tailWord_1379036) baseStart_1379036 baseEnd_1379036 := by
    simpa [prefixWord, tailWord_1379036, baseEnd_1379036] using wordTrace_append hprefix tailTrace_1379036
  have hstable : (prefixWord ++ tailWord_1379036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379036).length < 2 ^ (prefixWord ++ tailWord_1379036).sum := by decide
  have hdescent : baseEnd_1379036 < baseStart_1379036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379039 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_1379039 : Nat := 118140960795 + 1379039 * 2 ^ 59
def prefixEnd_1379039 : Nat := 4983230072969 + 3 ^ 40 * 1379039 * 2
def baseEnd_1379039 : Nat := 708109848295735237270421

theorem tailTrace_1379039 : CollatzResearch.WordTrace tailWord_1379039 prefixEnd_1379039 708109848295735237270421 := by
  unfold tailWord_1379039
  simp only [CollatzResearch.WordTrace]
  refine ⟨50297684450984698955516171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33531789633989799303677447 50297684450984698955516171)
  ·
    refine ⟨75446526676477048433274257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50297684450984698955516171 75446526676477048433274257)
    ·
      refine ⟨56584895007357786324955693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75446526676477048433274257 56584895007357786324955693)
      ·
        refine ⟨21219335627759169871858385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56584895007357786324955693 21219335627759169871858385)
        ·
          refine ⟨15914501720819377403893789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21219335627759169871858385 15914501720819377403893789)
          ·
            refine ⟨5967938145307266526460171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15914501720819377403893789 5967938145307266526460171)
            ·
              refine ⟨8951907217960899789690257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967938145307266526460171 8951907217960899789690257)
              ·
                refine ⟨6713930413470674842267693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8951907217960899789690257 6713930413470674842267693)
                ·
                  refine ⟨2517723905051503065850385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6713930413470674842267693 2517723905051503065850385)
                  ·
                    refine ⟨1888292928788627299387789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2517723905051503065850385 1888292928788627299387789)
                    ·
                      refine ⟨708109848295735237270421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1888292928788627299387789 708109848295735237270421)
                      ·
                        rfl

theorem cell23_1379039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_1379039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379039 prefixEnd_1379039 := by exact prefixLift 1379039
  have htrace : WordTrace (prefixWord ++ tailWord_1379039) baseStart_1379039 baseEnd_1379039 := by
    simpa [prefixWord, tailWord_1379039, baseEnd_1379039] using wordTrace_append hprefix tailTrace_1379039
  have hstable : (prefixWord ++ tailWord_1379039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379039).length < 2 ^ (prefixWord ++ tailWord_1379039).sum := by decide
  have hdescent : baseEnd_1379039 < baseStart_1379039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379053 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1379053 : Nat := 118140960795 + 1379053 * 2 ^ 59
def prefixEnd_1379053 : Nat := 4983230072969 + 3 ^ 40 * 1379053 * 2
def baseEnd_1379053 : Nat := 708117037024898182495357

theorem tailTrace_1379053 : CollatzResearch.WordTrace tailWord_1379053 prefixEnd_1379053 708117037024898182495357 := by
  unfold tailWord_1379053
  simp only [CollatzResearch.WordTrace]
  refine ⟨50298195072933979346525813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33532130048622652897683875 50298195072933979346525813)
  ·
    refine ⟨4715455788087560563736795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50298195072933979346525813 4715455788087560563736795)
    ·
      refine ⟨7073183682131340845605193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4715455788087560563736795 7073183682131340845605193)
      ·
        refine ⟨5304887761598505634203895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7073183682131340845605193 5304887761598505634203895)
        ·
          refine ⟨7957331642397758451305843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304887761598505634203895 7957331642397758451305843)
          ·
            refine ⟨11935997463596637676958765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7957331642397758451305843 11935997463596637676958765)
            ·
              refine ⟨4475999048848739128859537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11935997463596637676958765 4475999048848739128859537)
              ·
                refine ⟨3356999286636554346644653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475999048848739128859537 3356999286636554346644653)
                ·
                  refine ⟨1258874732488707879991745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3356999286636554346644653 1258874732488707879991745)
                  ·
                    refine ⟨944156049366530909993809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258874732488707879991745 944156049366530909993809)
                    ·
                      refine ⟨708117037024898182495357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944156049366530909993809 708117037024898182495357)
                      ·
                        rfl

theorem cell23_1379053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1379053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379053 prefixEnd_1379053 := by exact prefixLift 1379053
  have htrace : WordTrace (prefixWord ++ tailWord_1379053) baseStart_1379053 baseEnd_1379053 := by
    simpa [prefixWord, tailWord_1379053, baseEnd_1379053] using wordTrace_append hprefix tailTrace_1379053
  have hstable : (prefixWord ++ tailWord_1379053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379053).length < 2 ^ (prefixWord ++ tailWord_1379053).sum := by decide
  have hdescent : baseEnd_1379053 < baseStart_1379053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379069 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1379069 : Nat := 118140960795 + 1379069 * 2 ^ 59
def prefixEnd_1379069 : Nat := 4983230072969 + 3 ^ 40 * 1379069 * 2
def baseEnd_1379069 : Nat := 708125252715370119895283

theorem tailTrace_1379069 : CollatzResearch.WordTrace tailWord_1379069 prefixEnd_1379069 708125252715370119895283 := by
  unfold tailWord_1379069
  simp only [CollatzResearch.WordTrace]
  refine ⟨50298778640876014079108261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33532519093917342719405507 50298778640876014079108261)
  ·
    refine ⟨9431020995164252639832799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50298778640876014079108261 9431020995164252639832799)
    ·
      refine ⟨14146531492746378959749199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9431020995164252639832799 14146531492746378959749199)
      ·
        refine ⟨21219797239119568439623799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14146531492746378959749199 21219797239119568439623799)
        ·
          refine ⟨31829695858679352659435699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21219797239119568439623799 31829695858679352659435699)
          ·
            refine ⟨47744543788019028989153549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31829695858679352659435699 47744543788019028989153549)
            ·
              refine ⟨17904203920507135870932581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47744543788019028989153549 17904203920507135870932581)
              ·
                refine ⟨3357038235095087975799859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17904203920507135870932581 3357038235095087975799859)
                ·
                  refine ⟨5035557352642631963699789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357038235095087975799859 5035557352642631963699789)
                  ·
                    refine ⟨1888334007240986986387421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5035557352642631963699789 1888334007240986986387421)
                    ·
                      refine ⟨708125252715370119895283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1888334007240986986387421 708125252715370119895283)
                      ·
                        rfl

theorem cell23_1379069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1379069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379069 prefixEnd_1379069 := by exact prefixLift 1379069
  have htrace : WordTrace (prefixWord ++ tailWord_1379069) baseStart_1379069 baseEnd_1379069 := by
    simpa [prefixWord, tailWord_1379069, baseEnd_1379069] using wordTrace_append hprefix tailTrace_1379069
  have hstable : (prefixWord ++ tailWord_1379069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379069).length < 2 ^ (prefixWord ++ tailWord_1379069).sum := by decide
  have hdescent : baseEnd_1379069 < baseStart_1379069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379070 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_1379070 : Nat := 118140960795 + 1379070 * 2 ^ 59
def prefixEnd_1379070 : Nat := 4983230072969 + 3 ^ 40 * 1379070 * 2
def baseEnd_1379070 : Nat := 708125766196024615982779

theorem tailTrace_1379070 : CollatzResearch.WordTrace tailWord_1379070 prefixEnd_1379070 708125766196024615982779 := by
  unfold tailWord_1379070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287351889234048906236833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33532543409248260833263109 6287351889234048906236833)
  ·
    refine ⟨4715513916925536679677625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6287351889234048906236833 4715513916925536679677625)
    ·
      refine ⟨3536635437694152509758219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4715513916925536679677625 3536635437694152509758219)
      ·
        refine ⟨5304953156541228764637329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536635437694152509758219 5304953156541228764637329)
        ·
          refine ⟨3978714867405921573477997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5304953156541228764637329 3978714867405921573477997)
          ·
            refine ⟨1492018075277220590054249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3978714867405921573477997 1492018075277220590054249)
            ·
              refine ⟨1119013556457915442540687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492018075277220590054249 1119013556457915442540687)
              ·
                refine ⟨1678520334686873163811031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119013556457915442540687 1678520334686873163811031)
                ·
                  refine ⟨2517780502030309745716547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678520334686873163811031 2517780502030309745716547)
                  ·
                    refine ⟨3776670753045464618574821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517780502030309745716547 3776670753045464618574821)
                    ·
                      refine ⟨708125766196024615982779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3776670753045464618574821 708125766196024615982779)
                      ·
                        rfl

theorem cell23_1379070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_1379070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379070 prefixEnd_1379070 := by exact prefixLift 1379070
  have htrace : WordTrace (prefixWord ++ tailWord_1379070) baseStart_1379070 baseEnd_1379070 := by
    simpa [prefixWord, tailWord_1379070, baseEnd_1379070] using wordTrace_append hprefix tailTrace_1379070
  have hstable : (prefixWord ++ tailWord_1379070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379070).length < 2 ^ (prefixWord ++ tailWord_1379070).sum := by decide
  have hdescent : baseEnd_1379070 < baseStart_1379070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379143 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_1379143 : Nat := 118140960795 + 1379143 * 2 ^ 59
def prefixEnd_1379143 : Nat := 4983230072969 + 3 ^ 40 * 1379143 * 2
def baseEnd_1379143 : Nat := 708163250283802830369943

theorem tailTrace_1379143 : CollatzResearch.WordTrace tailWord_1379143 prefixEnd_1379143 708163250283802830369943 := by
  unfold tailWord_1379143
  simp only [CollatzResearch.WordTrace]
  refine ⟨50301477642607924717302083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33534318428405283144868055 50301477642607924717302083)
  ·
    refine ⟨75452216463911887075953125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50301477642607924717302083 75452216463911887075953125)
    ·
      refine ⟨14147290586983478826741211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75452216463911887075953125 14147290586983478826741211)
      ·
        refine ⟨21220935880475218240111817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14147290586983478826741211 21220935880475218240111817)
        ·
          refine ⟨15915701910356413680083863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21220935880475218240111817 15915701910356413680083863)
          ·
            refine ⟨23873552865534620520125795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15915701910356413680083863 23873552865534620520125795)
            ·
              refine ⟨35810329298301930780188693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23873552865534620520125795 35810329298301930780188693)
              ·
                refine ⟨1678609185857903005321345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35810329298301930780188693 1678609185857903005321345)
                ·
                  refine ⟨1258956889393427253991009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1678609185857903005321345 1258956889393427253991009)
                  ·
                    refine ⟨944217667045070440493257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258956889393427253991009 944217667045070440493257)
                    ·
                      refine ⟨708163250283802830369943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944217667045070440493257 708163250283802830369943)
                      ·
                        rfl

theorem cell23_1379143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_1379143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379143 prefixEnd_1379143 := by exact prefixLift 1379143
  have htrace : WordTrace (prefixWord ++ tailWord_1379143) baseStart_1379143 baseEnd_1379143 := by
    simpa [prefixWord, tailWord_1379143, baseEnd_1379143] using wordTrace_append hprefix tailTrace_1379143
  have hstable : (prefixWord ++ tailWord_1379143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379143).length < 2 ^ (prefixWord ++ tailWord_1379143).sum := by decide
  have hdescent : baseEnd_1379143 < baseStart_1379143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379179 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 2, 5]
def baseStart_1379179 : Nat := 118140960795 + 1379179 * 2 ^ 59
def prefixEnd_1379179 : Nat := 4983230072969 + 3 ^ 40 * 1379179 * 2
def baseEnd_1379179 : Nat := 236060578529121563173259

theorem tailTrace_1379179 : CollatzResearch.WordTrace tailWord_1379179 prefixEnd_1379179 236060578529121563173259 := by
  unfold tailWord_1379179
  simp only [CollatzResearch.WordTrace]
  refine ⟨50302790670477502865612591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33535193780318335243741727 50302790670477502865612591)
  ·
    refine ⟨75454186005716254298418887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50302790670477502865612591 75454186005716254298418887)
    ·
      refine ⟨113181279008574381447628331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75454186005716254298418887 113181279008574381447628331)
      ·
        refine ⟨169771918512861572171442497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113181279008574381447628331 169771918512861572171442497)
        ·
          refine ⟨127328938884646179128581873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169771918512861572171442497 127328938884646179128581873)
          ·
            refine ⟨95496704163484634346436405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127328938884646179128581873 95496704163484634346436405)
            ·
              refine ⟨8952816015326684469978413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95496704163484634346436405 8952816015326684469978413)
              ·
                refine ⟨3357306005747506676241905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8952816015326684469978413 3357306005747506676241905)
                ·
                  refine ⟨2517979504310630007181429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3357306005747506676241905 2517979504310630007181429)
                  ·
                    refine ⟨236060578529121563173259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2517979504310630007181429 236060578529121563173259)
                    ·
                      rfl

theorem cell23_1379179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 5].length) (baseStart_1379179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379179 prefixEnd_1379179 := by exact prefixLift 1379179
  have htrace : WordTrace (prefixWord ++ tailWord_1379179) baseStart_1379179 baseEnd_1379179 := by
    simpa [prefixWord, tailWord_1379179, baseEnd_1379179] using wordTrace_append hprefix tailTrace_1379179
  have hstable : (prefixWord ++ tailWord_1379179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379179).length < 2 ^ (prefixWord ++ tailWord_1379179).sum := by decide
  have hdescent : baseEnd_1379179 < baseStart_1379179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379233 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1379233 : Nat := 118140960795 + 1379233 * 2 ^ 59
def prefixEnd_1379233 : Nat := 4983230072969 + 3 ^ 40 * 1379233 * 2
def baseEnd_1379233 : Nat := 708209463542707478244529

theorem tailTrace_1379233 : CollatzResearch.WordTrace tailWord_1379233 prefixEnd_1379233 708209463542707478244529 := by
  unfold tailWord_1379233
  simp only [CollatzResearch.WordTrace]
  refine ⟨50304760212281870088078353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33536506808187913392052235 50304760212281870088078353)
  ·
    refine ⟨37728570159211402566058765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50304760212281870088078353 37728570159211402566058765)
    ·
      refine ⟨14148213809704275962272037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37728570159211402566058765 14148213809704275962272037)
      ·
        refine ⟨2652790089319551742926007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14148213809704275962272037 2652790089319551742926007)
        ·
          refine ⟨3979185133979327614389011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652790089319551742926007 3979185133979327614389011)
          ·
            refine ⟨5968777700968991421583517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979185133979327614389011 5968777700968991421583517)
            ·
              refine ⟨2238291637863371783093819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5968777700968991421583517 2238291637863371783093819)
              ·
                refine ⟨3357437456795057674640729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238291637863371783093819 3357437456795057674640729)
                ·
                  refine ⟨2518078092596293255980547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3357437456795057674640729 2518078092596293255980547)
                  ·
                    refine ⟨3777117138894439883970821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2518078092596293255980547 3777117138894439883970821)
                    ·
                      refine ⟨708209463542707478244529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3777117138894439883970821 708209463542707478244529)
                      ·
                        rfl

theorem cell23_1379233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1379233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379233 prefixEnd_1379233 := by exact prefixLift 1379233
  have htrace : WordTrace (prefixWord ++ tailWord_1379233) baseStart_1379233 baseEnd_1379233 := by
    simpa [prefixWord, tailWord_1379233, baseEnd_1379233] using wordTrace_append hprefix tailTrace_1379233
  have hstable : (prefixWord ++ tailWord_1379233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379233).length < 2 ^ (prefixWord ++ tailWord_1379233).sum := by decide
  have hdescent : baseEnd_1379233 < baseStart_1379233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379236 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_1379236 : Nat := 118140960795 + 1379236 * 2 ^ 59
def prefixEnd_1379236 : Nat := 4983230072969 + 3 ^ 40 * 1379236 * 2
def baseEnd_1379236 : Nat := 708211003984670966507015

theorem tailTrace_1379236 : CollatzResearch.WordTrace tailWord_1379236 prefixEnd_1379236 708211003984670966507015 := by
  unfold tailWord_1379236
  simp only [CollatzResearch.WordTrace]
  refine ⟨25152434815635500800218781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33536579754180667733625041 25152434815635500800218781)
  ·
    refine ⟨9432163055863312800082043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25152434815635500800218781 9432163055863312800082043)
    ·
      refine ⟨14148244583794969200123065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9432163055863312800082043 14148244583794969200123065)
      ·
        refine ⟨10611183437846226900092299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14148244583794969200123065 10611183437846226900092299)
        ·
          refine ⟨15916775156769340350138449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10611183437846226900092299 15916775156769340350138449)
          ·
            refine ⟨11937581367577005262603837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15916775156769340350138449 11937581367577005262603837)
            ·
              refine ⟨4476593012841376973476439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11937581367577005262603837 4476593012841376973476439)
              ·
                refine ⟨6714889519262065460214659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476593012841376973476439 6714889519262065460214659)
                ·
                  refine ⟨10072334278893098190321989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6714889519262065460214659 10072334278893098190321989)
                  ·
                    refine ⟨1888562677292455910685373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10072334278893098190321989 1888562677292455910685373)
                    ·
                      refine ⟨708211003984670966507015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1888562677292455910685373 708211003984670966507015)
                      ·
                        rfl

theorem cell23_1379236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_1379236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379236 prefixEnd_1379236 := by exact prefixLift 1379236
  have htrace : WordTrace (prefixWord ++ tailWord_1379236) baseStart_1379236 baseEnd_1379236 := by
    simpa [prefixWord, tailWord_1379236, baseEnd_1379236] using wordTrace_append hprefix tailTrace_1379236
  have hstable : (prefixWord ++ tailWord_1379236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379236).length < 2 ^ (prefixWord ++ tailWord_1379236).sum := by decide
  have hdescent : baseEnd_1379236 < baseStart_1379236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379256 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 6]
def baseStart_1379256 : Nat := 118140960795 + 1379256 * 2 ^ 59
def prefixEnd_1379256 : Nat := 4983230072969 + 3 ^ 40 * 1379256 * 2
def baseEnd_1379256 : Nat := 78691252621973432028547

theorem tailTrace_1379256 : CollatzResearch.WordTrace tailWord_1379256 prefixEnd_1379256 78691252621973432028547 := by
  unfold tailWord_1379256
  simp only [CollatzResearch.WordTrace]
  refine ⟨25152799545599272508082811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33537066060799030010777081 25152799545599272508082811)
  ·
    refine ⟨37729199318398908762124217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25152799545599272508082811 37729199318398908762124217)
    ·
      refine ⟨28296899488799181571593163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37729199318398908762124217 28296899488799181571593163)
      ·
        refine ⟨42445349233198772357389745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28296899488799181571593163 42445349233198772357389745)
        ·
          refine ⟨31834011924899079268042309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42445349233198772357389745 31834011924899079268042309)
          ·
            refine ⟨5968877235918577362757933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31834011924899079268042309 5968877235918577362757933)
            ·
              refine ⟨2238328963469466511034225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5968877235918577362757933 2238328963469466511034225)
              ·
                refine ⟨1678746722602099883275669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238328963469466511034225 1678746722602099883275669)
                ·
                  refine ⟨78691252621973432028547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1678746722602099883275669 78691252621973432028547)
                  ·
                    rfl

theorem cell23_1379256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 6].length) (baseStart_1379256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379256 prefixEnd_1379256 := by exact prefixLift 1379256
  have htrace : WordTrace (prefixWord ++ tailWord_1379256) baseStart_1379256 baseEnd_1379256 := by
    simpa [prefixWord, tailWord_1379256, baseEnd_1379256] using wordTrace_append hprefix tailTrace_1379256
  have hstable : (prefixWord ++ tailWord_1379256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379256).length < 2 ^ (prefixWord ++ tailWord_1379256).sum := by decide
  have hdescent : baseEnd_1379256 < baseStart_1379256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379300 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_1379300 : Nat := 118140960795 + 1379300 * 2 ^ 59
def prefixEnd_1379300 : Nat := 4983230072969 + 3 ^ 40 * 1379300 * 2
def baseEnd_1379300 : Nat := 708243866746558716106721

theorem tailTrace_1379300 : CollatzResearch.WordTrace tailWord_1379300 prefixEnd_1379300 708243866746558716106721 := by
  unfold tailWord_1379300
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153601951519570265383677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33538135935359427020511569 25153601951519570265383677)
  ·
    refine ⟨9432600731819838849518879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25153601951519570265383677 9432600731819838849518879)
    ·
      refine ⟨14148901097729758274278319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9432600731819838849518879 14148901097729758274278319)
      ·
        refine ⟨21223351646594637411417479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14148901097729758274278319 21223351646594637411417479)
        ·
          refine ⟨31835027469891956117126219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21223351646594637411417479 31835027469891956117126219)
          ·
            refine ⟨47752541204837934175689329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31835027469891956117126219 47752541204837934175689329)
            ·
              refine ⟨35814405903628450631766997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47752541204837934175689329 35814405903628450631766997)
              ·
                refine ⟨839400138366291811682039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35814405903628450631766997 839400138366291811682039)
                ·
                  refine ⟨1259100207549437717523059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839400138366291811682039 1259100207549437717523059)
                  ·
                    refine ⟨1888650311324156576284589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1259100207549437717523059 1888650311324156576284589)
                    ·
                      refine ⟨708243866746558716106721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1888650311324156576284589 708243866746558716106721)
                      ·
                        rfl

theorem cell23_1379300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_1379300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379300 prefixEnd_1379300 := by exact prefixLift 1379300
  have htrace : WordTrace (prefixWord ++ tailWord_1379300) baseStart_1379300 baseEnd_1379300 := by
    simpa [prefixWord, tailWord_1379300, baseEnd_1379300] using wordTrace_append hprefix tailTrace_1379300
  have hstable : (prefixWord ++ tailWord_1379300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379300).length < 2 ^ (prefixWord ++ tailWord_1379300).sum := by decide
  have hdescent : baseEnd_1379300 < baseStart_1379300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379303 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1379303 : Nat := 118140960795 + 1379303 * 2 ^ 59
def prefixEnd_1379303 : Nat := 4983230072969 + 3 ^ 40 * 1379303 * 2
def baseEnd_1379303 : Nat := 236081802396174068123069

theorem tailTrace_1379303 : CollatzResearch.WordTrace tailWord_1379303 prefixEnd_1379303 236081802396174068123069 := by
  unfold tailWord_1379303
  simp only [CollatzResearch.WordTrace]
  refine ⟨50307313322028272043126563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33538208881352181362084375 50307313322028272043126563)
  ·
    refine ⟨75460969983042408064689845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50307313322028272043126563 75460969983042408064689845)
    ·
      refine ⟨7074465935910225756064673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75460969983042408064689845 7074465935910225756064673)
      ·
        refine ⟨5305849451932669317048505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7074465935910225756064673 5305849451932669317048505)
        ·
          refine ⟨3979387088949501987786379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5305849451932669317048505 3979387088949501987786379)
          ·
            refine ⟨5969080633424252981679569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979387088949501987786379 5969080633424252981679569)
            ·
              refine ⟨4476810475068189736259677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5969080633424252981679569 4476810475068189736259677)
              ·
                refine ⟨1678803928150571151097379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4476810475068189736259677 1678803928150571151097379)
                ·
                  refine ⟨2518205892225856726646069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678803928150571151097379 2518205892225856726646069)
                  ·
                    refine ⟨236081802396174068123069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2518205892225856726646069 236081802396174068123069)
                    ·
                      rfl

theorem cell23_1379303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1379303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379303 prefixEnd_1379303 := by exact prefixLift 1379303
  have htrace : WordTrace (prefixWord ++ tailWord_1379303) baseStart_1379303 baseEnd_1379303 := by
    simpa [prefixWord, tailWord_1379303, baseEnd_1379303] using wordTrace_append hprefix tailTrace_1379303
  have hstable : (prefixWord ++ tailWord_1379303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379303).length < 2 ^ (prefixWord ++ tailWord_1379303).sum := by decide
  have hdescent : baseEnd_1379303 < baseStart_1379303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379333 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_1379333 : Nat := 118140960795 + 1379333 * 2 ^ 59
def prefixEnd_1379333 : Nat := 4983230072969 + 3 ^ 40 * 1379333 * 2
def baseEnd_1379333 : Nat := 236086937202719028998023

theorem tailTrace_1379333 : CollatzResearch.WordTrace tailWord_1379333 prefixEnd_1379333 236086937202719028998023 := by
  unfold tailWord_1379333
  simp only [CollatzResearch.WordTrace]
  refine ⟨50308407511919587166718653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33538938341279724777812435 50308407511919587166718653)
  ·
    refine ⟨18865652816969845187519495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50308407511919587166718653 18865652816969845187519495)
    ·
      refine ⟨28298479225454767781279243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18865652816969845187519495 28298479225454767781279243)
      ·
        refine ⟨42447718838182151671918865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28298479225454767781279243 42447718838182151671918865)
        ·
          refine ⟨31835789128636613753939149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42447718838182151671918865 31835789128636613753939149)
          ·
            refine ⟨11938420923238730157727181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31835789128636613753939149 11938420923238730157727181)
            ·
              refine ⟨4476907846214523809147693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11938420923238730157727181 4476907846214523809147693)
              ·
                refine ⟨1678840442330446428430385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4476907846214523809147693 1678840442330446428430385)
                ·
                  refine ⟨1259130331747834821322789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1678840442330446428430385 1259130331747834821322789)
                  ·
                    refine ⟨236086937202719028998023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259130331747834821322789 236086937202719028998023)
                    ·
                      rfl

theorem cell23_1379333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_1379333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379333 prefixEnd_1379333 := by exact prefixLift 1379333
  have htrace : WordTrace (prefixWord ++ tailWord_1379333) baseStart_1379333 baseEnd_1379333 := by
    simpa [prefixWord, tailWord_1379333, baseEnd_1379333] using wordTrace_append hprefix tailTrace_1379333
  have hstable : (prefixWord ++ tailWord_1379333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379333).length < 2 ^ (prefixWord ++ tailWord_1379333).sum := by decide
  have hdescent : baseEnd_1379333 < baseStart_1379333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379336 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1379336 : Nat := 118140960795 + 1379336 * 2 ^ 59
def prefixEnd_1379336 : Nat := 4983230072969 + 3 ^ 40 * 1379336 * 2
def baseEnd_1379336 : Nat := 708262352050120575256555

theorem tailTrace_1379336 : CollatzResearch.WordTrace tailWord_1379336 prefixEnd_1379336 708262352050120575256555 := by
  unfold tailWord_1379336
  simp only [CollatzResearch.WordTrace]
  refine ⟨25154258465454359339538931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33539011287272479119385241 25154258465454359339538931)
  ·
    refine ⟨37731387698181539009308397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25154258465454359339538931 37731387698181539009308397)
    ·
      refine ⟨14149270386818077128490649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37731387698181539009308397 14149270386818077128490649)
      ·
        refine ⟨10611952790113557846367987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14149270386818077128490649 10611952790113557846367987)
        ·
          refine ⟨15917929185170336769551981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10611952790113557846367987 15917929185170336769551981)
          ·
            refine ⟨5969223444438876288581993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15917929185170336769551981 5969223444438876288581993)
            ·
              refine ⟨4476917583329157216436495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5969223444438876288581993 4476917583329157216436495)
              ·
                refine ⟨6715376374993735824654743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476917583329157216436495 6715376374993735824654743)
                ·
                  refine ⟨10073064562490603736982115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715376374993735824654743 10073064562490603736982115)
                  ·
                    refine ⟨15109596843735905605473173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10073064562490603736982115 15109596843735905605473173)
                    ·
                      refine ⟨708262352050120575256555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15109596843735905605473173 708262352050120575256555)
                      ·
                        rfl

theorem cell23_1379336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1379336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379336 prefixEnd_1379336 := by exact prefixLift 1379336
  have htrace : WordTrace (prefixWord ++ tailWord_1379336) baseStart_1379336 baseEnd_1379336 := by
    simpa [prefixWord, tailWord_1379336, baseEnd_1379336] using wordTrace_append hprefix tailTrace_1379336
  have hstable : (prefixWord ++ tailWord_1379336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379336).length < 2 ^ (prefixWord ++ tailWord_1379336).sum := by decide
  have hdescent : baseEnd_1379336 < baseStart_1379336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379340 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1379340 : Nat := 118140960795 + 1379340 * 2 ^ 59
def prefixEnd_1379340 : Nat := 4983230072969 + 3 ^ 40 * 1379340 * 2
def baseEnd_1379340 : Nat := 708264405972738559606537

theorem tailTrace_1379340 : CollatzResearch.WordTrace tailWord_1379340 prefixEnd_1379340 708264405972738559606537 := by
  unfold tailWord_1379340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25154331411447113681111737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33539108548596151574815649 25154331411447113681111737)
  ·
    refine ⟨18865748558585335260833803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25154331411447113681111737 18865748558585335260833803)
    ·
      refine ⟨28298622837878002891250705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18865748558585335260833803 28298622837878002891250705)
      ·
        refine ⟨21223967128408502168438029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28298622837878002891250705 21223967128408502168438029)
        ·
          refine ⟨7958987673153188313164261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21223967128408502168438029 7958987673153188313164261)
          ·
            refine ⟨1492310188716222808718299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7958987673153188313164261 1492310188716222808718299)
            ·
              refine ⟨2238465283074334213077449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492310188716222808718299 2238465283074334213077449)
              ·
                refine ⟨1678848962305750659808087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238465283074334213077449 1678848962305750659808087)
                ·
                  refine ⟨2518273443458625989712131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678848962305750659808087 2518273443458625989712131)
                  ·
                    refine ⟨3777410165187938984568197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2518273443458625989712131 3777410165187938984568197)
                    ·
                      refine ⟨708264405972738559606537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3777410165187938984568197 708264405972738559606537)
                      ·
                        rfl

theorem cell23_1379340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1379340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379340 prefixEnd_1379340 := by exact prefixLift 1379340
  have htrace : WordTrace (prefixWord ++ tailWord_1379340) baseStart_1379340 baseEnd_1379340 := by
    simpa [prefixWord, tailWord_1379340, baseEnd_1379340] using wordTrace_append hprefix tailTrace_1379340
  have hstable : (prefixWord ++ tailWord_1379340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379340).length < 2 ^ (prefixWord ++ tailWord_1379340).sum := by decide
  have hdescent : baseEnd_1379340 < baseStart_1379340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379357 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_1379357 : Nat := 118140960795 + 1379357 * 2 ^ 59
def prefixEnd_1379357 : Nat := 4983230072969 + 3 ^ 40 * 1379357 * 2
def baseEnd_1379357 : Nat := 708273135143864993093959

theorem tailTrace_1379357 : CollatzResearch.WordTrace tailWord_1379357 prefixEnd_1379357 708273135143864993093959 := by
  unfold tailWord_1379357
  simp only [CollatzResearch.WordTrace]
  refine ⟨50309282863832639265592325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33539521909221759510394883 50309282863832639265592325)
  ·
    refine ⟨9432990536968619862298561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50309282863832639265592325 9432990536968619862298561)
    ·
      refine ⟨7074742902726464896723921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9432990536968619862298561 7074742902726464896723921)
      ·
        refine ⟨5306057177044848672542941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7074742902726464896723921 5306057177044848672542941)
        ·
          refine ⟨1989771441391818252203603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5306057177044848672542941 1989771441391818252203603)
          ·
            refine ⟨2984657162087727378305405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989771441391818252203603 2984657162087727378305405)
            ·
              refine ⟨1119246435782897766864527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2984657162087727378305405 1119246435782897766864527)
              ·
                refine ⟨1678869653674346650296791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119246435782897766864527 1678869653674346650296791)
                ·
                  refine ⟨2518304480511519975445187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678869653674346650296791 2518304480511519975445187)
                  ·
                    refine ⟨3777456720767279963167781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2518304480511519975445187 3777456720767279963167781)
                    ·
                      refine ⟨708273135143864993093959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3777456720767279963167781 708273135143864993093959)
                      ·
                        rfl

theorem cell23_1379357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_1379357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379357 prefixEnd_1379357 := by exact prefixLift 1379357
  have htrace : WordTrace (prefixWord ++ tailWord_1379357) baseStart_1379357 baseEnd_1379357 := by
    simpa [prefixWord, tailWord_1379357, baseEnd_1379357] using wordTrace_append hprefix tailTrace_1379357
  have hstable : (prefixWord ++ tailWord_1379357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379357).length < 2 ^ (prefixWord ++ tailWord_1379357).sum := by decide
  have hdescent : baseEnd_1379357 < baseStart_1379357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379367 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1379367 : Nat := 118140960795 + 1379367 * 2 ^ 59
def prefixEnd_1379367 : Nat := 4983230072969 + 3 ^ 40 * 1379367 * 2
def baseEnd_1379367 : Nat := 236092756650136651322971

theorem tailTrace_1379367 : CollatzResearch.WordTrace tailWord_1379367 prefixEnd_1379367 236092756650136651322971 := by
  unfold tailWord_1379367
  simp only [CollatzResearch.WordTrace]
  refine ⟨50309647593796410973456355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33539765062530940648970903 50309647593796410973456355)
  ·
    refine ⟨75464471390694616460184533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50309647593796410973456355 75464471390694616460184533)
    ·
      refine ⟨1768698548219405073285575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75464471390694616460184533 1768698548219405073285575)
      ·
        refine ⟨2653047822329107609928363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768698548219405073285575 2653047822329107609928363)
        ·
          refine ⟨3979571733493661414892545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653047822329107609928363 3979571733493661414892545)
          ·
            refine ⟨2984678800120246061169409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3979571733493661414892545 2984678800120246061169409)
            ·
              refine ⟨2238509100090184545877057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984678800120246061169409 2238509100090184545877057)
              ·
                refine ⟨1678881825067638409407793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238509100090184545877057 1678881825067638409407793)
                ·
                  refine ⟨1259161368800728807055845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1678881825067638409407793 1259161368800728807055845)
                  ·
                    refine ⟨236092756650136651322971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259161368800728807055845 236092756650136651322971)
                    ·
                      rfl

theorem cell23_1379367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1379367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379367 prefixEnd_1379367 := by exact prefixLift 1379367
  have htrace : WordTrace (prefixWord ++ tailWord_1379367) baseStart_1379367 baseEnd_1379367 := by
    simpa [prefixWord, tailWord_1379367, baseEnd_1379367] using wordTrace_append hprefix tailTrace_1379367
  have hstable : (prefixWord ++ tailWord_1379367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379367).length < 2 ^ (prefixWord ++ tailWord_1379367).sum := by decide
  have hdescent : baseEnd_1379367 < baseStart_1379367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379374 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_1379374 : Nat := 118140960795 + 1379374 * 2 ^ 59
def prefixEnd_1379374 : Nat := 4983230072969 + 3 ^ 40 * 1379374 * 2
def baseEnd_1379374 : Nat := 708281864314991426581381

theorem tailTrace_1379374 : CollatzResearch.WordTrace tailWord_1379374 prefixEnd_1379374 708281864314991426581381 := by
  unfold tailWord_1379374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288737863096381396120147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33539935269847367445974117 6288737863096381396120147)
  ·
    refine ⟨9433106794644572094180221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6288737863096381396120147 9433106794644572094180221)
    ·
      refine ⟨3537415047991714535317583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9433106794644572094180221 3537415047991714535317583)
      ·
        refine ⟨5306122571987571802976375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537415047991714535317583 5306122571987571802976375)
        ·
          refine ⟨7959183857981357704464563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306122571987571802976375 7959183857981357704464563)
          ·
            refine ⟨11938775786972036556696845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959183857981357704464563 11938775786972036556696845)
            ·
              refine ⟨4477040920114513708761317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11938775786972036556696845 4477040920114513708761317)
              ·
                refine ⟨839445172521471320392747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4477040920114513708761317 839445172521471320392747)
                ·
                  refine ⟨1259167758782206980589121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839445172521471320392747 1259167758782206980589121)
                  ·
                    refine ⟨944375819086655235441841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1259167758782206980589121 944375819086655235441841)
                    ·
                      refine ⟨708281864314991426581381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944375819086655235441841 708281864314991426581381)
                      ·
                        rfl

theorem cell23_1379374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_1379374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379374 prefixEnd_1379374 := by exact prefixLift 1379374
  have htrace : WordTrace (prefixWord ++ tailWord_1379374) baseStart_1379374 baseEnd_1379374 := by
    simpa [prefixWord, tailWord_1379374, baseEnd_1379374] using wordTrace_append hprefix tailTrace_1379374
  have hstable : (prefixWord ++ tailWord_1379374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379374).length < 2 ^ (prefixWord ++ tailWord_1379374).sum := by decide
  have hdescent : baseEnd_1379374 < baseStart_1379374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379380 : List Nat := [2, 5, 1, 2, 1, 3, 1, 8]
def baseStart_1379380 : Nat := 118140960795 + 1379380 * 2 ^ 59
def prefixEnd_1379380 : Nat := 4983230072969 + 3 ^ 40 * 1379380 * 2
def baseEnd_1379380 : Nat := 26232775748108089003939

theorem tailTrace_1379380 : CollatzResearch.WordTrace tailWord_1379380 prefixEnd_1379380 26232775748108089003939 := by
  unfold tailWord_1379380
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155060871374657096839797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33540081161832876129119729 25155060871374657096839797)
  ·
    refine ⟨2358286956691374102828731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25155060871374657096839797 2358286956691374102828731)
    ·
      refine ⟨3537430435037061154243097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358286956691374102828731 3537430435037061154243097)
      ·
        refine ⟨2653072826277795865682323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3537430435037061154243097 2653072826277795865682323)
        ·
          refine ⟨3979609239416693798523485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653072826277795865682323 3979609239416693798523485)
          ·
            refine ⟨1492353464781260174446307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3979609239416693798523485 1492353464781260174446307)
            ·
              refine ⟨2238530197171890261669461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492353464781260174446307 2238530197171890261669461)
              ·
                refine ⟨26232775748108089003939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2238530197171890261669461 26232775748108089003939)
                ·
                  rfl

theorem cell23_1379380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 8].length) (baseStart_1379380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379380 prefixEnd_1379380 := by exact prefixLift 1379380
  have htrace : WordTrace (prefixWord ++ tailWord_1379380) baseStart_1379380 baseEnd_1379380 := by
    simpa [prefixWord, tailWord_1379380, baseEnd_1379380] using wordTrace_append hprefix tailTrace_1379380
  have hstable : (prefixWord ++ tailWord_1379380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379380).length < 2 ^ (prefixWord ++ tailWord_1379380).sum := by decide
  have hdescent : baseEnd_1379380 < baseStart_1379380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379390 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1379390 : Nat := 118140960795 + 1379390 * 2 ^ 59
def prefixEnd_1379390 : Nat := 4983230072969 + 3 ^ 40 * 1379390 * 2
def baseEnd_1379390 : Nat := 708290080005463363981307

theorem tailTrace_1379390 : CollatzResearch.WordTrace tailWord_1379390 prefixEnd_1379390 708290080005463363981307 := by
  unfold tailWord_1379390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288810809089135737692953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33540324315142057267695749 6288810809089135737692953)
  ·
    refine ⟨4716608106816851803269715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6288810809089135737692953 4716608106816851803269715)
    ·
      refine ⟨7074912160225277704904573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4716608106816851803269715 7074912160225277704904573)
      ·
        refine ⟨2653092060084479139339215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7074912160225277704904573 2653092060084479139339215)
        ·
          refine ⟨3979638090126718709008823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653092060084479139339215 3979638090126718709008823)
          ·
            refine ⟨5969457135190078063513235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979638090126718709008823 5969457135190078063513235)
            ·
              refine ⟨8954185702785117095269853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5969457135190078063513235 8954185702785117095269853)
              ·
                refine ⟨3357819638544418910726195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8954185702785117095269853 3357819638544418910726195)
                ·
                  refine ⟨5036729457816628366089293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357819638544418910726195 5036729457816628366089293)
                  ·
                    refine ⟨1888773546681235637283485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5036729457816628366089293 1888773546681235637283485)
                    ·
                      refine ⟨708290080005463363981307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1888773546681235637283485 708290080005463363981307)
                      ·
                        rfl

theorem cell23_1379390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1379390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379390 prefixEnd_1379390 := by exact prefixLift 1379390
  have htrace : WordTrace (prefixWord ++ tailWord_1379390) baseStart_1379390 baseEnd_1379390 := by
    simpa [prefixWord, tailWord_1379390, baseEnd_1379390] using wordTrace_append hprefix tailTrace_1379390
  have hstable : (prefixWord ++ tailWord_1379390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379390).length < 2 ^ (prefixWord ++ tailWord_1379390).sum := by decide
  have hdescent : baseEnd_1379390 < baseStart_1379390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379400 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_1379400 : Nat := 118140960795 + 1379400 * 2 ^ 59
def prefixEnd_1379400 : Nat := 4983230072969 + 3 ^ 40 * 1379400 * 2
def baseEnd_1379400 : Nat := 708295214812008324856261

theorem tailTrace_1379400 : CollatzResearch.WordTrace tailWord_1379400 prefixEnd_1379400 708295214812008324856261 := by
  unfold tailWord_1379400
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155425601338428804703827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33540567468451238406271769 25155425601338428804703827)
  ·
    refine ⟨37733138402007643207055741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25155425601338428804703827 37733138402007643207055741)
    ·
      refine ⟨14149926900752866202645903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37733138402007643207055741 14149926900752866202645903)
      ·
        refine ⟨21224890351129299303968855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14149926900752866202645903 21224890351129299303968855)
        ·
          refine ⟨31837335526693948955953283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21224890351129299303968855 31837335526693948955953283)
          ·
            refine ⟨47756003290040923433929925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31837335526693948955953283 47756003290040923433929925)
            ·
              refine ⟨8954250616882673143861861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47756003290040923433929925 8954250616882673143861861)
              ·
                refine ⟨1678921990665501214474099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8954250616882673143861861 1678921990665501214474099)
                ·
                  refine ⟨2518382985998251821711149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678921990665501214474099 2518382985998251821711149)
                  ·
                    refine ⟨944393619749344433141681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518382985998251821711149 944393619749344433141681)
                    ·
                      refine ⟨708295214812008324856261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944393619749344433141681 708295214812008324856261)
                      ·
                        rfl

theorem cell23_1379400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_1379400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379400 prefixEnd_1379400 := by exact prefixLift 1379400
  have htrace : WordTrace (prefixWord ++ tailWord_1379400) baseStart_1379400 baseEnd_1379400 := by
    simpa [prefixWord, tailWord_1379400, baseEnd_1379400] using wordTrace_append hprefix tailTrace_1379400
  have hstable : (prefixWord ++ tailWord_1379400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379400).length < 2 ^ (prefixWord ++ tailWord_1379400).sum := by decide
  have hdescent : baseEnd_1379400 < baseStart_1379400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379406 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_1379406 : Nat := 118140960795 + 1379406 * 2 ^ 59
def prefixEnd_1379406 : Nat := 4983230072969 + 3 ^ 40 * 1379406 * 2
def baseEnd_1379406 : Nat := 236099431898645100460411

theorem tailTrace_1379406 : CollatzResearch.WordTrace tailWord_1379406 prefixEnd_1379406 236099431898645100460411 := by
  unfold tailWord_1379406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288883755081890079265759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33540713360436747089417381 6288883755081890079265759)
  ·
    refine ⟨9433325632622835118898639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6288883755081890079265759 9433325632622835118898639)
    ·
      refine ⟨14149988448934252678347959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9433325632622835118898639 14149988448934252678347959)
      ·
        refine ⟨21224982673401379017521939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14149988448934252678347959 21224982673401379017521939)
        ·
          refine ⟨31837474010102068526282909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21224982673401379017521939 31837474010102068526282909)
          ·
            refine ⟨11939052753788275697356091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31837474010102068526282909 11939052753788275697356091)
            ·
              refine ⟨17908579130682413546034137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11939052753788275697356091 17908579130682413546034137)
              ·
                refine ⟨13431434348011810159525603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17908579130682413546034137 13431434348011810159525603)
                ·
                  refine ⟨20147151522017715239288405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13431434348011810159525603 20147151522017715239288405)
                  ·
                    refine ⟨236099431898645100460411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20147151522017715239288405 236099431898645100460411)
                    ·
                      rfl

theorem cell23_1379406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_1379406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379406 prefixEnd_1379406 := by exact prefixLift 1379406
  have htrace : WordTrace (prefixWord ++ tailWord_1379406) baseStart_1379406 baseEnd_1379406 := by
    simpa [prefixWord, tailWord_1379406, baseEnd_1379406] using wordTrace_append hprefix tailTrace_1379406
  have hstable : (prefixWord ++ tailWord_1379406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379406).length < 2 ^ (prefixWord ++ tailWord_1379406).sum := by decide
  have hdescent : baseEnd_1379406 < baseStart_1379406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379416 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1379416 : Nat := 118140960795 + 1379416 * 2 ^ 59
def prefixEnd_1379416 : Nat := 4983230072969 + 3 ^ 40 * 1379416 * 2
def baseEnd_1379416 : Nat := 708303430502480262256187

theorem tailTrace_1379416 : CollatzResearch.WordTrace tailWord_1379416 prefixEnd_1379416 708303430502480262256187 := by
  unfold tailWord_1379416
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155717385309446170995051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33540956513745928227993401 25155717385309446170995051)
  ·
    refine ⟨37733576077964169256492577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25155717385309446170995051 37733576077964169256492577)
    ·
      refine ⟨28300182058473126942369433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37733576077964169256492577 28300182058473126942369433)
      ·
        refine ⟨21225136543854845206777075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28300182058473126942369433 21225136543854845206777075)
        ·
          refine ⟨31837704815782267810165613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21225136543854845206777075 31837704815782267810165613)
          ·
            refine ⟨11939139305918350428812105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31837704815782267810165613 11939139305918350428812105)
            ·
              refine ⟨8954354479438762821609079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11939139305918350428812105 8954354479438762821609079)
              ·
                refine ⟨13431531719158144232413619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8954354479438762821609079 13431531719158144232413619)
                ·
                  refine ⟨20147297578737216348620429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13431531719158144232413619 20147297578737216348620429)
                  ·
                    refine ⟨7555236592026456130732661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20147297578737216348620429 7555236592026456130732661)
                    ·
                      refine ⟨708303430502480262256187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7555236592026456130732661 708303430502480262256187)
                      ·
                        rfl

theorem cell23_1379416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1379416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379416 prefixEnd_1379416 := by exact prefixLift 1379416
  have htrace : WordTrace (prefixWord ++ tailWord_1379416) baseStart_1379416 baseEnd_1379416 := by
    simpa [prefixWord, tailWord_1379416, baseEnd_1379416] using wordTrace_append hprefix tailTrace_1379416
  have hstable : (prefixWord ++ tailWord_1379416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379416).length < 2 ^ (prefixWord ++ tailWord_1379416).sum := by decide
  have hdescent : baseEnd_1379416 < baseStart_1379416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379487 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 7]
def baseStart_1379487 : Nat := 118140960795 + 1379487 * 2 ^ 59
def prefixEnd_1379487 : Nat := 4983230072969 + 3 ^ 40 * 1379487 * 2
def baseEnd_1379487 : Nat := 78704431958772164940929

theorem tailTrace_1379487 : CollatzResearch.WordTrace tailWord_1379487 prefixEnd_1379487 78704431958772164940929 := by
  unfold tailWord_1379487
  simp only [CollatzResearch.WordTrace]
  refine ⟨50314024353361671467824715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33542682902241114311883143 50314024353361671467824715)
  ·
    refine ⟨75471036530042507201737073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50314024353361671467824715 75471036530042507201737073)
    ·
      refine ⟨56603277397531880401302805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75471036530042507201737073 56603277397531880401302805)
      ·
        refine ⟨2653278628009306893811069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56603277397531880401302805 2653278628009306893811069)
        ·
          refine ⟨994979485503490085179151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2653278628009306893811069 994979485503490085179151)
          ·
            refine ⟨1492469228255235127768727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994979485503490085179151 1492469228255235127768727)
            ·
              refine ⟨2238703842382852691653091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492469228255235127768727 2238703842382852691653091)
              ·
                refine ⟨3358055763574279037479637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238703842382852691653091 3358055763574279037479637)
                ·
                  refine ⟨78704431958772164940929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3358055763574279037479637 78704431958772164940929)
                  ·
                    rfl

theorem cell23_1379487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 7].length) (baseStart_1379487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379487 prefixEnd_1379487 := by exact prefixLift 1379487
  have htrace : WordTrace (prefixWord ++ tailWord_1379487) baseStart_1379487 baseEnd_1379487 := by
    simpa [prefixWord, tailWord_1379487, baseEnd_1379487] using wordTrace_append hprefix tailTrace_1379487
  have hstable : (prefixWord ++ tailWord_1379487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379487).length < 2 ^ (prefixWord ++ tailWord_1379487).sum := by decide
  have hdescent : baseEnd_1379487 < baseStart_1379487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379493 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_1379493 : Nat := 118140960795 + 1379493 * 2 ^ 59
def prefixEnd_1379493 : Nat := 4983230072969 + 3 ^ 40 * 1379493 * 2
def baseEnd_1379493 : Nat := 708342968512876460993333

theorem tailTrace_1379493 : CollatzResearch.WordTrace tailWord_1379493 prefixEnd_1379493 708342968512876460993333 := by
  unfold tailWord_1379493
  simp only [CollatzResearch.WordTrace]
  refine ⟨50314243191339934492543133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33542828794226622995028755 50314243191339934492543133)
  ·
    refine ⟨18867841196752475434703675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50314243191339934492543133 18867841196752475434703675)
    ·
      refine ⟨28301761795128713152055513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18867841196752475434703675 28301761795128713152055513)
      ·
        refine ⟨21226321346346534864041635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28301761795128713152055513 21226321346346534864041635)
        ·
          refine ⟨31839482019519802296062453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21226321346346534864041635 31839482019519802296062453)
          ·
            refine ⟨2984951439329981465255855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31839482019519802296062453 2984951439329981465255855)
            ·
              refine ⟨4477427158994972197883783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984951439329981465255855 4477427158994972197883783)
              ·
                refine ⟨6716140738492458296825675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477427158994972197883783 6716140738492458296825675)
                ·
                  refine ⟨10074211107738687445238513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716140738492458296825675 10074211107738687445238513)
                  ·
                    refine ⟨7555658330804015583928885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10074211107738687445238513 7555658330804015583928885)
                    ·
                      refine ⟨708342968512876460993333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7555658330804015583928885 708342968512876460993333)
                      ·
                        rfl

theorem cell23_1379493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_1379493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379493 prefixEnd_1379493 := by exact prefixLift 1379493
  have htrace : WordTrace (prefixWord ++ tailWord_1379493) baseStart_1379493 baseEnd_1379493 := by
    simpa [prefixWord, tailWord_1379493, baseEnd_1379493] using wordTrace_append hprefix tailTrace_1379493
  have hstable : (prefixWord ++ tailWord_1379493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379493).length < 2 ^ (prefixWord ++ tailWord_1379493).sum := by decide
  have hdescent : baseEnd_1379493 < baseStart_1379493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379498 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1379498 : Nat := 118140960795 + 1379498 * 2 ^ 59
def prefixEnd_1379498 : Nat := 4983230072969 + 3 ^ 40 * 1379498 * 2
def baseEnd_1379498 : Nat := 708345535916148941430811

theorem tailTrace_1379498 : CollatzResearch.WordTrace tailWord_1379498 prefixEnd_1379498 708345535916148941430811 := by
  unfold tailWord_1379498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12578606389080455086618787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33542950370881213564316765 12578606389080455086618787)
  ·
    refine ⟨18867909583620682629928181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12578606389080455086618787 18867909583620682629928181)
    ·
      refine ⟨1768866523464438996555767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18867909583620682629928181 1768866523464438996555767)
      ·
        refine ⟨2653299785196658494833651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768866523464438996555767 2653299785196658494833651)
        ·
          refine ⟨3979949677794987742250477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653299785196658494833651 3979949677794987742250477)
          ·
            refine ⟨1492481129173120403343929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3979949677794987742250477 1492481129173120403343929)
            ·
              refine ⟨1119360846879840302507947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1492481129173120403343929 1119360846879840302507947)
              ·
                refine ⟨1679041270319760453761921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119360846879840302507947 1679041270319760453761921)
                ·
                  refine ⟨1259280952739820340321441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1679041270319760453761921 1259280952739820340321441)
                  ·
                    refine ⟨944460714554865255241081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1259280952739820340321441 944460714554865255241081)
                    ·
                      refine ⟨708345535916148941430811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944460714554865255241081 708345535916148941430811)
                      ·
                        rfl

theorem cell23_1379498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1379498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379498 prefixEnd_1379498 := by exact prefixLift 1379498
  have htrace : WordTrace (prefixWord ++ tailWord_1379498) baseStart_1379498 baseEnd_1379498 := by
    simpa [prefixWord, tailWord_1379498, baseEnd_1379498] using wordTrace_append hprefix tailTrace_1379498
  have hstable : (prefixWord ++ tailWord_1379498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379498).length < 2 ^ (prefixWord ++ tailWord_1379498).sum := by decide
  have hdescent : baseEnd_1379498 < baseStart_1379498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379543 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 6]
def baseStart_1379543 : Nat := 118140960795 + 1379543 * 2 ^ 59
def prefixEnd_1379543 : Nat := 4983230072969 + 3 ^ 40 * 1379543 * 2
def baseEnd_1379543 : Nat := 78707626949511251707567

theorem tailTrace_1379543 : CollatzResearch.WordTrace tailWord_1379543 prefixEnd_1379543 78707626949511251707567 := by
  unfold tailWord_1379543
  simp only [CollatzResearch.WordTrace]
  refine ⟨50316066841158793031863283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33544044560772528687908855 50316066841158793031863283)
  ·
    refine ⟨75474100261738189547794925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50316066841158793031863283 75474100261738189547794925)
    ·
      refine ⟨28302787598151821080423097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75474100261738189547794925 28302787598151821080423097)
      ·
        refine ⟨21227090698613865810317323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28302787598151821080423097 21227090698613865810317323)
        ·
          refine ⟨31840636047920798715475985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21227090698613865810317323 31840636047920798715475985)
          ·
            refine ⟨23880477035940599036606989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31840636047920798715475985 23880477035940599036606989)
            ·
              refine ⟨8955178888477724638727621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23880477035940599036606989 8955178888477724638727621)
              ·
                refine ⟨1679096041589573369761429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8955178888477724638727621 1679096041589573369761429)
                ·
                  refine ⟨78707626949511251707567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1679096041589573369761429 78707626949511251707567)
                  ·
                    rfl

theorem cell23_1379543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 6].length) (baseStart_1379543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379543 prefixEnd_1379543 := by exact prefixLift 1379543
  have htrace : WordTrace (prefixWord ++ tailWord_1379543) baseStart_1379543 baseEnd_1379543 := by
    simpa [prefixWord, tailWord_1379543, baseEnd_1379543] using wordTrace_append hprefix tailTrace_1379543
  have hstable : (prefixWord ++ tailWord_1379543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379543).length < 2 ^ (prefixWord ++ tailWord_1379543).sum := by decide
  have hdescent : baseEnd_1379543 < baseStart_1379543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379647 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 3]
def baseStart_1379647 : Nat := 118140960795 + 1379647 * 2 ^ 59
def prefixEnd_1379647 : Nat := 4983230072969 + 3 ^ 40 * 1379647 * 2
def baseEnd_1379647 : Nat := 708422044533668858467625

theorem tailTrace_1379647 : CollatzResearch.WordTrace tailWord_1379647 prefixEnd_1379647 708422044533668858467625 := by
  unfold tailWord_1379647
  simp only [CollatzResearch.WordTrace]
  refine ⟨50319860032782018793649195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33546573355188012529099463 50319860032782018793649195)
  ·
    refine ⟨75479790049173028190473793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50319860032782018793649195 75479790049173028190473793)
    ·
      refine ⟨56609842536879771142855345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75479790049173028190473793 56609842536879771142855345)
      ·
        refine ⟨42457381902659828357141509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56609842536879771142855345 42457381902659828357141509)
        ·
          refine ⟨7960759106748717816964033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42457381902659828357141509 7960759106748717816964033)
          ·
            refine ⟨5970569330061538362723025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7960759106748717816964033 5970569330061538362723025)
            ·
              refine ⟨4477926997546153772042269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970569330061538362723025 4477926997546153772042269)
              ·
                refine ⟨1679222624079807664515851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4477926997546153772042269 1679222624079807664515851)
                ·
                  refine ⟨2518833936119711496773777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679222624079807664515851 2518833936119711496773777)
                  ·
                    refine ⟨1889125452089783622580333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2518833936119711496773777 1889125452089783622580333)
                    ·
                      refine ⟨708422044533668858467625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1889125452089783622580333 708422044533668858467625)
                      ·
                        rfl

theorem cell23_1379647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_1379647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379647 prefixEnd_1379647 := by exact prefixLift 1379647
  have htrace : WordTrace (prefixWord ++ tailWord_1379647) baseStart_1379647 baseEnd_1379647 := by
    simpa [prefixWord, tailWord_1379647, baseEnd_1379647] using wordTrace_append hprefix tailTrace_1379647
  have hstable : (prefixWord ++ tailWord_1379647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379647).length < 2 ^ (prefixWord ++ tailWord_1379647).sum := by decide
  have hdescent : baseEnd_1379647 < baseStart_1379647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379807 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1379807 : Nat := 118140960795 + 1379807 * 2 ^ 59
def prefixEnd_1379807 : Nat := 4983230072969 + 3 ^ 40 * 1379807 * 2
def baseEnd_1379807 : Nat := 708504201438388232466889

theorem tailTrace_1379807 : CollatzResearch.WordTrace tailWord_1379807 prefixEnd_1379807 708504201438388232466889 := by
  unfold tailWord_1379807
  simp only [CollatzResearch.WordTrace]
  refine ⟨50325695712202366119473675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33550463808134910746315783 50325695712202366119473675)
  ·
    refine ⟨75488543568303549179210513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50325695712202366119473675 75488543568303549179210513)
    ·
      refine ⟨56616407676227661884407885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75488543568303549179210513 56616407676227661884407885)
      ·
        refine ⟨21231152878585373206652957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56616407676227661884407885 21231152878585373206652957)
        ·
          refine ⟨7961682329469514952494859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21231152878585373206652957 7961682329469514952494859)
          ·
            refine ⟨11942523494204272428742289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7961682329469514952494859 11942523494204272428742289)
            ·
              refine ⟨8956892620653204321556717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11942523494204272428742289 8956892620653204321556717)
              ·
                refine ⟨3358834732744951620583769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8956892620653204321556717 3358834732744951620583769)
                ·
                  refine ⟨2519126049558713715437827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3358834732744951620583769 2519126049558713715437827)
                  ·
                    refine ⟨3778689074338070573156741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2519126049558713715437827 3778689074338070573156741)
                    ·
                      refine ⟨708504201438388232466889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3778689074338070573156741 708504201438388232466889)
                      ·
                        rfl

theorem cell23_1379807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1379807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379807 prefixEnd_1379807 := by exact prefixLift 1379807
  have htrace : WordTrace (prefixWord ++ tailWord_1379807) baseStart_1379807 baseEnd_1379807 := by
    simpa [prefixWord, tailWord_1379807, baseEnd_1379807] using wordTrace_append hprefix tailTrace_1379807
  have hstable : (prefixWord ++ tailWord_1379807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379807).length < 2 ^ (prefixWord ++ tailWord_1379807).sum := by decide
  have hdescent : baseEnd_1379807 < baseStart_1379807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379820 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1379820 : Nat := 118140960795 + 1379820 * 2 ^ 59
def prefixEnd_1379820 : Nat := 4983230072969 + 3 ^ 40 * 1379820 * 2
def baseEnd_1379820 : Nat := 708510876686896681604329

theorem tailTrace_1379820 : CollatzResearch.WordTrace tailWord_1379820 prefixEnd_1379820 708510876686896681604329 := by
  unfold tailWord_1379820
  simp only [CollatzResearch.WordTrace]
  refine ⟨25163084930577634669848457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33550779907436846226464609 25163084930577634669848457)
  ·
    refine ⟨18872313697933226002386343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25163084930577634669848457 18872313697933226002386343)
    ·
      refine ⟨28308470546899839003579515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18872313697933226002386343 28308470546899839003579515)
      ·
        refine ⟨42462705820349758505369273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28308470546899839003579515 42462705820349758505369273)
        ·
          refine ⟨31847029365262318879026955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42462705820349758505369273 31847029365262318879026955)
          ·
            refine ⟨47770544047893478318540433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31847029365262318879026955 47770544047893478318540433)
            ·
              refine ⟨35827908035920108738905325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47770544047893478318540433 35827908035920108738905325)
              ·
                refine ⟨13435465513470040777089497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35827908035920108738905325 13435465513470040777089497)
                ·
                  refine ⟨10076599135102530582817123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13435465513470040777089497 10076599135102530582817123)
                  ·
                    refine ⟨15114898702653795874225685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10076599135102530582817123 15114898702653795874225685)
                    ·
                      refine ⟨708510876686896681604329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15114898702653795874225685 708510876686896681604329)
                      ·
                        rfl

theorem cell23_1379820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1379820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379820 prefixEnd_1379820 := by exact prefixLift 1379820
  have htrace : WordTrace (prefixWord ++ tailWord_1379820) baseStart_1379820 baseEnd_1379820 := by
    simpa [prefixWord, tailWord_1379820, baseEnd_1379820] using wordTrace_append hprefix tailTrace_1379820
  have hstable : (prefixWord ++ tailWord_1379820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379820).length < 2 ^ (prefixWord ++ tailWord_1379820).sum := by decide
  have hdescent : baseEnd_1379820 < baseStart_1379820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379907 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 8, 4]
def baseStart_1379907 : Nat := 118140960795 + 1379907 * 2 ^ 59
def prefixEnd_1379907 : Nat := 4983230072969 + 3 ^ 40 * 1379907 * 2
def baseEnd_1379907 : Nat := 236185183167945947072143

theorem tailTrace_1379907 : CollatzResearch.WordTrace tailWord_1379907 prefixEnd_1379907 236185183167945947072143 := by
  unfold tailWord_1379907
  simp only [CollatzResearch.WordTrace]
  refine ⟨50329343011840083198113975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33552895341226722132075983 50329343011840083198113975)
  ·
    refine ⟨75494014517760124797170963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50329343011840083198113975 75494014517760124797170963)
    ·
      refine ⟨113241021776640187195756445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75494014517760124797170963 113241021776640187195756445)
      ·
        refine ⟨42465383166240070198408667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113241021776640187195756445 42465383166240070198408667)
        ·
          refine ⟨63698074749360105297613001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42465383166240070198408667 63698074749360105297613001)
          ·
            refine ⟨47773556062020078973209751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63698074749360105297613001 47773556062020078973209751)
            ·
              refine ⟨71660334093030118459814627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47773556062020078973209751 71660334093030118459814627)
              ·
                refine ⟨107490501139545177689721941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71660334093030118459814627 107490501139545177689721941)
                ·
                  refine ⟨1259654310229045051051429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 107490501139545177689721941 1259654310229045051051429)
                  ·
                    refine ⟨236185183167945947072143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259654310229045051051429 236185183167945947072143)
                    ·
                      rfl

theorem cell23_1379907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 4].length) (baseStart_1379907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379907 prefixEnd_1379907 := by exact prefixLift 1379907
  have htrace : WordTrace (prefixWord ++ tailWord_1379907) baseStart_1379907 baseEnd_1379907 := by
    simpa [prefixWord, tailWord_1379907, baseEnd_1379907] using wordTrace_append hprefix tailTrace_1379907
  have hstable : (prefixWord ++ tailWord_1379907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379907).length < 2 ^ (prefixWord ++ tailWord_1379907).sum := by decide
  have hdescent : baseEnd_1379907 < baseStart_1379907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379914 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_1379914 : Nat := 118140960795 + 1379914 * 2 ^ 59
def prefixEnd_1379914 : Nat := 4983230072969 + 3 ^ 40 * 1379914 * 2
def baseEnd_1379914 : Nat := 708559143868419313828897

theorem tailTrace_1379914 : CollatzResearch.WordTrace tailWord_1379914 prefixEnd_1379914 708559143868419313828897 := by
  unfold tailWord_1379914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12582399580703680848404699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33553065548543148929079197 12582399580703680848404699)
  ·
    refine ⟨18873599371055521272607049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12582399580703680848404699 18873599371055521272607049)
    ·
      refine ⟨14155199528291640954455287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18873599371055521272607049 14155199528291640954455287)
      ·
        refine ⟨21232799292437461431682931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14155199528291640954455287 21232799292437461431682931)
        ·
          refine ⟨31849198938656192147524397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21232799292437461431682931 31849198938656192147524397)
          ·
            refine ⟨11943449601996072055321649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31849198938656192147524397 11943449601996072055321649)
            ·
              refine ⟨8957587201497054041491237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11943449601996072055321649 8957587201497054041491237)
              ·
                refine ⟨1679547600280697632779607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8957587201497054041491237 1679547600280697632779607)
                ·
                  refine ⟨2519321400421046449169411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679547600280697632779607 2519321400421046449169411)
                  ·
                    refine ⟨3778982100631569673754117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2519321400421046449169411 3778982100631569673754117)
                    ·
                      refine ⟨708559143868419313828897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3778982100631569673754117 708559143868419313828897)
                      ·
                        rfl

theorem cell23_1379914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_1379914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379914 prefixEnd_1379914 := by exact prefixLift 1379914
  have htrace : WordTrace (prefixWord ++ tailWord_1379914) baseStart_1379914 baseEnd_1379914 := by
    simpa [prefixWord, tailWord_1379914, baseEnd_1379914] using wordTrace_append hprefix tailTrace_1379914
  have hstable : (prefixWord ++ tailWord_1379914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379914).length < 2 ^ (prefixWord ++ tailWord_1379914).sum := by decide
  have hdescent : baseEnd_1379914 < baseStart_1379914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379924 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1379924 : Nat := 118140960795 + 1379924 * 2 ^ 59
def prefixEnd_1379924 : Nat := 4983230072969 + 3 ^ 40 * 1379924 * 2
def baseEnd_1379924 : Nat := 236188092891654758234617

theorem tailTrace_1379924 : CollatzResearch.WordTrace tailWord_1379924 prefixEnd_1379924 236188092891654758234617 := by
  unfold tailWord_1379924
  simp only [CollatzResearch.WordTrace]
  refine ⟨25164981526389247550741413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33553308701852330067655217 25164981526389247550741413)
  ·
    refine ⟨4718434036197983915764015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25164981526389247550741413 4718434036197983915764015)
    ·
      refine ⟨7077651054296975873646023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4718434036197983915764015 7077651054296975873646023)
      ·
        refine ⟨10616476581445463810469035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7077651054296975873646023 10616476581445463810469035)
        ·
          refine ⟨15924714872168195715703553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616476581445463810469035 15924714872168195715703553)
          ·
            refine ⟨11943536154126146786777665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15924714872168195715703553 11943536154126146786777665)
            ·
              refine ⟨8957652115594610090083249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11943536154126146786777665 8957652115594610090083249)
              ·
                refine ⟨6718239086695957567562437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8957652115594610090083249 6718239086695957567562437)
                ·
                  refine ⟨1259669828755492043917957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6718239086695957567562437 1259669828755492043917957)
                  ·
                    refine ⟨236188092891654758234617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259669828755492043917957 236188092891654758234617)
                    ·
                      rfl

theorem cell23_1379924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1379924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379924 prefixEnd_1379924 := by exact prefixLift 1379924
  have htrace : WordTrace (prefixWord ++ tailWord_1379924) baseStart_1379924 baseEnd_1379924 := by
    simpa [prefixWord, tailWord_1379924, baseEnd_1379924] using wordTrace_append hprefix tailTrace_1379924
  have hstable : (prefixWord ++ tailWord_1379924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379924).length < 2 ^ (prefixWord ++ tailWord_1379924).sum := by decide
  have hdescent : baseEnd_1379924 < baseStart_1379924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379941 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_1379941 : Nat := 118140960795 + 1379941 * 2 ^ 59
def prefixEnd_1379941 : Nat := 4983230072969 + 3 ^ 40 * 1379941 * 2
def baseEnd_1379941 : Nat := 236191002615363569397091

theorem tailTrace_1379941 : CollatzResearch.WordTrace tailWord_1379941 prefixEnd_1379941 236191002615363569397091 := by
  unfold tailWord_1379941
  simp only [CollatzResearch.WordTrace]
  refine ⟨50330583093716907004851677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33553722062477938003234451 50330583093716907004851677)
  ·
    refine ⟨18873968660143840126819379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50330583093716907004851677 18873968660143840126819379)
    ·
      refine ⟨28310952990215760190229069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18873968660143840126819379 28310952990215760190229069)
      ·
        refine ⟨10616607371330910071335901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28310952990215760190229069 10616607371330910071335901)
        ·
          refine ⟨3981227764249091276750963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10616607371330910071335901 3981227764249091276750963)
          ·
            refine ⟨5971841646373636915126445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981227764249091276750963 5971841646373636915126445)
            ·
              refine ⟨2239440617390113843172417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5971841646373636915126445 2239440617390113843172417)
              ·
                refine ⟨1679580463042585382379313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239440617390113843172417 1679580463042585382379313)
                ·
                  refine ⟨1259685347281939036784485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1679580463042585382379313 1259685347281939036784485)
                  ·
                    refine ⟨236191002615363569397091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259685347281939036784485 236191002615363569397091)
                    ·
                      rfl

theorem cell23_1379941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_1379941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379941 prefixEnd_1379941 := by exact prefixLift 1379941
  have htrace : WordTrace (prefixWord ++ tailWord_1379941) baseStart_1379941 baseEnd_1379941 := by
    simpa [prefixWord, tailWord_1379941, baseEnd_1379941] using wordTrace_append hprefix tailTrace_1379941
  have hstable : (prefixWord ++ tailWord_1379941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379941).length < 2 ^ (prefixWord ++ tailWord_1379941).sum := by decide
  have hdescent : baseEnd_1379941 < baseStart_1379941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379977 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_1379977 : Nat := 118140960795 + 1379977 * 2 ^ 59
def prefixEnd_1379977 : Nat := 4983230072969 + 3 ^ 40 * 1379977 * 2
def baseEnd_1379977 : Nat := 708591493149652567341107

theorem tailTrace_1379977 : CollatzResearch.WordTrace tailWord_1379977 prefixEnd_1379977 708591493149652567341107 := by
  unfold tailWord_1379977
  simp only [CollatzResearch.WordTrace]
  refine ⟨50331896121586485153162185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33554597414390990102108123 50331896121586485153162185)
  ·
    refine ⟨37748922091189863864871639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50331896121586485153162185 37748922091189863864871639)
    ·
      refine ⟨56623383136784795797307459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37748922091189863864871639 56623383136784795797307459)
      ·
        refine ⟨84935074705177193695961189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56623383136784795797307459 84935074705177193695961189)
        ·
          refine ⟨15925326507220723817992723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84935074705177193695961189 15925326507220723817992723)
          ·
            refine ⟨23887989760831085726989085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15925326507220723817992723 23887989760831085726989085)
            ·
              refine ⟨8957996160311657147620907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23887989760831085726989085 8957996160311657147620907)
              ·
                refine ⟨13436994240467485721431361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8957996160311657147620907 13436994240467485721431361)
                ·
                  refine ⟨10077745680350614291073521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13436994240467485721431361 10077745680350614291073521)
                  ·
                    refine ⟨7558309260262960718305141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10077745680350614291073521 7558309260262960718305141)
                    ·
                      refine ⟨708591493149652567341107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7558309260262960718305141 708591493149652567341107)
                      ·
                        rfl

theorem cell23_1379977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_1379977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379977 prefixEnd_1379977 := by exact prefixLift 1379977
  have htrace : WordTrace (prefixWord ++ tailWord_1379977) baseStart_1379977 baseEnd_1379977 := by
    simpa [prefixWord, tailWord_1379977, baseEnd_1379977] using wordTrace_append hprefix tailTrace_1379977
  have hstable : (prefixWord ++ tailWord_1379977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379977).length < 2 ^ (prefixWord ++ tailWord_1379977).sum := by decide
  have hdescent : baseEnd_1379977 < baseStart_1379977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379982 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1379982 : Nat := 118140960795 + 1379982 * 2 ^ 59
def prefixEnd_1379982 : Nat := 4983230072969 + 3 ^ 40 * 1379982 * 2
def baseEnd_1379982 : Nat := 708594060552925047778585

theorem tailTrace_1379982 : CollatzResearch.WordTrace tailWord_1379982 prefixEnd_1379982 708594060552925047778585 := by
  unfold tailWord_1379982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291509810821046375886775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33554718991045580671396133 6291509810821046375886775)
  ·
    refine ⟨9437264716231569563830163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6291509810821046375886775 9437264716231569563830163)
    ·
      refine ⟨14155897074347354345745245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9437264716231569563830163 14155897074347354345745245)
      ·
        refine ⟨5308461402880257879654467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14155897074347354345745245 5308461402880257879654467)
        ·
          refine ⟨7962692104320386819481701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308461402880257879654467 7962692104320386819481701)
          ·
            refine ⟨1493004769560072528652819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7962692104320386819481701 1493004769560072528652819)
            ·
              refine ⟨2239507154340108792979229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493004769560072528652819 2239507154340108792979229)
              ·
                refine ⟨839815182877540797367211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2239507154340108792979229 839815182877540797367211)
                ·
                  refine ⟨1259722774316311196050817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839815182877540797367211 1259722774316311196050817)
                  ·
                    refine ⟨944792080737233397038113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1259722774316311196050817 944792080737233397038113)
                    ·
                      refine ⟨708594060552925047778585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944792080737233397038113 708594060552925047778585)
                      ·
                        rfl

theorem cell23_1379982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1379982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379982 prefixEnd_1379982 := by exact prefixLift 1379982
  have htrace : WordTrace (prefixWord ++ tailWord_1379982) baseStart_1379982 baseEnd_1379982 := by
    simpa [prefixWord, tailWord_1379982, baseEnd_1379982] using wordTrace_append hprefix tailTrace_1379982
  have hstable : (prefixWord ++ tailWord_1379982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379982).length < 2 ^ (prefixWord ++ tailWord_1379982).sum := by decide
  have hdescent : baseEnd_1379982 < baseStart_1379982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379998 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1379998 : Nat := 118140960795 + 1379998 * 2 ^ 59
def prefixEnd_1379998 : Nat := 4983230072969 + 3 ^ 40 * 1379998 * 2
def baseEnd_1379998 : Nat := 708602276243396985178511

theorem tailTrace_1379998 : CollatzResearch.WordTrace tailWord_1379998 prefixEnd_1379998 708602276243396985178511 := by
  unfold tailWord_1379998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291582756813800717459581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33555108036340270493117765 6291582756813800717459581)
  ·
    refine ⟨2359343533805175269047343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6291582756813800717459581 2359343533805175269047343)
    ·
      refine ⟨3539015300707762903571015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359343533805175269047343 3539015300707762903571015)
      ·
        refine ⟨5308522951061644355356523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539015300707762903571015 5308522951061644355356523)
        ·
          refine ⟨7962784426592466533034785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308522951061644355356523 7962784426592466533034785)
          ·
            refine ⟨5972088319944349899776089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962784426592466533034785 5972088319944349899776089)
            ·
              refine ⟨4479066239958262424832067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5972088319944349899776089 4479066239958262424832067)
              ·
                refine ⟨6718599359937393637248101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479066239958262424832067 6718599359937393637248101)
                ·
                  refine ⟨1259737379988261306984019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6718599359937393637248101 1259737379988261306984019)
                  ·
                    refine ⟨1889606069982391960476029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1259737379988261306984019 1889606069982391960476029)
                    ·
                      refine ⟨708602276243396985178511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1889606069982391960476029 708602276243396985178511)
                      ·
                        rfl

theorem cell23_1379998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1379998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379998 prefixEnd_1379998 := by exact prefixLift 1379998
  have htrace : WordTrace (prefixWord ++ tailWord_1379998) baseStart_1379998 baseEnd_1379998 := by
    simpa [prefixWord, tailWord_1379998, baseEnd_1379998] using wordTrace_append hprefix tailTrace_1379998
  have hstable : (prefixWord ++ tailWord_1379998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379998).length < 2 ^ (prefixWord ++ tailWord_1379998).sum := by decide
  have hdescent : baseEnd_1379998 < baseStart_1379998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1379999 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1379999 : Nat := 118140960795 + 1379999 * 2 ^ 59
def prefixEnd_1379999 : Nat := 4983230072969 + 3 ^ 40 * 1379999 * 2
def baseEnd_1379999 : Nat := 708602789724051481266007

theorem tailTrace_1379999 : CollatzResearch.WordTrace tailWord_1379999 prefixEnd_1379999 708602789724051481266007 := by
  unfold tailWord_1379999
  simp only [CollatzResearch.WordTrace]
  refine ⟨50332698527506782910463051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33555132351671188606975367 50332698527506782910463051)
  ·
    refine ⟨75499047791260174365694577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50332698527506782910463051 75499047791260174365694577)
    ·
      refine ⟨56624285843445130774270933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75499047791260174365694577 56624285843445130774270933)
      ·
        refine ⟨1327131699455745252521975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 56624285843445130774270933 1327131699455745252521975)
        ·
          refine ⟨1990697549183617878782963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327131699455745252521975 1990697549183617878782963)
          ·
            refine ⟨2986046323775426818174445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990697549183617878782963 2986046323775426818174445)
            ·
              refine ⟨1119767371415785056815417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2986046323775426818174445 1119767371415785056815417)
              ·
                refine ⟨839825528561838792611563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119767371415785056815417 839825528561838792611563)
                ·
                  refine ⟨1259738292842758188917345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839825528561838792611563 1259738292842758188917345)
                  ·
                    refine ⟨944803719632068641688009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1259738292842758188917345 944803719632068641688009)
                    ·
                      refine ⟨708602789724051481266007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944803719632068641688009 708602789724051481266007)
                      ·
                        rfl

theorem cell23_1379999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1379999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1379999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1379999 prefixEnd_1379999 := by exact prefixLift 1379999
  have htrace : WordTrace (prefixWord ++ tailWord_1379999) baseStart_1379999 baseEnd_1379999 := by
    simpa [prefixWord, tailWord_1379999, baseEnd_1379999] using wordTrace_append hprefix tailTrace_1379999
  have hstable : (prefixWord ++ tailWord_1379999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1379999).length < 2 ^ (prefixWord ++ tailWord_1379999).sum := by decide
  have hdescent : baseEnd_1379999 < baseStart_1379999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1379999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380027 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 7]
def baseStart_1380027 : Nat := 118140960795 + 1380027 * 2 ^ 59
def prefixEnd_1380027 : Nat := 4983230072969 + 3 ^ 40 * 1380027 * 2
def baseEnd_1380027 : Nat := 78735240798041930190653

theorem tailTrace_1380027 : CollatzResearch.WordTrace tailWord_1380027 prefixEnd_1380027 78735240798041930190653 := by
  unfold tailWord_1380027
  simp only [CollatzResearch.WordTrace]
  refine ⟨50333719771405343692482335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33555813180936895794988223 50333719771405343692482335)
  ·
    refine ⟨75500579657108015538723503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50333719771405343692482335 75500579657108015538723503)
    ·
      refine ⟨113250869485662023308085255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75500579657108015538723503 113250869485662023308085255)
      ·
        refine ⟨169876304228493034962127883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113250869485662023308085255 169876304228493034962127883)
        ·
          refine ⟨254814456342739552443191825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169876304228493034962127883 254814456342739552443191825)
          ·
            refine ⟨191110842257054664332393869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254814456342739552443191825 191110842257054664332393869)
            ·
              refine ⟨71666565846395499124647701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191110842257054664332393869 71666565846395499124647701)
              ·
                refine ⟨3359370274049789021467861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71666565846395499124647701 3359370274049789021467861)
                ·
                  refine ⟨78735240798041930190653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3359370274049789021467861 78735240798041930190653)
                  ·
                    rfl

theorem cell23_1380027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 7].length) (baseStart_1380027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380027 prefixEnd_1380027 := by exact prefixLift 1380027
  have htrace : WordTrace (prefixWord ++ tailWord_1380027) baseStart_1380027 baseEnd_1380027 := by
    simpa [prefixWord, tailWord_1380027, baseEnd_1380027] using wordTrace_append hprefix tailTrace_1380027
  have hstable : (prefixWord ++ tailWord_1380027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380027).length < 2 ^ (prefixWord ++ tailWord_1380027).sum := by decide
  have hdescent : baseEnd_1380027 < baseStart_1380027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380074 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1380074 : Nat := 118140960795 + 1380074 * 2 ^ 59
def prefixEnd_1380074 : Nat := 4983230072969 + 3 ^ 40 * 1380074 * 2
def baseEnd_1380074 : Nat := 236213766924379562609387

theorem tailTrace_1380074 : CollatzResearch.WordTrace tailWord_1380074 prefixEnd_1380074 236213766924379562609387 := by
  unfold tailWord_1380074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583858500558767679860819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33556956001490047146295517 12583858500558767679860819)
  ·
    refine ⟨18875787750838151519791229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12583858500558767679860819 18875787750838151519791229)
    ·
      refine ⟨7078420406564306819921711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18875787750838151519791229 7078420406564306819921711)
      ·
        refine ⟨10617630609846460229882567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078420406564306819921711 10617630609846460229882567)
        ·
          refine ⟨15926445914769690344823851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10617630609846460229882567 15926445914769690344823851)
          ·
            refine ⟨23889668872154535517235777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15926445914769690344823851 23889668872154535517235777)
            ·
              refine ⟨17917251654115901637926833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23889668872154535517235777 17917251654115901637926833)
              ·
                refine ⟨13437938740586926228445125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17917251654115901637926833 13437938740586926228445125)
                ·
                  refine ⟨2519613513860048667833461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13437938740586926228445125 2519613513860048667833461)
                  ·
                    refine ⟨236213766924379562609387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2519613513860048667833461 236213766924379562609387)
                    ·
                      rfl

theorem cell23_1380074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1380074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380074 prefixEnd_1380074 := by exact prefixLift 1380074
  have htrace : WordTrace (prefixWord ++ tailWord_1380074) baseStart_1380074 baseEnd_1380074 := by
    simpa [prefixWord, tailWord_1380074, baseEnd_1380074] using wordTrace_append hprefix tailTrace_1380074
  have hstable : (prefixWord ++ tailWord_1380074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380074).length < 2 ^ (prefixWord ++ tailWord_1380074).sum := by decide
  have hdescent : baseEnd_1380074 < baseStart_1380074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380124 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1380124 : Nat := 118140960795 + 1380124 * 2 ^ 59
def prefixEnd_1380124 : Nat := 4983230072969 + 3 ^ 40 * 1380124 * 2
def baseEnd_1380124 : Nat := 708666974805863492202931

theorem tailTrace_1380124 : CollatzResearch.WordTrace tailWord_1380124 prefixEnd_1380124 708666974805863492202931 := by
  unfold tailWord_1380124
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168628826026964629381713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33558171768035952839175617 25168628826026964629381713)
  ·
    refine ⟨18876471619520223472036285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25168628826026964629381713 18876471619520223472036285)
    ·
      refine ⟨7078676857320083802013607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18876471619520223472036285 7078676857320083802013607)
      ·
        refine ⟨10618015285980125703020411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078676857320083802013607 10618015285980125703020411)
        ·
          refine ⟨15927022928970188554530617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10618015285980125703020411 15927022928970188554530617)
          ·
            refine ⟨11945267196727641415897963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15927022928970188554530617 11945267196727641415897963)
            ·
              refine ⟨17917900795091462123846945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11945267196727641415897963 17917900795091462123846945)
              ·
                refine ⟨13438425596318596592885209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17917900795091462123846945 13438425596318596592885209)
                ·
                  refine ⟨10078819197238947444663907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13438425596318596592885209 10078819197238947444663907)
                  ·
                    refine ⟨15118228795858421166995861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10078819197238947444663907 15118228795858421166995861)
                    ·
                      refine ⟨708666974805863492202931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15118228795858421166995861 708666974805863492202931)
                      ·
                        rfl

theorem cell23_1380124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1380124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380124 prefixEnd_1380124 := by exact prefixLift 1380124
  have htrace : WordTrace (prefixWord ++ tailWord_1380124) baseStart_1380124 baseEnd_1380124 := by
    simpa [prefixWord, tailWord_1380124, baseEnd_1380124] using wordTrace_append hprefix tailTrace_1380124
  have hstable : (prefixWord ++ tailWord_1380124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380124).length < 2 ^ (prefixWord ++ tailWord_1380124).sum := by decide
  have hdescent : baseEnd_1380124 < baseStart_1380124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380148 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1380148 : Nat := 118140960795 + 1380148 * 2 ^ 59
def prefixEnd_1380148 : Nat := 4983230072969 + 3 ^ 40 * 1380148 * 2
def baseEnd_1380148 : Nat := 708679298341571398302821

theorem tailTrace_1380148 : CollatzResearch.WordTrace tailWord_1380148 prefixEnd_1380148 708679298341571398302821 := by
  unfold tailWord_1380148
  simp only [CollatzResearch.WordTrace]
  refine ⟨25169066501983490678818549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33558755335977987571758065 25169066501983490678818549)
  ·
    refine ⟨2359599984560952251139239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25169066501983490678818549 2359599984560952251139239)
    ·
      refine ⟨3539399976841428376708859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359599984560952251139239 3539399976841428376708859)
      ·
        refine ⟨5309099965262142565063289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539399976841428376708859 5309099965262142565063289)
        ·
          refine ⟨3981824973946606923797467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5309099965262142565063289 3981824973946606923797467)
          ·
            refine ⟨5972737460919910385696201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981824973946606923797467 5972737460919910385696201)
            ·
              refine ⟨4479553095689932789272151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5972737460919910385696201 4479553095689932789272151)
              ·
                refine ⟨6719329643534899183908227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479553095689932789272151 6719329643534899183908227)
                ·
                  refine ⟨10078994465302348775862341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719329643534899183908227 10078994465302348775862341)
                  ·
                    refine ⟨1889811462244190395474189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10078994465302348775862341 1889811462244190395474189)
                    ·
                      refine ⟨708679298341571398302821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1889811462244190395474189 708679298341571398302821)
                      ·
                        rfl

theorem cell23_1380148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1380148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380148 prefixEnd_1380148 := by exact prefixLift 1380148
  have htrace : WordTrace (prefixWord ++ tailWord_1380148) baseStart_1380148 baseEnd_1380148 := by
    simpa [prefixWord, tailWord_1380148, baseEnd_1380148] using wordTrace_append hprefix tailTrace_1380148
  have hstable : (prefixWord ++ tailWord_1380148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380148).length < 2 ^ (prefixWord ++ tailWord_1380148).sum := by decide
  have hdescent : baseEnd_1380148 < baseStart_1380148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380172 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_1380172 : Nat := 118140960795 + 1380172 * 2 ^ 59
def prefixEnd_1380172 : Nat := 4983230072969 + 3 ^ 40 * 1380172 * 2
def baseEnd_1380172 : Nat := 236230540625759768134237

theorem tailTrace_1380172 : CollatzResearch.WordTrace tailWord_1380172 prefixEnd_1380172 236230540625759768134237 := by
  unfold tailWord_1380172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25169504177940016728255385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33559338903920022304340513 25169504177940016728255385)
  ·
    refine ⟨18877128133455012546191539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25169504177940016728255385 18877128133455012546191539)
    ·
      refine ⟨28315692200182518819287309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18877128133455012546191539 28315692200182518819287309)
      ·
        refine ⟨10618384575068444557232741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28315692200182518819287309 10618384575068444557232741)
        ·
          refine ⟨1990947107825333354481139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10618384575068444557232741 1990947107825333354481139)
          ·
            refine ⟨2986420661738000031721709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990947107825333354481139 2986420661738000031721709)
            ·
              refine ⟨1119907748151750011895641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2986420661738000031721709 1119907748151750011895641)
              ·
                refine ⟨839930811113812508921731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119907748151750011895641 839930811113812508921731)
                ·
                  refine ⟨1259896216670718763382597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839930811113812508921731 1259896216670718763382597)
                  ·
                    refine ⟨236230540625759768134237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259896216670718763382597 236230540625759768134237)
                    ·
                      rfl

theorem cell23_1380172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_1380172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380172 prefixEnd_1380172 := by exact prefixLift 1380172
  have htrace : WordTrace (prefixWord ++ tailWord_1380172) baseStart_1380172 baseEnd_1380172 := by
    simpa [prefixWord, tailWord_1380172, baseEnd_1380172] using wordTrace_append hprefix tailTrace_1380172
  have hstable : (prefixWord ++ tailWord_1380172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380172).length < 2 ^ (prefixWord ++ tailWord_1380172).sum := by decide
  have hdescent : baseEnd_1380172 < baseStart_1380172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380174 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1380174 : Nat := 118140960795 + 1380174 * 2 ^ 59
def prefixEnd_1380174 : Nat := 4983230072969 + 3 ^ 40 * 1380174 * 2
def baseEnd_1380174 : Nat := 708692648838588296577701

theorem tailTrace_1380174 : CollatzResearch.WordTrace tailWord_1380174 prefixEnd_1380174 708692648838588296577701 := by
  unfold tailWord_1380174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292385162734098474760447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33559387534581858532055717 6292385162734098474760447)
  ·
    refine ⟨9438577744101147712140671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6292385162734098474760447 9438577744101147712140671)
    ·
      refine ⟨14157866616151721568211007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9438577744101147712140671 14157866616151721568211007)
      ·
        refine ⟨21236799924227582352316511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14157866616151721568211007 21236799924227582352316511)
        ·
          refine ⟨31855199886341373528474767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21236799924227582352316511 31855199886341373528474767)
          ·
            refine ⟨47782799829512060292712151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31855199886341373528474767 47782799829512060292712151)
            ·
              refine ⟨71674199744268090439068227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47782799829512060292712151 71674199744268090439068227)
              ·
                refine ⟨107511299616402135658602341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71674199744268090439068227 107511299616402135658602341)
                ·
                  refine ⟨20158368678075400435987939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107511299616402135658602341 20158368678075400435987939)
                  ·
                    refine ⟨30237553017113100653981909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20158368678075400435987939 30237553017113100653981909)
                    ·
                      refine ⟨708692648838588296577701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30237553017113100653981909 708692648838588296577701)
                      ·
                        rfl

theorem cell23_1380174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1380174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380174 prefixEnd_1380174 := by exact prefixLift 1380174
  have htrace : WordTrace (prefixWord ++ tailWord_1380174) baseStart_1380174 baseEnd_1380174 := by
    simpa [prefixWord, tailWord_1380174, baseEnd_1380174] using wordTrace_append hprefix tailTrace_1380174
  have hstable : (prefixWord ++ tailWord_1380174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380174).length < 2 ^ (prefixWord ++ tailWord_1380174).sum := by decide
  have hdescent : baseEnd_1380174 < baseStart_1380174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380184 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1380184 : Nat := 118140960795 + 1380184 * 2 ^ 59
def prefixEnd_1380184 : Nat := 4983230072969 + 3 ^ 40 * 1380184 * 2
def baseEnd_1380184 : Nat := 708697783645133257452655

theorem tailTrace_1380184 : CollatzResearch.WordTrace tailWord_1380184 prefixEnd_1380184 708697783645133257452655 := by
  unfold tailWord_1380184
  simp only [CollatzResearch.WordTrace]
  refine ⟨25169723015918279752973803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33559630687891039670631737 25169723015918279752973803)
  ·
    refine ⟨37754584523877419629460705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25169723015918279752973803 37754584523877419629460705)
    ·
      refine ⟨28315938392908064722095529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37754584523877419629460705 28315938392908064722095529)
      ·
        refine ⟨21236953794681048541571647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28315938392908064722095529 21236953794681048541571647)
        ·
          refine ⟨31855430692021572812357471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21236953794681048541571647 31855430692021572812357471)
          ·
            refine ⟨47783146038032359218536207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31855430692021572812357471 47783146038032359218536207)
            ·
              refine ⟨71674719057048538827804311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47783146038032359218536207 71674719057048538827804311)
              ·
                refine ⟨107512078585572808241706467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71674719057048538827804311 107512078585572808241706467)
                ·
                  refine ⟨161268117878359212362559701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107512078585572808241706467 161268117878359212362559701)
                  ·
                    refine ⟨3779721512774044039747493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 161268117878359212362559701 3779721512774044039747493)
                    ·
                      refine ⟨708697783645133257452655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3779721512774044039747493 708697783645133257452655)
                      ·
                        rfl

theorem cell23_1380184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1380184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380184 prefixEnd_1380184 := by exact prefixLift 1380184
  have htrace : WordTrace (prefixWord ++ tailWord_1380184) baseStart_1380184 baseEnd_1380184 := by
    simpa [prefixWord, tailWord_1380184, baseEnd_1380184] using wordTrace_append hprefix tailTrace_1380184
  have hstable : (prefixWord ++ tailWord_1380184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380184).length < 2 ^ (prefixWord ++ tailWord_1380184).sum := by decide
  have hdescent : baseEnd_1380184 < baseStart_1380184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380201 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 6, 2]
def baseStart_1380201 : Nat := 118140960795 + 1380201 * 2 ^ 59
def prefixEnd_1380201 : Nat := 4983230072969 + 3 ^ 40 * 1380201 * 2
def baseEnd_1380201 : Nat := 708706512816259690940077

theorem tailTrace_1380201 : CollatzResearch.WordTrace tailWord_1380201 prefixEnd_1380201 708706512816259690940077 := by
  unfold tailWord_1380201
  simp only [CollatzResearch.WordTrace]
  refine ⟨50340066072774971409316457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33560044048516647606210971 50340066072774971409316457)
  ·
    refine ⟨37755049554581228556987343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50340066072774971409316457 37755049554581228556987343)
    ·
      refine ⟨56632574331871842835481015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37755049554581228556987343 56632574331871842835481015)
      ·
        refine ⟨84948861497807764253221523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56632574331871842835481015 84948861497807764253221523)
        ·
          refine ⟨127423292246711646379832285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84948861497807764253221523 127423292246711646379832285)
          ·
            refine ⟨47783734592516867392437107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127423292246711646379832285 47783734592516867392437107)
            ·
              refine ⟨71675601888775301088655661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47783734592516867392437107 71675601888775301088655661)
              ·
                refine ⟨26878350708290737908245873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71675601888775301088655661 26878350708290737908245873)
                ·
                  refine ⟨20158763031218053431184405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26878350708290737908245873 20158763031218053431184405)
                  ·
                    refine ⟨944942017088346254586769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20158763031218053431184405 944942017088346254586769)
                    ·
                      refine ⟨708706512816259690940077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944942017088346254586769 708706512816259690940077)
                      ·
                        rfl

theorem cell23_1380201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 6, 2].length) (baseStart_1380201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380201 prefixEnd_1380201 := by exact prefixLift 1380201
  have htrace : WordTrace (prefixWord ++ tailWord_1380201) baseStart_1380201 baseEnd_1380201 := by
    simpa [prefixWord, tailWord_1380201, baseEnd_1380201] using wordTrace_append hprefix tailTrace_1380201
  have hstable : (prefixWord ++ tailWord_1380201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380201).length < 2 ^ (prefixWord ++ tailWord_1380201).sum := by decide
  have hdescent : baseEnd_1380201 < baseStart_1380201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380222 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1380222 : Nat := 118140960795 + 1380222 * 2 ^ 59
def prefixEnd_1380222 : Nat := 4983230072969 + 3 ^ 40 * 1380222 * 2
def baseEnd_1380222 : Nat := 708717295910004108777481

theorem tailTrace_1380222 : CollatzResearch.WordTrace tailWord_1380222 prefixEnd_1380222 708717295910004108777481 := by
  unfold tailWord_1380222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292604000712361499478865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33560554670465927997220613 6292604000712361499478865)
  ·
    refine ⟨4719453000534271124609149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6292604000712361499478865 4719453000534271124609149)
    ·
      refine ⟨1769794875200351671728431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4719453000534271124609149 1769794875200351671728431)
      ·
        refine ⟨2654692312800527507592647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769794875200351671728431 2654692312800527507592647)
        ·
          refine ⟨3982038469200791261388971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654692312800527507592647 3982038469200791261388971)
          ·
            refine ⟨5973057703801186892083457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982038469200791261388971 5973057703801186892083457)
            ·
              refine ⟨4479793277850890169062593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5973057703801186892083457 4479793277850890169062593)
              ·
                refine ⟨3359844958388167626796945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479793277850890169062593 3359844958388167626796945)
                ·
                  refine ⟨2519883718791125720097709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359844958388167626796945 2519883718791125720097709)
                  ·
                    refine ⟨944956394546672145036641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519883718791125720097709 944956394546672145036641)
                    ·
                      refine ⟨708717295910004108777481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944956394546672145036641 708717295910004108777481)
                      ·
                        rfl

theorem cell23_1380222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1380222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380222 prefixEnd_1380222 := by exact prefixLift 1380222
  have htrace : WordTrace (prefixWord ++ tailWord_1380222) baseStart_1380222 baseEnd_1380222 := by
    simpa [prefixWord, tailWord_1380222, baseEnd_1380222] using wordTrace_append hprefix tailTrace_1380222
  have hstable : (prefixWord ++ tailWord_1380222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380222).length < 2 ^ (prefixWord ++ tailWord_1380222).sum := by decide
  have hdescent : baseEnd_1380222 < baseStart_1380222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380228 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1380228 : Nat := 118140960795 + 1380228 * 2 ^ 59
def prefixEnd_1380228 : Nat := 4983230072969 + 3 ^ 40 * 1380228 * 2
def baseEnd_1380228 : Nat := 236240125597977028434151

theorem tailTrace_1380228 : CollatzResearch.WordTrace tailWord_1380228 prefixEnd_1380228 236240125597977028434151 := by
  unfold tailWord_1380228
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170525421838577510274669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33560700562451436680366225 25170525421838577510274669)
  ·
    refine ⟨9438947033189466566353001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25170525421838577510274669 9438947033189466566353001)
    ·
      refine ⟨7079210274892099924764751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9438947033189466566353001 7079210274892099924764751)
      ·
        refine ⟨10618815412338149887147127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7079210274892099924764751 10618815412338149887147127)
        ·
          refine ⟨15928223118507224830720691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10618815412338149887147127 15928223118507224830720691)
          ·
            refine ⟨23892334677760837246081037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15928223118507224830720691 23892334677760837246081037)
            ·
              refine ⟨8959625504160313967280389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23892334677760837246081037 8959625504160313967280389)
              ·
                refine ⟨1679929782030058868865073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8959625504160313967280389 1679929782030058868865073)
                ·
                  refine ⟨1259947336522544151648805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1679929782030058868865073 1259947336522544151648805)
                  ·
                    refine ⟨236240125597977028434151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259947336522544151648805 236240125597977028434151)
                    ·
                      rfl

theorem cell23_1380228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1380228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380228 prefixEnd_1380228 := by exact prefixLift 1380228
  have htrace : WordTrace (prefixWord ++ tailWord_1380228) baseStart_1380228 baseEnd_1380228 := by
    simpa [prefixWord, tailWord_1380228, baseEnd_1380228] using wordTrace_append hprefix tailTrace_1380228
  have hstable : (prefixWord ++ tailWord_1380228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380228).length < 2 ^ (prefixWord ++ tailWord_1380228).sum := by decide
  have hdescent : baseEnd_1380228 < baseStart_1380228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380252 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1380252 : Nat := 118140960795 + 1380252 * 2 ^ 59
def prefixEnd_1380252 : Nat := 4983230072969 + 3 ^ 40 * 1380252 * 2
def baseEnd_1380252 : Nat := 708732700329638991402343

theorem tailTrace_1380252 : CollatzResearch.WordTrace tailWord_1380252 prefixEnd_1380252 708732700329638991402343 := by
  unfold tailWord_1380252
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170963097795103559711505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33561284130393471412948673 25170963097795103559711505)
  ·
    refine ⟨18878222323346327669783629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25170963097795103559711505 18878222323346327669783629)
    ·
      refine ⟨7079333371254872876168861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18878222323346327669783629 7079333371254872876168861)
      ·
        refine ⟨2654750014220577328563323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7079333371254872876168861 2654750014220577328563323)
        ·
          refine ⟨3982125021330865992844985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654750014220577328563323 3982125021330865992844985)
          ·
            refine ⟨2986593765998149494633739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3982125021330865992844985 2986593765998149494633739)
            ·
              refine ⟨4479890648997224241950609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986593765998149494633739 4479890648997224241950609)
              ·
                refine ⟨3359917986747918181462957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479890648997224241950609 3359917986747918181462957)
                ·
                  refine ⟨1259969245030469318048609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3359917986747918181462957 1259969245030469318048609)
                  ·
                    refine ⟨944976933772851988536457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1259969245030469318048609 944976933772851988536457)
                    ·
                      refine ⟨708732700329638991402343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 944976933772851988536457 708732700329638991402343)
                      ·
                        rfl

theorem cell23_1380252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1380252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380252 prefixEnd_1380252 := by exact prefixLift 1380252
  have htrace : WordTrace (prefixWord ++ tailWord_1380252) baseStart_1380252 baseEnd_1380252 := by
    simpa [prefixWord, tailWord_1380252, baseEnd_1380252] using wordTrace_append hprefix tailTrace_1380252
  have hstable : (prefixWord ++ tailWord_1380252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380252).length < 2 ^ (prefixWord ++ tailWord_1380252).sum := by decide
  have hdescent : baseEnd_1380252 < baseStart_1380252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380285 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1380285 : Nat := 118140960795 + 1380285 * 2 ^ 59
def prefixEnd_1380285 : Nat := 4983230072969 + 3 ^ 40 * 1380285 * 2
def baseEnd_1380285 : Nat := 708749645191237362289691

theorem tailTrace_1380285 : CollatzResearch.WordTrace tailWord_1380285 prefixEnd_1380285 708749645191237362289691 := by
  unfold tailWord_1380285
  simp only [CollatzResearch.WordTrace]
  refine ⟨50343129804470653755374309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33562086536313769170249539 50343129804470653755374309)
  ·
    refine ⟨9439336838338247579132683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50343129804470653755374309 9439336838338247579132683)
    ·
      refine ⟨14159005257507371368699025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439336838338247579132683 14159005257507371368699025)
      ·
        refine ⟨10619253943130528526524269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14159005257507371368699025 10619253943130528526524269)
        ·
          refine ⟨3982220228673948197446601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10619253943130528526524269 3982220228673948197446601)
          ·
            refine ⟨2986665171505461148084951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3982220228673948197446601 2986665171505461148084951)
            ·
              refine ⟨4479997757258191722127427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986665171505461148084951 4479997757258191722127427)
              ·
                refine ⟨6719996635887287583191141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479997757258191722127427 6719996635887287583191141)
                ·
                  refine ⟨1259999369228866421848339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6719996635887287583191141 1259999369228866421848339)
                  ·
                    refine ⟨1889999053843299632772509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1259999369228866421848339 1889999053843299632772509)
                    ·
                      refine ⟨708749645191237362289691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1889999053843299632772509 708749645191237362289691)
                      ·
                        rfl

theorem cell23_1380285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1380285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380285 prefixEnd_1380285 := by exact prefixLift 1380285
  have htrace : WordTrace (prefixWord ++ tailWord_1380285) baseStart_1380285 baseEnd_1380285 := by
    simpa [prefixWord, tailWord_1380285, baseEnd_1380285] using wordTrace_append hprefix tailTrace_1380285
  have hstable : (prefixWord ++ tailWord_1380285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380285).length < 2 ^ (prefixWord ++ tailWord_1380285).sum := by decide
  have hdescent : baseEnd_1380285 < baseStart_1380285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380302 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_1380302 : Nat := 118140960795 + 1380302 * 2 ^ 59
def prefixEnd_1380302 : Nat := 4983230072969 + 3 ^ 40 * 1380302 * 2
def baseEnd_1380302 : Nat := 708758374362363795777113

theorem tailTrace_1380302 : CollatzResearch.WordTrace tailWord_1380302 prefixEnd_1380302 708758374362363795777113 := by
  unfold tailWord_1380302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292968730676133207342895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33562499896939377105828773 6292968730676133207342895)
  ·
    refine ⟨9439453096014199811014343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6292968730676133207342895 9439453096014199811014343)
    ·
      refine ⟨14159179644021299716521515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439453096014199811014343 14159179644021299716521515)
      ·
        refine ⟨21238769466031949574782273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159179644021299716521515 21238769466031949574782273)
        ·
          refine ⟨15929077099523962181086705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21238769466031949574782273 15929077099523962181086705)
          ·
            refine ⟨11946807824642971635815029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15929077099523962181086705 11946807824642971635815029)
            ·
              refine ⟨1120013233560278590857659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11946807824642971635815029 1120013233560278590857659)
              ·
                refine ⟨1680019850340417886286489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120013233560278590857659 1680019850340417886286489)
                ·
                  refine ⟨1260014887755313414714867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680019850340417886286489 1260014887755313414714867)
                  ·
                    refine ⟨1890022331632970122072301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1260014887755313414714867 1890022331632970122072301)
                    ·
                      refine ⟨708758374362363795777113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1890022331632970122072301 708758374362363795777113)
                      ·
                        rfl

theorem cell23_1380302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_1380302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380302 prefixEnd_1380302 := by exact prefixLift 1380302
  have htrace : WordTrace (prefixWord ++ tailWord_1380302) baseStart_1380302 baseEnd_1380302 := by
    simpa [prefixWord, tailWord_1380302, baseEnd_1380302] using wordTrace_append hprefix tailTrace_1380302
  have hstable : (prefixWord ++ tailWord_1380302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380302).length < 2 ^ (prefixWord ++ tailWord_1380302).sum := by decide
  have hdescent : baseEnd_1380302 < baseStart_1380302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380311 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1380311 : Nat := 118140960795 + 1380311 * 2 ^ 59
def prefixEnd_1380311 : Nat := 4983230072969 + 3 ^ 40 * 1380311 * 2
def baseEnd_1380311 : Nat := 708762995688254260564571

theorem tailTrace_1380311 : CollatzResearch.WordTrace tailWord_1380311 prefixEnd_1380311 708762995688254260564571 := by
  unfold tailWord_1380311
  simp only [CollatzResearch.WordTrace]
  refine ⟨50344078102376460195820787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33562718734917640130547191 50344078102376460195820787)
  ·
    refine ⟨75516117153564690293731181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50344078102376460195820787 75516117153564690293731181)
    ·
      refine ⟨28318543932586758860149193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75516117153564690293731181 28318543932586758860149193)
      ·
        refine ⟨21238907949440069145111895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28318543932586758860149193 21238907949440069145111895)
        ·
          refine ⟨31858361924160103717667843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21238907949440069145111895 31858361924160103717667843)
          ·
            refine ⟨47787542886240155576501765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31858361924160103717667843 47787542886240155576501765)
            ·
              refine ⟨8960164291170029170594081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47787542886240155576501765 8960164291170029170594081)
              ·
                refine ⟨6720123218377521877945561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8960164291170029170594081 6720123218377521877945561)
                ·
                  refine ⟨5040092413783141408459171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6720123218377521877945561 5040092413783141408459171)
                  ·
                    refine ⟨7560138620674712112688757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5040092413783141408459171 7560138620674712112688757)
                    ·
                      refine ⟨708762995688254260564571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7560138620674712112688757 708762995688254260564571)
                      ·
                        rfl

theorem cell23_1380311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1380311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380311 prefixEnd_1380311 := by exact prefixLift 1380311
  have htrace : WordTrace (prefixWord ++ tailWord_1380311) baseStart_1380311 baseEnd_1380311 := by
    simpa [prefixWord, tailWord_1380311, baseEnd_1380311] using wordTrace_append hprefix tailTrace_1380311
  have hstable : (prefixWord ++ tailWord_1380311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380311).length < 2 ^ (prefixWord ++ tailWord_1380311).sum := by decide
  have hdescent : baseEnd_1380311 < baseStart_1380311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380321 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_1380321 : Nat := 118140960795 + 1380321 * 2 ^ 59
def prefixEnd_1380321 : Nat := 4983230072969 + 3 ^ 40 * 1380321 * 2
def baseEnd_1380321 : Nat := 708768130494799221439525

theorem tailTrace_1380321 : CollatzResearch.WordTrace tailWord_1380321 prefixEnd_1380321 708768130494799221439525 := by
  unfold tailWord_1380321
  simp only [CollatzResearch.WordTrace]
  refine ⟨50344442832340231903684817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33562961888226821269123211 50344442832340231903684817)
  ·
    refine ⟨37758332124255173927763613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50344442832340231903684817 37758332124255173927763613)
    ·
      refine ⟨14159374546595690222911355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37758332124255173927763613 14159374546595690222911355)
      ·
        refine ⟨21239061819893535334367033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159374546595690222911355 21239061819893535334367033)
        ·
          refine ⟨15929296364920151500775275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21239061819893535334367033 15929296364920151500775275)
          ·
            refine ⟨23893944547380227251162913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15929296364920151500775275 23893944547380227251162913)
            ·
              refine ⟨17920458410535170438372185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23893944547380227251162913 17920458410535170438372185)
              ·
                refine ⟨13440343807901377828779139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17920458410535170438372185 13440343807901377828779139)
                ·
                  refine ⟨20160515711852066743168709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13440343807901377828779139 20160515711852066743168709)
                  ·
                    refine ⟨3780096695972262514344133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20160515711852066743168709 3780096695972262514344133)
                    ·
                      refine ⟨708768130494799221439525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3780096695972262514344133 708768130494799221439525)
                      ·
                        rfl

theorem cell23_1380321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_1380321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380321 prefixEnd_1380321 := by exact prefixLift 1380321
  have htrace : WordTrace (prefixWord ++ tailWord_1380321) baseStart_1380321 baseEnd_1380321 := by
    simpa [prefixWord, tailWord_1380321, baseEnd_1380321] using wordTrace_append hprefix tailTrace_1380321
  have hstable : (prefixWord ++ tailWord_1380321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380321).length < 2 ^ (prefixWord ++ tailWord_1380321).sum := by decide
  have hdescent : baseEnd_1380321 < baseStart_1380321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380359 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_1380359 : Nat := 118140960795 + 1380359 * 2 ^ 59
def prefixEnd_1380359 : Nat := 4983230072969 + 3 ^ 40 * 1380359 * 2
def baseEnd_1380359 : Nat := 708787642759670072764351

theorem tailTrace_1380359 : CollatzResearch.WordTrace tailWord_1380359 prefixEnd_1380359 708787642759670072764351 := by
  unfold tailWord_1380359
  simp only [CollatzResearch.WordTrace]
  refine ⟨50345828806202564393568131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33563885870801709595712087 50345828806202564393568131)
  ·
    refine ⟨75518743209303846590352197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50345828806202564393568131 75518743209303846590352197)
    ·
      refine ⟨14159764351744471235691037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75518743209303846590352197 14159764351744471235691037)
      ·
        refine ⟨5309911631904176713384139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14159764351744471235691037 5309911631904176713384139)
        ·
          refine ⟨7964867447856265070076209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5309911631904176713384139 7964867447856265070076209)
          ·
            refine ⟨5973650585892198802557157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7964867447856265070076209 5973650585892198802557157)
            ·
              refine ⟨1120059484854787275479467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5973650585892198802557157 1120059484854787275479467)
              ·
                refine ⟨1680089227282180913219201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120059484854787275479467 1680089227282180913219201)
                ·
                  refine ⟨1260066920461635684914401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680089227282180913219201 1260066920461635684914401)
                  ·
                    refine ⟨945050190346226763685801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260066920461635684914401 945050190346226763685801)
                    ·
                      refine ⟨708787642759670072764351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945050190346226763685801 708787642759670072764351)
                      ·
                        rfl

theorem cell23_1380359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_1380359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380359 prefixEnd_1380359 := by exact prefixLift 1380359
  have htrace : WordTrace (prefixWord ++ tailWord_1380359) baseStart_1380359 baseEnd_1380359 := by
    simpa [prefixWord, tailWord_1380359, baseEnd_1380359] using wordTrace_append hprefix tailTrace_1380359
  have hstable : (prefixWord ++ tailWord_1380359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380359).length < 2 ^ (prefixWord ++ tailWord_1380359).sum := by decide
  have hdescent : baseEnd_1380359 < baseStart_1380359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380368 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 2, 5, 2]
def baseStart_1380368 : Nat := 118140960795 + 1380368 * 2 ^ 59
def prefixEnd_1380368 : Nat := 4983230072969 + 3 ^ 40 * 1380368 * 2
def baseEnd_1380368 : Nat := 708792264085560537551809

theorem tailTrace_1380368 : CollatzResearch.WordTrace tailWord_1380368 prefixEnd_1380368 708792264085560537551809 := by
  unfold tailWord_1380368
  simp only [CollatzResearch.WordTrace]
  refine ⟨25173078531584979465322879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33564104708779972620430505 25173078531584979465322879)
  ·
    refine ⟨37759617797377469197984319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25173078531584979465322879 37759617797377469197984319)
    ·
      refine ⟨56639426696066203796976479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37759617797377469197984319 56639426696066203796976479)
      ·
        refine ⟨84959140044099305695464719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56639426696066203796976479 84959140044099305695464719)
        ·
          refine ⟨127438710066148958543197079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84959140044099305695464719 127438710066148958543197079)
          ·
            refine ⟨191158065099223437814795619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127438710066148958543197079 191158065099223437814795619)
            ·
              refine ⟨286737097648835156722193429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191158065099223437814795619 286737097648835156722193429)
              ·
                refine ⟨13440801452289147971352817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 286737097648835156722193429 13440801452289147971352817)
                ·
                  refine ⟨10080601089216860978514613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13440801452289147971352817 10080601089216860978514613)
                  ·
                    refine ⟨945056352114080716735745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10080601089216860978514613 945056352114080716735745)
                    ·
                      refine ⟨708792264085560537551809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945056352114080716735745 708792264085560537551809)
                      ·
                        rfl

theorem cell23_1380368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 5, 2].length) (baseStart_1380368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380368 prefixEnd_1380368 := by exact prefixLift 1380368
  have htrace : WordTrace (prefixWord ++ tailWord_1380368) baseStart_1380368 baseEnd_1380368 := by
    simpa [prefixWord, tailWord_1380368, baseEnd_1380368] using wordTrace_append hprefix tailTrace_1380368
  have hstable : (prefixWord ++ tailWord_1380368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380368).length < 2 ^ (prefixWord ++ tailWord_1380368).sum := by decide
  have hdescent : baseEnd_1380368 < baseStart_1380368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380378 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_1380378 : Nat := 118140960795 + 1380378 * 2 ^ 59
def prefixEnd_1380378 : Nat := 4983230072969 + 3 ^ 40 * 1380378 * 2
def baseEnd_1380378 : Nat := 236265799630701832808921

theorem tailTrace_1380378 : CollatzResearch.WordTrace tailWord_1380378 prefixEnd_1380378 236265799630701832808921 := by
  unfold tailWord_1380378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12586630448283432659627447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33564347862089153759006525 12586630448283432659627447)
  ·
    refine ⟨18879945672425148989441171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12586630448283432659627447 18879945672425148989441171)
    ·
      refine ⟨28319918508637723484161757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18879945672425148989441171 28319918508637723484161757)
      ·
        refine ⟨10619969440739146306560659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28319918508637723484161757 10619969440739146306560659)
        ·
          refine ⟨15929954161108719459840989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10619969440739146306560659 15929954161108719459840989)
          ·
            refine ⟨5973732810415769797440371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15929954161108719459840989 5973732810415769797440371)
            ·
              refine ⟨8960599215623654696160557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973732810415769797440371 8960599215623654696160557)
              ·
                refine ⟨3360224705858870511060209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8960599215623654696160557 3360224705858870511060209)
                ·
                  refine ⟨2520168529394152883295157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3360224705858870511060209 2520168529394152883295157)
                  ·
                    refine ⟨236265799630701832808921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2520168529394152883295157 236265799630701832808921)
                    ·
                      rfl

theorem cell23_1380378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_1380378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380378 prefixEnd_1380378 := by exact prefixLift 1380378
  have htrace : WordTrace (prefixWord ++ tailWord_1380378) baseStart_1380378 baseEnd_1380378 := by
    simpa [prefixWord, tailWord_1380378, baseEnd_1380378] using wordTrace_append hprefix tailTrace_1380378
  have hstable : (prefixWord ++ tailWord_1380378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380378).length < 2 ^ (prefixWord ++ tailWord_1380378).sum := by decide
  have hdescent : baseEnd_1380378 < baseStart_1380378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380411 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_1380411 : Nat := 118140960795 + 1380411 * 2 ^ 59
def prefixEnd_1380411 : Nat := 4983230072969 + 3 ^ 40 * 1380411 * 2
def baseEnd_1380411 : Nat := 708814343753703869314111

theorem tailTrace_1380411 : CollatzResearch.WordTrace tailWord_1380411 prefixEnd_1380411 708814343753703869314111 := by
  unfold tailWord_1380411
  simp only [CollatzResearch.WordTrace]
  refine ⟨50347725402014177274461087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33565150268009451516307391 50347725402014177274461087)
  ·
    refine ⟨75521588103021265911691631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50347725402014177274461087 75521588103021265911691631)
    ·
      refine ⟨113282382154531898867537447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75521588103021265911691631 113282382154531898867537447)
      ·
        refine ⟨169923573231797848301306171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113282382154531898867537447 169923573231797848301306171)
        ·
          refine ⟨254885359847696772451959257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169923573231797848301306171 254885359847696772451959257)
          ·
            refine ⟨191164019885772579338969443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254885359847696772451959257 191164019885772579338969443)
            ·
              refine ⟨286746029828658869008454165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191164019885772579338969443 286746029828658869008454165)
              ·
                refine ⟨13441220148218384484771289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 286746029828658869008454165 13441220148218384484771289)
                ·
                  refine ⟨10080915111163788363578467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13441220148218384484771289 10080915111163788363578467)
                  ·
                    refine ⟨15121372666745682545367701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10080915111163788363578467 15121372666745682545367701)
                    ·
                      refine ⟨708814343753703869314111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15121372666745682545367701 708814343753703869314111)
                      ·
                        rfl

theorem cell23_1380411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_1380411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380411 prefixEnd_1380411 := by exact prefixLift 1380411
  have htrace : WordTrace (prefixWord ++ tailWord_1380411) baseStart_1380411 baseEnd_1380411 := by
    simpa [prefixWord, tailWord_1380411, baseEnd_1380411] using wordTrace_append hprefix tailTrace_1380411
  have hstable : (prefixWord ++ tailWord_1380411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380411).length < 2 ^ (prefixWord ++ tailWord_1380411).sum := by decide
  have hdescent : baseEnd_1380411 < baseStart_1380411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380421 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 10]
def baseStart_1380421 : Nat := 118140960795 + 1380421 * 2 ^ 59
def prefixEnd_1380421 : Nat := 4983230072969 + 3 ^ 40 * 1380421 * 2
def baseEnd_1380421 : Nat := 78757719840027647798785

theorem tailTrace_1380421 : CollatzResearch.WordTrace tailWord_1380421 prefixEnd_1380421 78757719840027647798785 := by
  unfold tailWord_1380421
  simp only [CollatzResearch.WordTrace]
  refine ⟨50348090131977948982325117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33565393421318632654883411 50348090131977948982325117)
  ·
    refine ⟨18880533799491730868371919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50348090131977948982325117 18880533799491730868371919)
    ·
      refine ⟨28320800699237596302557879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18880533799491730868371919 28320800699237596302557879)
      ·
        refine ⟨42481201048856394453836819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28320800699237596302557879 42481201048856394453836819)
        ·
          refine ⟨63721801573284591680755229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42481201048856394453836819 63721801573284591680755229)
          ·
            refine ⟨23895675589981721880283211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63721801573284591680755229 23895675589981721880283211)
            ·
              refine ⟨35843513384972582820424817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23895675589981721880283211 35843513384972582820424817)
              ·
                refine ⟨26882635038729437115318613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35843513384972582820424817 26882635038729437115318613)
                ·
                  refine ⟨78757719840027647798785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26882635038729437115318613 78757719840027647798785)
                  ·
                    rfl

theorem cell23_1380421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_1380421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380421 prefixEnd_1380421 := by exact prefixLift 1380421
  have htrace : WordTrace (prefixWord ++ tailWord_1380421) baseStart_1380421 baseEnd_1380421 := by
    simpa [prefixWord, tailWord_1380421, baseEnd_1380421] using wordTrace_append hprefix tailTrace_1380421
  have hstable : (prefixWord ++ tailWord_1380421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380421).length < 2 ^ (prefixWord ++ tailWord_1380421).sum := by decide
  have hdescent : baseEnd_1380421 < baseStart_1380421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380442 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_1380442 : Nat := 118140960795 + 1380442 * 2 ^ 59
def prefixEnd_1380442 : Nat := 4983230072969 + 3 ^ 40 * 1380442 * 2
def baseEnd_1380442 : Nat := 236276753884664416008823

theorem tailTrace_1380442 : CollatzResearch.WordTrace tailWord_1380442 prefixEnd_1380442 236276753884664416008823 := by
  unfold tailWord_1380442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12587214016225467392209895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33565904043267913045893053 12587214016225467392209895)
  ·
    refine ⟨18880821024338201088314843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12587214016225467392209895 18880821024338201088314843)
    ·
      refine ⟨28321231536507301632472265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18880821024338201088314843 28321231536507301632472265)
      ·
        refine ⟨21240923652380476224354199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28321231536507301632472265 21240923652380476224354199)
        ·
          refine ⟨31861385478570714336531299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21240923652380476224354199 31861385478570714336531299)
          ·
            refine ⟨47792078217856071504796949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31861385478570714336531299 47792078217856071504796949)
            ·
              refine ⟨2240253666462003351787357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47792078217856071504796949 2240253666462003351787357)
              ·
                refine ⟨840095124923251256920259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240253666462003351787357 840095124923251256920259)
                ·
                  refine ⟨1260142687384876885380389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840095124923251256920259 1260142687384876885380389)
                  ·
                    refine ⟨236276753884664416008823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260142687384876885380389 236276753884664416008823)
                    ·
                      rfl

theorem cell23_1380442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_1380442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380442 prefixEnd_1380442 := by exact prefixLift 1380442
  have htrace : WordTrace (prefixWord ++ tailWord_1380442) baseStart_1380442 baseEnd_1380442 := by
    simpa [prefixWord, tailWord_1380442, baseEnd_1380442] using wordTrace_append hprefix tailTrace_1380442
  have hstable : (prefixWord ++ tailWord_1380442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380442).length < 2 ^ (prefixWord ++ tailWord_1380442).sum := by decide
  have hdescent : baseEnd_1380442 < baseStart_1380442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380445 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1380445 : Nat := 118140960795 + 1380445 * 2 ^ 59
def prefixEnd_1380445 : Nat := 4983230072969 + 3 ^ 40 * 1380445 * 2
def baseEnd_1380445 : Nat := 708831802095956736288955

theorem tailTrace_1380445 : CollatzResearch.WordTrace tailWord_1380445 prefixEnd_1380445 708831802095956736288955 := by
  unfold tailWord_1380445
  simp only [CollatzResearch.WordTrace]
  refine ⟨50348965483891001081198789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33565976989260667387465859 50348965483891001081198789)
  ·
    refine ⟨9440431028229562702724773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50348965483891001081198789 9440431028229562702724773)
    ·
      refine ⟨1770080817793043006760895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9440431028229562702724773 1770080817793043006760895)
      ·
        refine ⟨2655121226689564510141343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770080817793043006760895 2655121226689564510141343)
        ·
          refine ⟨3982681840034346765212015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655121226689564510141343 3982681840034346765212015)
          ·
            refine ⟨5974022760051520147818023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982681840034346765212015 5974022760051520147818023)
            ·
              refine ⟨8961034140077280221727035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974022760051520147818023 8961034140077280221727035)
              ·
                refine ⟨13441551210115920332590553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8961034140077280221727035 13441551210115920332590553)
                ·
                  refine ⟨10081163407586940249442915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13441551210115920332590553 10081163407586940249442915)
                  ·
                    refine ⟨15121745111380410374164373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10081163407586940249442915 15121745111380410374164373)
                    ·
                      refine ⟨708831802095956736288955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15121745111380410374164373 708831802095956736288955)
                      ·
                        rfl

theorem cell23_1380445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1380445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380445 prefixEnd_1380445 := by exact prefixLift 1380445
  have htrace : WordTrace (prefixWord ++ tailWord_1380445) baseStart_1380445 baseEnd_1380445 := by
    simpa [prefixWord, tailWord_1380445, baseEnd_1380445] using wordTrace_append hprefix tailTrace_1380445
  have hstable : (prefixWord ++ tailWord_1380445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380445).length < 2 ^ (prefixWord ++ tailWord_1380445).sum := by decide
  have hdescent : baseEnd_1380445 < baseStart_1380445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380485 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_1380485 : Nat := 118140960795 + 1380485 * 2 ^ 59
def prefixEnd_1380485 : Nat := 4983230072969 + 3 ^ 40 * 1380485 * 2
def baseEnd_1380485 : Nat := 236284113774045526596257

theorem tailTrace_1380485 : CollatzResearch.WordTrace tailWord_1380485 prefixEnd_1380485 236284113774045526596257 := by
  unfold tailWord_1380485
  simp only [CollatzResearch.WordTrace]
  refine ⟨50350424403746087912654909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33566949602497391941769939 50350424403746087912654909)
  ·
    refine ⟨18881409151404782967245591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50350424403746087912654909 18881409151404782967245591)
    ·
      refine ⟨28322113727107174450868387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18881409151404782967245591 28322113727107174450868387)
      ·
        refine ⟨42483170590660761676302581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28322113727107174450868387 42483170590660761676302581)
        ·
          refine ⟨3982797242874446407153367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42483170590660761676302581 3982797242874446407153367)
          ·
            refine ⟨5974195864311669610730051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982797242874446407153367 5974195864311669610730051)
            ·
              refine ⟨8961293796467504416095077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974195864311669610730051 8961293796467504416095077)
              ·
                refine ⟨1680242586837657078017827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8961293796467504416095077 1680242586837657078017827)
                ·
                  refine ⟨2520363880256485617026741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680242586837657078017827 2520363880256485617026741)
                  ·
                    refine ⟨236284113774045526596257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2520363880256485617026741 236284113774045526596257)
                    ·
                      rfl

theorem cell23_1380485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_1380485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380485 prefixEnd_1380485 := by exact prefixLift 1380485
  have htrace : WordTrace (prefixWord ++ tailWord_1380485) baseStart_1380485 baseEnd_1380485 := by
    simpa [prefixWord, tailWord_1380485, baseEnd_1380485] using wordTrace_append hprefix tailTrace_1380485
  have hstable : (prefixWord ++ tailWord_1380485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380485).length < 2 ^ (prefixWord ++ tailWord_1380485).sum := by decide
  have hdescent : baseEnd_1380485 < baseStart_1380485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380516 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_1380516 : Nat := 118140960795 + 1380516 * 2 ^ 59
def prefixEnd_1380516 : Nat := 4983230072969 + 3 ^ 40 * 1380516 * 2
def baseEnd_1380516 : Nat := 708868259222425958501129

theorem tailTrace_1380516 : CollatzResearch.WordTrace tailWord_1380516 prefixEnd_1380516 708868259222425958501129 := by
  unfold tailWord_1380516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25175777533316890103516701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33567703377755853471355601 25175777533316890103516701)
  ·
    refine ⟨9440916574993833788818763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25175777533316890103516701 9440916574993833788818763)
    ·
      refine ⟨14161374862490750683228145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9440916574993833788818763 14161374862490750683228145)
      ·
        refine ⟨10621031146868063012421109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14161374862490750683228145 10621031146868063012421109)
        ·
          refine ⟨995721670018880907414479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10621031146868063012421109 995721670018880907414479)
          ·
            refine ⟨1493582505028321361121719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995721670018880907414479 1493582505028321361121719)
            ·
              refine ⟨2240373757542482041682579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493582505028321361121719 2240373757542482041682579)
              ·
                refine ⟨3360560636313723062523869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240373757542482041682579 3360560636313723062523869)
                ·
                  refine ⟨1260210238617646148446451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3360560636313723062523869 1260210238617646148446451)
                  ·
                    refine ⟨1890315357926469222669677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1260210238617646148446451 1890315357926469222669677)
                    ·
                      refine ⟨708868259222425958501129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1890315357926469222669677 708868259222425958501129)
                      ·
                        rfl

theorem cell23_1380516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_1380516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380516 prefixEnd_1380516 := by exact prefixLift 1380516
  have htrace : WordTrace (prefixWord ++ tailWord_1380516) baseStart_1380516 baseEnd_1380516 := by
    simpa [prefixWord, tailWord_1380516, baseEnd_1380516] using wordTrace_append hprefix tailTrace_1380516
  have hstable : (prefixWord ++ tailWord_1380516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380516).length < 2 ^ (prefixWord ++ tailWord_1380516).sum := by decide
  have hdescent : baseEnd_1380516 < baseStart_1380516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380555 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 3]
def baseStart_1380555 : Nat := 118140960795 + 1380555 * 2 ^ 59
def prefixEnd_1380555 : Nat := 4983230072969 + 3 ^ 40 * 1380555 * 2
def baseEnd_1380555 : Nat := 708888284967951305913449

theorem tailTrace_1380555 : CollatzResearch.WordTrace tailWord_1380555 prefixEnd_1380555 708888284967951305913449 := by
  unfold tailWord_1380555
  simp only [CollatzResearch.WordTrace]
  refine ⟨50352977513492489867703119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33568651675661659911802079 50352977513492489867703119)
  ·
    refine ⟨75529466270238734801554679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50352977513492489867703119 75529466270238734801554679)
    ·
      refine ⟨113294199405358102202332019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75529466270238734801554679 113294199405358102202332019)
      ·
        refine ⟨169941299108037153303498029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113294199405358102202332019 169941299108037153303498029)
        ·
          refine ⟨63727987165513932488811761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169941299108037153303498029 63727987165513932488811761)
          ·
            refine ⟨47795990374135449366608821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63727987165513932488811761 47795990374135449366608821)
            ·
              refine ⟨4480874097575198378119577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47795990374135449366608821 4480874097575198378119577)
              ·
                refine ⟨3360655573181398783589683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4480874097575198378119577 3360655573181398783589683)
                ·
                  refine ⟨5040983359772098175384525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360655573181398783589683 5040983359772098175384525)
                  ·
                    refine ⟨1890368759914536815769197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5040983359772098175384525 1890368759914536815769197)
                    ·
                      refine ⟨708888284967951305913449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1890368759914536815769197 708888284967951305913449)
                      ·
                        rfl

theorem cell23_1380555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 3].length) (baseStart_1380555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380555 prefixEnd_1380555 := by exact prefixLift 1380555
  have htrace : WordTrace (prefixWord ++ tailWord_1380555) baseStart_1380555 baseEnd_1380555 := by
    simpa [prefixWord, tailWord_1380555, baseEnd_1380555] using wordTrace_append hprefix tailTrace_1380555
  have hstable : (prefixWord ++ tailWord_1380555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380555).length < 2 ^ (prefixWord ++ tailWord_1380555).sum := by decide
  have hdescent : baseEnd_1380555 < baseStart_1380555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380556 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1380556 : Nat := 118140960795 + 1380556 * 2 ^ 59
def prefixEnd_1380556 : Nat := 4983230072969 + 3 ^ 40 * 1380556 * 2
def baseEnd_1380556 : Nat := 708888798448605802000945

theorem tailTrace_1380556 : CollatzResearch.WordTrace tailWord_1380556 prefixEnd_1380556 708888798448605802000945 := by
  unfold tailWord_1380556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25176506993244433519244761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33568675990992578025659681 25176506993244433519244761)
  ·
    refine ⟨18882380244933325139433571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25176506993244433519244761 18882380244933325139433571)
    ·
      refine ⟨28323570367399987709150357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18882380244933325139433571 28323570367399987709150357)
      ·
        refine ⟨1327667360971874423866423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28323570367399987709150357 1327667360971874423866423)
        ·
          refine ⟨1991501041457811635799635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327667360971874423866423 1991501041457811635799635)
          ·
            refine ⟨2987251562186717453699453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991501041457811635799635 2987251562186717453699453)
            ·
              refine ⟨1120219335820019045137295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2987251562186717453699453 1120219335820019045137295)
              ·
                refine ⟨1680329003730028567705943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120219335820019045137295 1680329003730028567705943)
                ·
                  refine ⟨2520493505595042851558915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680329003730028567705943 2520493505595042851558915)
                  ·
                    refine ⟨3780740258392564277338373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2520493505595042851558915 3780740258392564277338373)
                    ·
                      refine ⟨708888798448605802000945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3780740258392564277338373 708888798448605802000945)
                      ·
                        rfl

theorem cell23_1380556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1380556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380556 prefixEnd_1380556 := by exact prefixLift 1380556
  have htrace : WordTrace (prefixWord ++ tailWord_1380556) baseStart_1380556 baseEnd_1380556 := by
    simpa [prefixWord, tailWord_1380556, baseEnd_1380556] using wordTrace_append hprefix tailTrace_1380556
  have hstable : (prefixWord ++ tailWord_1380556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380556).length < 2 ^ (prefixWord ++ tailWord_1380556).sum := by decide
  have hdescent : baseEnd_1380556 < baseStart_1380556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380566 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1380566 : Nat := 118140960795 + 1380566 * 2 ^ 59
def prefixEnd_1380566 : Nat := 4983230072969 + 3 ^ 40 * 1380566 * 2
def baseEnd_1380566 : Nat := 236297977751716920958633

theorem tailTrace_1380566 : CollatzResearch.WordTrace tailWord_1380566 prefixEnd_1380566 236297977751716920958633 := by
  unfold tailWord_1380566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147086169778289921647097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33568919144301759164235701 3147086169778289921647097)
  ·
    refine ⟨2360314627333717441235323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3147086169778289921647097 2360314627333717441235323)
    ·
      refine ⟨3540471941000576161852985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360314627333717441235323 3540471941000576161852985)
      ·
        refine ⟨2655353955750432121389739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540471941000576161852985 2655353955750432121389739)
        ·
          refine ⟨3983030933625648182084609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655353955750432121389739 3983030933625648182084609)
          ·
            refine ⟨2987273200219236136563457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3983030933625648182084609 2987273200219236136563457)
            ·
              refine ⟨2240454900164427102422593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987273200219236136563457 2240454900164427102422593)
              ·
                refine ⟨1680341175123320326816945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2240454900164427102422593 1680341175123320326816945)
                ·
                  refine ⟨1260255881342490245112709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680341175123320326816945 1260255881342490245112709)
                  ·
                    refine ⟨236297977751716920958633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260255881342490245112709 236297977751716920958633)
                    ·
                      rfl

theorem cell23_1380566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1380566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380566 prefixEnd_1380566 := by exact prefixLift 1380566
  have htrace : WordTrace (prefixWord ++ tailWord_1380566) baseStart_1380566 baseEnd_1380566 := by
    simpa [prefixWord, tailWord_1380566, baseEnd_1380566] using wordTrace_append hprefix tailTrace_1380566
  have hstable : (prefixWord ++ tailWord_1380566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380566).length < 2 ^ (prefixWord ++ tailWord_1380566).sum := by decide
  have hdescent : baseEnd_1380566 < baseStart_1380566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380573 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1380573 : Nat := 118140960795 + 1380573 * 2 ^ 59
def prefixEnd_1380573 : Nat := 4983230072969 + 3 ^ 40 * 1380573 * 2
def baseEnd_1380573 : Nat := 708897527619732235488367

theorem tailTrace_1380573 : CollatzResearch.WordTrace tailWord_1380573 prefixEnd_1380573 708897527619732235488367 := by
  unfold tailWord_1380573
  simp only [CollatzResearch.WordTrace]
  refine ⟨50353634027427278941858373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33569089351618185961238915 50353634027427278941858373)
  ·
    refine ⟨9441306380142614801598445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50353634027427278941858373 9441306380142614801598445)
    ·
      refine ⟨3540489892553480550599417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9441306380142614801598445 3540489892553480550599417)
      ·
        refine ⟨2655367419415110412949563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540489892553480550599417 2655367419415110412949563)
        ·
          refine ⟨3983051129122665619424345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655367419415110412949563 3983051129122665619424345)
          ·
            refine ⟨2987288346841999214568259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3983051129122665619424345 2987288346841999214568259)
            ·
              refine ⟨4480932520262998821852389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987288346841999214568259 4480932520262998821852389)
              ·
                refine ⟨840174847549312279097323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4480932520262998821852389 840174847549312279097323)
                ·
                  refine ⟨1260262271323968418645985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840174847549312279097323 1260262271323968418645985)
                  ·
                    refine ⟨945196703492976313984489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260262271323968418645985 945196703492976313984489)
                    ·
                      refine ⟨708897527619732235488367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945196703492976313984489 708897527619732235488367)
                      ·
                        rfl

theorem cell23_1380573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1380573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380573 prefixEnd_1380573 := by exact prefixLift 1380573
  have htrace : WordTrace (prefixWord ++ tailWord_1380573) baseStart_1380573 baseEnd_1380573 := by
    simpa [prefixWord, tailWord_1380573, baseEnd_1380573] using wordTrace_append hprefix tailTrace_1380573
  have hstable : (prefixWord ++ tailWord_1380573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380573).length < 2 ^ (prefixWord ++ tailWord_1380573).sum := by decide
  have hdescent : baseEnd_1380573 < baseStart_1380573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380579 : List Nat := [1, 1, 1, 8, 2, 1, 1, 8]
def baseStart_1380579 : Nat := 118140960795 + 1380579 * 2 ^ 59
def prefixEnd_1380579 : Nat := 4983230072969 + 3 ^ 40 * 1380579 * 2
def baseEnd_1380579 : Nat := 26255578092728118963457

theorem tailTrace_1380579 : CollatzResearch.WordTrace tailWord_1380579 prefixEnd_1380579 26255578092728118963457 := by
  unfold tailWord_1380579
  simp only [CollatzResearch.WordTrace]
  refine ⟨50353852865405541966576791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33569235243603694644384527 50353852865405541966576791)
  ·
    refine ⟨75530779298108312949865187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50353852865405541966576791 75530779298108312949865187)
    ·
      refine ⟨113296168947162469424797781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75530779298108312949865187 113296168947162469424797781)
      ·
        refine ⟨1327689479849560188571849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 113296168947162469424797781 1327689479849560188571849)
        ·
          refine ⟨995767109887170141428887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327689479849560188571849 995767109887170141428887)
          ·
            refine ⟨1493650664830755212143331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995767109887170141428887 1493650664830755212143331)
            ·
              refine ⟨2240475997246132818214997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493650664830755212143331 2240475997246132818214997)
              ·
                refine ⟨26255578092728118963457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2240475997246132818214997 26255578092728118963457)
                ·
                  rfl

theorem cell23_1380579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 8].length) (baseStart_1380579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380579 prefixEnd_1380579 := by exact prefixLift 1380579
  have htrace : WordTrace (prefixWord ++ tailWord_1380579) baseStart_1380579 baseEnd_1380579 := by
    simpa [prefixWord, tailWord_1380579, baseEnd_1380579] using wordTrace_append hprefix tailTrace_1380579
  have hstable : (prefixWord ++ tailWord_1380579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380579).length < 2 ^ (prefixWord ++ tailWord_1380579).sum := by decide
  have hdescent : baseEnd_1380579 < baseStart_1380579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380589 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1380589 : Nat := 118140960795 + 1380589 * 2 ^ 59
def prefixEnd_1380589 : Nat := 4983230072969 + 3 ^ 40 * 1380589 * 2
def baseEnd_1380589 : Nat := 708905743310204172888293

theorem tailTrace_1380589 : CollatzResearch.WordTrace tailWord_1380589 prefixEnd_1380589 708905743310204172888293 := by
  unfold tailWord_1380589
  simp only [CollatzResearch.WordTrace]
  refine ⟨50354217595369313674440821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33569478396912875782960547 50354217595369313674440821)
  ·
    refine ⟨4720707899565873156978827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50354217595369313674440821 4720707899565873156978827)
    ·
      refine ⟨7081061849348809735468241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4720707899565873156978827 7081061849348809735468241)
      ·
        refine ⟨5310796387011607301601181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7081061849348809735468241 5310796387011607301601181)
        ·
          refine ⟨1991548645129352738100443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5310796387011607301601181 1991548645129352738100443)
          ·
            refine ⟨2987322967694029107150665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991548645129352738100443 2987322967694029107150665)
            ·
              refine ⟨2240492225770521830362999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987322967694029107150665 2240492225770521830362999)
              ·
                refine ⟨3360738338655782745544499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240492225770521830362999 3360738338655782745544499)
                ·
                  refine ⟨5041107507983674118316749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360738338655782745544499 5041107507983674118316749)
                  ·
                    refine ⟨1890415315493877794368781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5041107507983674118316749 1890415315493877794368781)
                    ·
                      refine ⟨708905743310204172888293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1890415315493877794368781 708905743310204172888293)
                      ·
                        rfl

theorem cell23_1380589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1380589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380589 prefixEnd_1380589 := by exact prefixLift 1380589
  have htrace : WordTrace (prefixWord ++ tailWord_1380589) baseStart_1380589 baseEnd_1380589 := by
    simpa [prefixWord, tailWord_1380589, baseEnd_1380589] using wordTrace_append hprefix tailTrace_1380589
  have hstable : (prefixWord ++ tailWord_1380589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380589).length < 2 ^ (prefixWord ++ tailWord_1380589).sum := by decide
  have hdescent : baseEnd_1380589 < baseStart_1380589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380616 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_1380616 : Nat := 118140960795 + 1380616 * 2 ^ 59
def prefixEnd_1380616 : Nat := 4983230072969 + 3 ^ 40 * 1380616 * 2
def baseEnd_1380616 : Nat := 708919607287875567250669

theorem tailTrace_1380616 : CollatzResearch.WordTrace tailWord_1380616 prefixEnd_1380616 708919607287875567250669 := by
  unfold tailWord_1380616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25177601183135748642836851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33570134910847664857115801 25177601183135748642836851)
  ·
    refine ⟨37766401774703622964255277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25177601183135748642836851 37766401774703622964255277)
    ·
      refine ⟨14162400665513858611595729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37766401774703622964255277 14162400665513858611595729)
      ·
        refine ⟨10621800499135393958696797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14162400665513858611595729 10621800499135393958696797)
        ·
          refine ⟨3983175187175772734511299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10621800499135393958696797 3983175187175772734511299)
          ·
            refine ⟨5974762780763659101766949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983175187175772734511299 5974762780763659101766949)
            ·
              refine ⟨1120268021393186081581303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5974762780763659101766949 1120268021393186081581303)
              ·
                refine ⟨1680402032089779122371955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120268021393186081581303 1680402032089779122371955)
                ·
                  refine ⟨2520603048134668683557933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680402032089779122371955 2520603048134668683557933)
                  ·
                    refine ⟨945226143050500756334225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520603048134668683557933 945226143050500756334225)
                    ·
                      refine ⟨708919607287875567250669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945226143050500756334225 708919607287875567250669)
                      ·
                        rfl

theorem cell23_1380616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_1380616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380616 prefixEnd_1380616 := by exact prefixLift 1380616
  have htrace : WordTrace (prefixWord ++ tailWord_1380616) baseStart_1380616 baseEnd_1380616 := by
    simpa [prefixWord, tailWord_1380616, baseEnd_1380616] using wordTrace_append hprefix tailTrace_1380616
  have hstable : (prefixWord ++ tailWord_1380616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380616).length < 2 ^ (prefixWord ++ tailWord_1380616).sum := by decide
  have hdescent : baseEnd_1380616 < baseStart_1380616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380625 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_1380625 : Nat := 118140960795 + 1380625 * 2 ^ 59
def prefixEnd_1380625 : Nat := 4983230072969 + 3 ^ 40 * 1380625 * 2
def baseEnd_1380625 : Nat := 708924228613766032038127

theorem tailTrace_1380625 : CollatzResearch.WordTrace tailWord_1380625 prefixEnd_1380625 708924228613766032038127 := by
  unfold tailWord_1380625
  simp only [CollatzResearch.WordTrace]
  refine ⟨50355530623238891822751329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33570353748825927881834219 50355530623238891822751329)
  ·
    refine ⟨37766647967429168867063497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50355530623238891822751329 37766647967429168867063497)
    ·
      refine ⟨28324985975571876650297623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37766647967429168867063497 28324985975571876650297623)
      ·
        refine ⟨42487478963357814975446435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28324985975571876650297623 42487478963357814975446435)
        ·
          refine ⟨63731218445036722463169653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42487478963357814975446435 63731218445036722463169653)
          ·
            refine ⟨5974801729222192730922155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63731218445036722463169653 5974801729222192730922155)
            ·
              refine ⟨8962202593833289096383233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974801729222192730922155 8962202593833289096383233)
              ·
                refine ⟨6721651945374966822287425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962202593833289096383233 6721651945374966822287425)
                ·
                  refine ⟨5041238959031225116715569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721651945374966822287425 5041238959031225116715569)
                  ·
                    refine ⟨3780929219273418837536677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041238959031225116715569 3780929219273418837536677)
                    ·
                      refine ⟨708924228613766032038127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3780929219273418837536677 708924228613766032038127)
                      ·
                        rfl

theorem cell23_1380625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_1380625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380625 prefixEnd_1380625 := by exact prefixLift 1380625
  have htrace : WordTrace (prefixWord ++ tailWord_1380625) baseStart_1380625 baseEnd_1380625 := by
    simpa [prefixWord, tailWord_1380625, baseEnd_1380625] using wordTrace_append hprefix tailTrace_1380625
  have hstable : (prefixWord ++ tailWord_1380625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380625).length < 2 ^ (prefixWord ++ tailWord_1380625).sum := by decide
  have hdescent : baseEnd_1380625 < baseStart_1380625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380642 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1380642 : Nat := 118140960795 + 1380642 * 2 ^ 59
def prefixEnd_1380642 : Nat := 4983230072969 + 3 ^ 40 * 1380642 * 2
def baseEnd_1380642 : Nat := 708932957784892465525549

theorem tailTrace_1380642 : CollatzResearch.WordTrace tailWord_1380642 prefixEnd_1380642 708932957784892465525549 := by
  unfold tailWord_1380642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589037666044325931530045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33570767109451535817413453 12589037666044325931530045)
  ·
    refine ⟨4720889124766622224323767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12589037666044325931530045 4720889124766622224323767)
    ·
      refine ⟨7081333687149933336485651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4720889124766622224323767 7081333687149933336485651)
      ·
        refine ⟨10622000530724900004728477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081333687149933336485651 10622000530724900004728477)
        ·
          refine ⟨3983250199021837501773179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10622000530724900004728477 3983250199021837501773179)
          ·
            refine ⟨5974875298532756252659769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983250199021837501773179 5974875298532756252659769)
            ·
              refine ⟨4481156473899567189494827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5974875298532756252659769 4481156473899567189494827)
              ·
                refine ⟨6721734710849350784242241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481156473899567189494827 6721734710849350784242241)
                ·
                  refine ⟨5041301033137013088181681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721734710849350784242241 5041301033137013088181681)
                  ·
                    refine ⟨3780975774852759816136261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041301033137013088181681 3780975774852759816136261)
                    ·
                      refine ⟨708932957784892465525549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3780975774852759816136261 708932957784892465525549)
                      ·
                        rfl

theorem cell23_1380642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1380642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380642 prefixEnd_1380642 := by exact prefixLift 1380642
  have htrace : WordTrace (prefixWord ++ tailWord_1380642) baseStart_1380642 baseEnd_1380642 := by
    simpa [prefixWord, tailWord_1380642, baseEnd_1380642] using wordTrace_append hprefix tailTrace_1380642
  have hstable : (prefixWord ++ tailWord_1380642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380642).length < 2 ^ (prefixWord ++ tailWord_1380642).sum := by decide
  have hdescent : baseEnd_1380642 < baseStart_1380642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380692 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1380692 : Nat := 118140960795 + 1380692 * 2 ^ 59
def prefixEnd_1380692 : Nat := 4983230072969 + 3 ^ 40 * 1380692 * 2
def baseEnd_1380692 : Nat := 708958631817617269900319

theorem tailTrace_1380692 : CollatzResearch.WordTrace tailWord_1380692 prefixEnd_1380692 708958631817617269900319 := by
  unfold tailWord_1380692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178987156998081132720165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33571982875997441510293553 25178987156998081132720165)
  ·
    refine ⟨4721060091937140212385031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25178987156998081132720165 4721060091937140212385031)
    ·
      refine ⟨7081590137905710318577547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721060091937140212385031 7081590137905710318577547)
      ·
        refine ⟨10622385206858565477866321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081590137905710318577547 10622385206858565477866321)
        ·
          refine ⟨7966788905143924108399741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10622385206858565477866321 7966788905143924108399741)
          ·
            refine ⟨2987545839428971540649903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7966788905143924108399741 2987545839428971540649903)
            ·
              refine ⟨4481318759143457310974855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987545839428971540649903 4481318759143457310974855)
              ·
                refine ⟨6721978138715185966462283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481318759143457310974855 6721978138715185966462283)
                ·
                  refine ⟨10082967208072778949693425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6721978138715185966462283 10082967208072778949693425)
                  ·
                    refine ⟨7562225406054584212270069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10082967208072778949693425 7562225406054584212270069)
                    ·
                      refine ⟨708958631817617269900319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7562225406054584212270069 708958631817617269900319)
                      ·
                        rfl

theorem cell23_1380692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1380692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380692 prefixEnd_1380692 := by exact prefixLift 1380692
  have htrace : WordTrace (prefixWord ++ tailWord_1380692) baseStart_1380692 baseEnd_1380692 := by
    simpa [prefixWord, tailWord_1380692, baseEnd_1380692] using wordTrace_append hprefix tailTrace_1380692
  have hstable : (prefixWord ++ tailWord_1380692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380692).length < 2 ^ (prefixWord ++ tailWord_1380692).sum := by decide
  have hdescent : baseEnd_1380692 < baseStart_1380692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380729 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 1, 4]
def baseStart_1380729 : Nat := 118140960795 + 1380729 * 2 ^ 59
def prefixEnd_1380729 : Nat := 4983230072969 + 3 ^ 40 * 1380729 * 2
def baseEnd_1380729 : Nat := 236325876867277875045883

theorem tailTrace_1380729 : CollatzResearch.WordTrace tailWord_1380729 prefixEnd_1380729 236325876867277875045883 := by
  unfold tailWord_1380729
  simp only [CollatzResearch.WordTrace]
  refine ⟨50359323814862117584537241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33572882543241411723024827 50359323814862117584537241)
  ·
    refine ⟨37769492861146588188402931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50359323814862117584537241 37769492861146588188402931)
    ·
      refine ⟨56654239291719882282604397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37769492861146588188402931 56654239291719882282604397)
      ·
        refine ⟨21245339734394955855976649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56654239291719882282604397 21245339734394955855976649)
        ·
          refine ⟨15934004800796216891982487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21245339734394955855976649 15934004800796216891982487)
          ·
            refine ⟨23901007201194325337973731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15934004800796216891982487 23901007201194325337973731)
            ·
              refine ⟨35851510801791488006960597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23901007201194325337973731 35851510801791488006960597)
              ·
                refine ⟨840269784416988000163139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35851510801791488006960597 840269784416988000163139)
                ·
                  refine ⟨1260404676625482000244709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840269784416988000163139 1260404676625482000244709)
                  ·
                    refine ⟨236325876867277875045883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260404676625482000244709 236325876867277875045883)
                    ·
                      rfl

theorem cell23_1380729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 4].length) (baseStart_1380729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380729 prefixEnd_1380729 := by exact prefixLift 1380729
  have htrace : WordTrace (prefixWord ++ tailWord_1380729) baseStart_1380729 baseEnd_1380729 := by
    simpa [prefixWord, tailWord_1380729, baseEnd_1380729] using wordTrace_append hprefix tailTrace_1380729
  have hstable : (prefixWord ++ tailWord_1380729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380729).length < 2 ^ (prefixWord ++ tailWord_1380729).sum := by decide
  have hdescent : baseEnd_1380729 < baseStart_1380729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380772 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_1380772 : Nat := 118140960795 + 1380772 * 2 ^ 59
def prefixEnd_1380772 : Nat := 4983230072969 + 3 ^ 40 * 1380772 * 2
def baseEnd_1380772 : Nat := 236333236756658985633317

theorem tailTrace_1380772 : CollatzResearch.WordTrace tailWord_1380772 prefixEnd_1380772 236333236756658985633317 := by
  unfold tailWord_1380772
  simp only [CollatzResearch.WordTrace]
  refine ⟨25180446076853167964176285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33573928102470890618901713 25180446076853167964176285)
  ·
    refine ⟨9442667278819937986566107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25180446076853167964176285 9442667278819937986566107)
    ·
      refine ⟨14164000918229906979849161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9442667278819937986566107 14164000918229906979849161)
      ·
        refine ⟨10623000688672430234886871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14164000918229906979849161 10623000688672430234886871)
        ·
          refine ⟨15934501033008645352330307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10623000688672430234886871 15934501033008645352330307)
          ·
            refine ⟨23901751549512968028495461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15934501033008645352330307 23901751549512968028495461)
            ·
              refine ⟨4481578415533681505342899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23901751549512968028495461 4481578415533681505342899)
              ·
                refine ⟨6722367623300522258014349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481578415533681505342899 6722367623300522258014349)
                ·
                  refine ⟨2520887858737695846755381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6722367623300522258014349 2520887858737695846755381)
                  ·
                    refine ⟨236333236756658985633317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2520887858737695846755381 236333236756658985633317)
                    ·
                      rfl

theorem cell23_1380772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_1380772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380772 prefixEnd_1380772 := by exact prefixLift 1380772
  have htrace : WordTrace (prefixWord ++ tailWord_1380772) baseStart_1380772 baseEnd_1380772 := by
    simpa [prefixWord, tailWord_1380772, baseEnd_1380772] using wordTrace_append hprefix tailTrace_1380772
  have hstable : (prefixWord ++ tailWord_1380772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380772).length < 2 ^ (prefixWord ++ tailWord_1380772).sum := by decide
  have hdescent : baseEnd_1380772 < baseStart_1380772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380815 : List Nat := [1, 1, 2, 1, 1, 4, 1, 12]
def baseStart_1380815 : Nat := 118140960795 + 1380815 * 2 ^ 59
def prefixEnd_1380815 : Nat := 4983230072969 + 3 ^ 40 * 1380815 * 2
def baseEnd_1380815 : Nat := 26260066294004455135639

theorem tailTrace_1380815 : CollatzResearch.WordTrace tailWord_1380815 prefixEnd_1380815 26260066294004455135639 := by
  unfold tailWord_1380815
  simp only [CollatzResearch.WordTrace]
  refine ⟨50362460492550554272167899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33574973661700369514778599 50362460492550554272167899)
  ·
    refine ⟨75543690738825831408251849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50362460492550554272167899 75543690738825831408251849)
    ·
      refine ⟨56657768054119373556188887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75543690738825831408251849 56657768054119373556188887)
      ·
        refine ⟨84986652081179060334283331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56657768054119373556188887 84986652081179060334283331)
        ·
          refine ⟨127479978121768590501424997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84986652081179060334283331 127479978121768590501424997)
          ·
            refine ⟨23902495897831610719017187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127479978121768590501424997 23902495897831610719017187)
            ·
              refine ⟨35853743846747416078525781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23902495897831610719017187 35853743846747416078525781)
              ·
                refine ⟨26260066294004455135639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 35853743846747416078525781 26260066294004455135639)
                ·
                  rfl

theorem cell23_1380815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 12].length) (baseStart_1380815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380815 prefixEnd_1380815 := by exact prefixLift 1380815
  have htrace : WordTrace (prefixWord ++ tailWord_1380815) baseStart_1380815 baseEnd_1380815 := by
    simpa [prefixWord, tailWord_1380815, baseEnd_1380815] using wordTrace_append hprefix tailTrace_1380815
  have hstable : (prefixWord ++ tailWord_1380815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380815).length < 2 ^ (prefixWord ++ tailWord_1380815).sum := by decide
  have hdescent : baseEnd_1380815 < baseStart_1380815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380826 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2]
def baseStart_1380826 : Nat := 118140960795 + 1380826 * 2 ^ 59
def prefixEnd_1380826 : Nat := 4983230072969 + 3 ^ 40 * 1380826 * 2
def baseEnd_1380826 : Nat := 709027438225319745624703

theorem tailTrace_1380826 : CollatzResearch.WordTrace tailWord_1380826 prefixEnd_1380826 709027438225319745624703 := by
  unfold tailWord_1380826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12590715423877675787704583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33575241130340468767212221 12590715423877675787704583)
  ·
    refine ⟨18886073135816513681556875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12590715423877675787704583 18886073135816513681556875)
    ·
      refine ⟨28329109703724770522335313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18886073135816513681556875 28329109703724770522335313)
      ·
        refine ⟨21246832277793577891751485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28329109703724770522335313 21246832277793577891751485)
        ·
          refine ⟨7967562104172591709406807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21246832277793577891751485 7967562104172591709406807)
          ·
            refine ⟨11951343156258887564110211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7967562104172591709406807 11951343156258887564110211)
            ·
              refine ⟨17927014734388331346165317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11951343156258887564110211 17927014734388331346165317)
              ·
                refine ⟨3361315262697812127405997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17927014734388331346165317 3361315262697812127405997)
                ·
                  refine ⟨1260493223511679547777249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3361315262697812127405997 1260493223511679547777249)
                  ·
                    refine ⟨945369917633759660832937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260493223511679547777249 945369917633759660832937)
                    ·
                      refine ⟨709027438225319745624703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945369917633759660832937 709027438225319745624703)
                      ·
                        rfl

theorem cell23_1380826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_1380826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380826 prefixEnd_1380826 := by exact prefixLift 1380826
  have htrace : WordTrace (prefixWord ++ tailWord_1380826) baseStart_1380826 baseEnd_1380826 := by
    simpa [prefixWord, tailWord_1380826, baseEnd_1380826] using wordTrace_append hprefix tailTrace_1380826
  have hstable : (prefixWord ++ tailWord_1380826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380826).length < 2 ^ (prefixWord ++ tailWord_1380826).sum := by decide
  have hdescent : baseEnd_1380826 < baseStart_1380826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380837 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1380837 : Nat := 118140960795 + 1380837 * 2 ^ 59
def prefixEnd_1380837 : Nat := 4983230072969 + 3 ^ 40 * 1380837 * 2
def baseEnd_1380837 : Nat := 709033086512519202587153

theorem tailTrace_1380837 : CollatzResearch.WordTrace tailWord_1380837 prefixEnd_1380837 709033086512519202587153 := by
  unfold tailWord_1380837
  simp only [CollatzResearch.WordTrace]
  refine ⟨50363262898470852029468765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33575508598980568019645843 50363262898470852029468765)
  ·
    refine ⟨18886223586926569511050787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50363262898470852029468765 18886223586926569511050787)
    ·
      refine ⟨28329335380389854266576181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18886223586926569511050787 28329335380389854266576181)
      ·
        refine ⟨2655875191911548837491517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28329335380389854266576181 2655875191911548837491517)
        ·
          refine ⟨995953196966830814059319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2655875191911548837491517 995953196966830814059319)
          ·
            refine ⟨1493929795450246221088979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995953196966830814059319 1493929795450246221088979)
            ·
              refine ⟨2240894693175369331633469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493929795450246221088979 2240894693175369331633469)
              ·
                refine ⟨840335509940763499362551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240894693175369331633469 840335509940763499362551)
                ·
                  refine ⟨1260503264911145249043827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840335509940763499362551 1260503264911145249043827)
                  ·
                    refine ⟨1890754897366717873565741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1260503264911145249043827 1890754897366717873565741)
                    ·
                      refine ⟨709033086512519202587153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1890754897366717873565741 709033086512519202587153)
                      ·
                        rfl

theorem cell23_1380837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1380837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380837 prefixEnd_1380837 := by exact prefixLift 1380837
  have htrace : WordTrace (prefixWord ++ tailWord_1380837) baseStart_1380837 baseEnd_1380837 := by
    simpa [prefixWord, tailWord_1380837, baseEnd_1380837] using wordTrace_append hprefix tailTrace_1380837
  have hstable : (prefixWord ++ tailWord_1380837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380837).length < 2 ^ (prefixWord ++ tailWord_1380837).sum := by decide
  have hdescent : baseEnd_1380837 < baseStart_1380837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380846 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1380846 : Nat := 118140960795 + 1380846 * 2 ^ 59
def prefixEnd_1380846 : Nat := 4983230072969 + 3 ^ 40 * 1380846 * 2
def baseEnd_1380846 : Nat := 709037707838409667374611

theorem tailTrace_1380846 : CollatzResearch.WordTrace tailWord_1380846 prefixEnd_1380846 709037707838409667374611 := by
  unfold tailWord_1380846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295448894429780820818299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33575727436958831044364261 6295448894429780820818299)
  ·
    refine ⟨9443173341644671231227449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6295448894429780820818299 9443173341644671231227449)
    ·
      refine ⟨7082380006233503423420587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9443173341644671231227449 7082380006233503423420587)
      ·
        refine ⟨10623570009350255135130881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7082380006233503423420587 10623570009350255135130881)
        ·
          refine ⟨7967677507012691351348161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10623570009350255135130881 7967677507012691351348161)
          ·
            refine ⟨5975758130259518513511121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7967677507012691351348161 5975758130259518513511121)
            ·
              refine ⟨4481818597694638885133341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975758130259518513511121 4481818597694638885133341)
              ·
                refine ⟨1680681974135489581925003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4481818597694638885133341 1680681974135489581925003)
                ·
                  refine ⟨2521022961203234372887505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680681974135489581925003 2521022961203234372887505)
                  ·
                    refine ⟨1890767220902425779665629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2521022961203234372887505 1890767220902425779665629)
                    ·
                      refine ⟨709037707838409667374611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1890767220902425779665629 709037707838409667374611)
                      ·
                        rfl

theorem cell23_1380846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1380846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380846 prefixEnd_1380846 := by exact prefixLift 1380846
  have htrace : WordTrace (prefixWord ++ tailWord_1380846) baseStart_1380846 baseEnd_1380846 := by
    simpa [prefixWord, tailWord_1380846, baseEnd_1380846] using wordTrace_append hprefix tailTrace_1380846
  have hstable : (prefixWord ++ tailWord_1380846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380846).length < 2 ^ (prefixWord ++ tailWord_1380846).sum := by decide
  have hdescent : baseEnd_1380846 < baseStart_1380846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380866 : List Nat := [3, 4, 1, 2, 2, 1, 2, 8]
def baseStart_1380866 : Nat := 118140960795 + 1380866 * 2 ^ 59
def prefixEnd_1380866 : Nat := 4983230072969 + 3 ^ 40 * 1380866 * 2
def baseEnd_1380866 : Nat := 26261036201907392189797

theorem tailTrace_1380866 : CollatzResearch.WordTrace tailWord_1380866 prefixEnd_1380866 26261036201907392189797 := by
  unfold tailWord_1380866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591080153841447495568613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33576213743577193321516301 12591080153841447495568613)
  ·
    refine ⟨2360827528845271405419115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12591080153841447495568613 2360827528845271405419115)
    ·
      refine ⟨3541241293267907108128673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360827528845271405419115 3541241293267907108128673)
      ·
        refine ⟨2655930969950930331096505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3541241293267907108128673 2655930969950930331096505)
        ·
          refine ⟨1991948227463197748322379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655930969950930331096505 1991948227463197748322379)
          ·
            refine ⟨2987922341194796622483569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991948227463197748322379 2987922341194796622483569)
            ·
              refine ⟨2240941755896097466862677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987922341194796622483569 2240941755896097466862677)
              ·
                refine ⟨26261036201907392189797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2240941755896097466862677 26261036201907392189797)
                ·
                  rfl

theorem cell23_1380866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_1380866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380866 prefixEnd_1380866 := by exact prefixLift 1380866
  have htrace : WordTrace (prefixWord ++ tailWord_1380866) baseStart_1380866 baseEnd_1380866 := by
    simpa [prefixWord, tailWord_1380866, baseEnd_1380866] using wordTrace_append hprefix tailTrace_1380866
  have hstable : (prefixWord ++ tailWord_1380866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380866).length < 2 ^ (prefixWord ++ tailWord_1380866).sum := by decide
  have hdescent : baseEnd_1380866 < baseStart_1380866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380910 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1380910 : Nat := 118140960795 + 1380910 * 2 ^ 59
def prefixEnd_1380910 : Nat := 4983230072969 + 3 ^ 40 * 1380910 * 2
def baseEnd_1380910 : Nat := 709070570600297416974317

theorem tailTrace_1380910 : CollatzResearch.WordTrace tailWord_1380910 prefixEnd_1380910 709070570600297416974317 := by
  unfold tailWord_1380910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295740678400798187109523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33577283618137590331250789 6295740678400798187109523)
  ·
    refine ⟨9443611017601197280664285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6295740678400798187109523 9443611017601197280664285)
    ·
      refine ⟨3541354131600448980249107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9443611017601197280664285 3541354131600448980249107)
      ·
        refine ⟨5312031197400673470373661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541354131600448980249107 5312031197400673470373661)
        ·
          refine ⟨1992011699025252551390123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5312031197400673470373661 1992011699025252551390123)
          ·
            refine ⟨2988017548537878827085185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992011699025252551390123 2988017548537878827085185)
            ·
              refine ⟨2241013161403409120313889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988017548537878827085185 2241013161403409120313889)
              ·
                refine ⟨1680759871052556840235417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241013161403409120313889 1680759871052556840235417)
                ·
                  refine ⟨1260569903289417630176563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680759871052556840235417 1260569903289417630176563)
                  ·
                    refine ⟨1890854854934126445264845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1260569903289417630176563 1890854854934126445264845)
                    ·
                      refine ⟨709070570600297416974317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1890854854934126445264845 709070570600297416974317)
                      ·
                        rfl

theorem cell23_1380910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1380910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380910 prefixEnd_1380910 := by exact prefixLift 1380910
  have htrace : WordTrace (prefixWord ++ tailWord_1380910) baseStart_1380910 baseEnd_1380910 := by
    simpa [prefixWord, tailWord_1380910, baseEnd_1380910] using wordTrace_append hprefix tailTrace_1380910
  have hstable : (prefixWord ++ tailWord_1380910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380910).length < 2 ^ (prefixWord ++ tailWord_1380910).sum := by decide
  have hdescent : baseEnd_1380910 < baseStart_1380910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380929 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1380929 : Nat := 118140960795 + 1380929 * 2 ^ 59
def prefixEnd_1380929 : Nat := 4983230072969 + 3 ^ 40 * 1380929 * 2
def baseEnd_1380929 : Nat := 709080326732732842636729

theorem tailTrace_1380929 : CollatzResearch.WordTrace tailWord_1380929 prefixEnd_1380929 709080326732732842636729 := by
  unfold tailWord_1380929
  simp only [CollatzResearch.WordTrace]
  refine ⟨50366618414137551741817841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33577745609425034494545227 50366618414137551741817841)
  ·
    refine ⟨37774963810603163806363381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50366618414137551741817841 37774963810603163806363381)
    ·
      refine ⟨3541402857244046606846567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37774963810603163806363381 3541402857244046606846567)
      ·
        refine ⟨5312104285866069910269851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541402857244046606846567 5312104285866069910269851)
        ·
          refine ⟨7968156428799104865404777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312104285866069910269851 7968156428799104865404777)
          ·
            refine ⟨5976117321599328649053583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7968156428799104865404777 5976117321599328649053583)
            ·
              refine ⟨8964175982398992973580375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976117321599328649053583 8964175982398992973580375)
              ·
                refine ⟨13446263973598489460370563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964175982398992973580375 13446263973598489460370563)
                ·
                  refine ⟨20169395960397734190555845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13446263973598489460370563 20169395960397734190555845)
                  ·
                    refine ⟨3781761742574575160729221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20169395960397734190555845 3781761742574575160729221)
                    ·
                      refine ⟨709080326732732842636729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3781761742574575160729221 709080326732732842636729)
                      ·
                        rfl

theorem cell23_1380929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1380929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380929 prefixEnd_1380929 := by exact prefixLift 1380929
  have htrace : WordTrace (prefixWord ++ tailWord_1380929) baseStart_1380929 baseEnd_1380929 := by
    simpa [prefixWord, tailWord_1380929, baseEnd_1380929] using wordTrace_append hprefix tailTrace_1380929
  have hstable : (prefixWord ++ tailWord_1380929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380929).length < 2 ^ (prefixWord ++ tailWord_1380929).sum := by decide
  have hdescent : baseEnd_1380929 < baseStart_1380929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380933 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 2, 2, 2]
def baseStart_1380933 : Nat := 118140960795 + 1380933 * 2 ^ 59
def prefixEnd_1380933 : Nat := 4983230072969 + 3 ^ 40 * 1380933 * 2
def baseEnd_1380933 : Nat := 709082380655350826986711

theorem tailTrace_1380933 : CollatzResearch.WordTrace tailWord_1380933 prefixEnd_1380933 709082380655350826986711 := by
  unfold tailWord_1380933
  simp only [CollatzResearch.WordTrace]
  refine ⟨50366764306123060424963453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33577842870748706949975635 50366764306123060424963453)
  ·
    refine ⟨18887536614796147659361295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50366764306123060424963453 18887536614796147659361295)
    ·
      refine ⟨28331304922194221489041943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18887536614796147659361295 28331304922194221489041943)
      ·
        refine ⟨42496957383291332233562915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28331304922194221489041943 42496957383291332233562915)
        ·
          refine ⟨63745436074936998350344373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42496957383291332233562915 63745436074936998350344373)
          ·
            refine ⟨5976134632025343595344785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63745436074936998350344373 5976134632025343595344785)
            ·
              refine ⟨4482100974019007696508589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976134632025343595344785 4482100974019007696508589)
              ·
                refine ⟨1680787865257127886190721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4482100974019007696508589 1680787865257127886190721)
                ·
                  refine ⟨1260590898942845914643041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680787865257127886190721 1260590898942845914643041)
                  ·
                    refine ⟨945443174207134435982281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260590898942845914643041 945443174207134435982281)
                    ·
                      refine ⟨709082380655350826986711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945443174207134435982281 709082380655350826986711)
                      ·
                        rfl

theorem cell23_1380933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_1380933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1380933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1380933 prefixEnd_1380933 := by exact prefixLift 1380933
  have htrace : WordTrace (prefixWord ++ tailWord_1380933) baseStart_1380933 baseEnd_1380933 := by
    simpa [prefixWord, tailWord_1380933, baseEnd_1380933] using wordTrace_append hprefix tailTrace_1380933
  have hstable : (prefixWord ++ tailWord_1380933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380933).length < 2 ^ (prefixWord ++ tailWord_1380933).sum := by decide
  have hdescent : baseEnd_1380933 < baseStart_1380933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381006 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1381006 : Nat := 118140960795 + 1381006 * 2 ^ 59
def prefixEnd_1381006 : Nat := 4983230072969 + 3 ^ 40 * 1381006 * 2
def baseEnd_1381006 : Nat := 709119864743129041373875

theorem tailTrace_1381006 : CollatzResearch.WordTrace tailWord_1381006 prefixEnd_1381006 709119864743129041373875 := by
  unfold tailWord_1381006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296178354357324236546359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33579617889905729261580581 6296178354357324236546359)
  ·
    refine ⟨9444267531535986354819539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6296178354357324236546359 9444267531535986354819539)
    ·
      refine ⟨14166401297303979532229309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9444267531535986354819539 14166401297303979532229309)
      ·
        refine ⟨5312400486488992324585991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14166401297303979532229309 5312400486488992324585991)
        ·
          refine ⟨7968600729733488486878987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312400486488992324585991 7968600729733488486878987)
          ·
            refine ⟨11952901094600232730318481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7968600729733488486878987 11952901094600232730318481)
            ·
              refine ⟨8964675820950174547738861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11952901094600232730318481 8964675820950174547738861)
              ·
                refine ⟨3361753432856315455402073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8964675820950174547738861 3361753432856315455402073)
                ·
                  refine ⟨2521315074642236591551555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361753432856315455402073 2521315074642236591551555)
                  ·
                    refine ⟨3781972611963354887327333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2521315074642236591551555 3781972611963354887327333)
                    ·
                      refine ⟨709119864743129041373875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3781972611963354887327333 709119864743129041373875)
                      ·
                        rfl

theorem cell23_1381006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1381006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381006 prefixEnd_1381006 := by exact prefixLift 1381006
  have htrace : WordTrace (prefixWord ++ tailWord_1381006) baseStart_1381006 baseEnd_1381006 := by
    simpa [prefixWord, tailWord_1381006, baseEnd_1381006] using wordTrace_append hprefix tailTrace_1381006
  have hstable : (prefixWord ++ tailWord_1381006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381006).length < 2 ^ (prefixWord ++ tailWord_1381006).sum := by decide
  have hdescent : baseEnd_1381006 < baseStart_1381006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381029 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 6]
def baseStart_1381029 : Nat := 118140960795 + 1381029 * 2 ^ 59
def prefixEnd_1381029 : Nat := 4983230072969 + 3 ^ 40 * 1381029 * 2
def baseEnd_1381029 : Nat := 78792408310909161265141

theorem tailTrace_1381029 : CollatzResearch.WordTrace tailWord_1381029 prefixEnd_1381029 78792408310909161265141 := by
  unfold tailWord_1381029
  simp only [CollatzResearch.WordTrace]
  refine ⟨50370265713775268820458141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33580177142516845880305427 50370265713775268820458141)
  ·
    refine ⟨18888849642665725807671803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50370265713775268820458141 18888849642665725807671803)
    ·
      refine ⟨28333274463998588711507705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18888849642665725807671803 28333274463998588711507705)
      ·
        refine ⟨21249955847998941533630779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28333274463998588711507705 21249955847998941533630779)
        ·
          refine ⟨31874933771998412300446169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21249955847998941533630779 31874933771998412300446169)
          ·
            refine ⟨23906200328998809225334627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31874933771998412300446169 23906200328998809225334627)
            ·
              refine ⟨35859300493498213838001941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23906200328998809225334627 35859300493498213838001941)
              ·
                refine ⟨1680904710632728773656341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35859300493498213838001941 1680904710632728773656341)
                ·
                  refine ⟨78792408310909161265141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1680904710632728773656341 78792408310909161265141)
                  ·
                    rfl

theorem cell23_1381029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_1381029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381029 prefixEnd_1381029 := by exact prefixLift 1381029
  have htrace : WordTrace (prefixWord ++ tailWord_1381029) baseStart_1381029 baseEnd_1381029 := by
    simpa [prefixWord, tailWord_1381029, baseEnd_1381029] using wordTrace_append hprefix tailTrace_1381029
  have hstable : (prefixWord ++ tailWord_1381029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381029).length < 2 ^ (prefixWord ++ tailWord_1381029).sum := by decide
  have hdescent : baseEnd_1381029 < baseStart_1381029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381084 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1381084 : Nat := 118140960795 + 1381084 * 2 ^ 59
def prefixEnd_1381084 : Nat := 4983230072969 + 3 ^ 40 * 1381084 * 2
def baseEnd_1381084 : Nat := 236386638744726578732839

theorem tailTrace_1381084 : CollatzResearch.WordTrace tailWord_1381084 prefixEnd_1381084 236386638744726578732839 := by
  unfold tailWord_1381084
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186135864288006606855153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33581514485717342142473537 25186135864288006606855153)
  ·
    refine ⟨18889601898216004955141365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25186135864288006606855153 18889601898216004955141365)
    ·
      refine ⟨1770900177957750464544503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18889601898216004955141365 1770900177957750464544503)
      ·
        refine ⟨2656350266936625696816755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770900177957750464544503 2656350266936625696816755)
        ·
          refine ⟨3984525400404938545225133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656350266936625696816755 3984525400404938545225133)
          ·
            refine ⟨1494197025151851954459425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3984525400404938545225133 1494197025151851954459425)
            ·
              refine ⟨1120647768863888965844569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494197025151851954459425 1120647768863888965844569)
              ·
                refine ⟨840485826647916724383427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120647768863888965844569 840485826647916724383427)
                ·
                  refine ⟨1260728739971875086575141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840485826647916724383427 1260728739971875086575141)
                  ·
                    refine ⟨236386638744726578732839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260728739971875086575141 236386638744726578732839)
                    ·
                      rfl

theorem cell23_1381084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1381084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381084 prefixEnd_1381084 := by exact prefixLift 1381084
  have htrace : WordTrace (prefixWord ++ tailWord_1381084) baseStart_1381084 baseEnd_1381084 := by
    simpa [prefixWord, tailWord_1381084, baseEnd_1381084] using wordTrace_append hprefix tailTrace_1381084
  have hstable : (prefixWord ++ tailWord_1381084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381084).length < 2 ^ (prefixWord ++ tailWord_1381084).sum := by decide
  have hdescent : baseEnd_1381084 < baseStart_1381084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381099 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5]
def baseStart_1381099 : Nat := 118140960795 + 1381099 * 2 ^ 59
def prefixEnd_1381099 : Nat := 4983230072969 + 3 ^ 40 * 1381099 * 2
def baseEnd_1381099 : Nat := 709167618443997177510947

theorem tailTrace_1381099 : CollatzResearch.WordTrace tailWord_1381099 prefixEnd_1381099 709167618443997177510947 := by
  unfold tailWord_1381099
  simp only [CollatzResearch.WordTrace]
  refine ⟨50372818823521670775506351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33581879215681113850337567 50372818823521670775506351)
  ·
    refine ⟨75559228235282506163259527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50372818823521670775506351 75559228235282506163259527)
    ·
      refine ⟨113338842352923759244889291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75559228235282506163259527 113338842352923759244889291)
      ·
        refine ⟨170008263529385638867333937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113338842352923759244889291 170008263529385638867333937)
        ·
          refine ⟨127506197647039229150500453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170008263529385638867333937 127506197647039229150500453)
          ·
            refine ⟨23907412058819855465718835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127506197647039229150500453 23907412058819855465718835)
            ·
              refine ⟨35861118088229783198578253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23907412058819855465718835 35861118088229783198578253)
              ·
                refine ⟨13447919283086168699466845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35861118088229783198578253 13447919283086168699466845)
                ·
                  refine ⟨5042969731157313262300067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13447919283086168699466845 5042969731157313262300067)
                  ·
                    refine ⟨7564454596735969893450101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042969731157313262300067 7564454596735969893450101)
                    ·
                      refine ⟨709167618443997177510947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7564454596735969893450101 709167618443997177510947)
                      ·
                        rfl

theorem cell23_1381099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_1381099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381099 prefixEnd_1381099 := by exact prefixLift 1381099
  have htrace : WordTrace (prefixWord ++ tailWord_1381099) baseStart_1381099 baseEnd_1381099 := by
    simpa [prefixWord, tailWord_1381099, baseEnd_1381099] using wordTrace_append hprefix tailTrace_1381099
  have hstable : (prefixWord ++ tailWord_1381099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381099).length < 2 ^ (prefixWord ++ tailWord_1381099).sum := by decide
  have hdescent : baseEnd_1381099 < baseStart_1381099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381106 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1381106 : Nat := 118140960795 + 1381106 * 2 ^ 59
def prefixEnd_1381106 : Nat := 4983230072969 + 3 ^ 40 * 1381106 * 2
def baseEnd_1381106 : Nat := 236390404269526216707805

theorem tailTrace_1381106 : CollatzResearch.WordTrace tailWord_1381106 prefixEnd_1381106 236390404269526216707805 := by
  unfold tailWord_1381106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12593268533624077742752793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33582049422997540647340781 12593268533624077742752793)
  ·
    refine ⟨9444951400218058307064595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12593268533624077742752793 9444951400218058307064595)
    ·
      refine ⟨14167427100327087460596893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9444951400218058307064595 14167427100327087460596893)
      ·
        refine ⟨5312785162622657797723835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14167427100327087460596893 5312785162622657797723835)
        ·
          refine ⟨7969177743933986696585753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312785162622657797723835 7969177743933986696585753)
          ·
            refine ⟨5976883307950490022439315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7969177743933986696585753 5976883307950490022439315)
            ·
              refine ⟨8965324961925735033658973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976883307950490022439315 8965324961925735033658973)
              ·
                refine ⟨3361996860722150637622115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8965324961925735033658973 3361996860722150637622115)
                ·
                  refine ⟨5042995291083225956433173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361996860722150637622115 5042995291083225956433173)
                  ·
                    refine ⟨236390404269526216707805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5042995291083225956433173 236390404269526216707805)
                    ·
                      rfl

theorem cell23_1381106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1381106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381106 prefixEnd_1381106 := by exact prefixLift 1381106
  have htrace : WordTrace (prefixWord ++ tailWord_1381106) baseStart_1381106 baseEnd_1381106 := by
    simpa [prefixWord, tailWord_1381106, baseEnd_1381106] using wordTrace_append hprefix tailTrace_1381106
  have hstable : (prefixWord ++ tailWord_1381106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381106).length < 2 ^ (prefixWord ++ tailWord_1381106).sum := by decide
  have hdescent : baseEnd_1381106 < baseStart_1381106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381181 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1381181 : Nat := 118140960795 + 1381181 * 2 ^ 59
def prefixEnd_1381181 : Nat := 4983230072969 + 3 ^ 40 * 1381181 * 2
def baseEnd_1381181 : Nat := 709209723857665856685571

theorem tailTrace_1381181 : CollatzResearch.WordTrace tailWord_1381181 prefixEnd_1381181 709209723857665856685571 := by
  unfold tailWord_1381181
  simp only [CollatzResearch.WordTrace]
  refine ⟨50375809609224598779991397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33583873072816399186660931 50375809609224598779991397)
  ·
    refine ⟨9445464301729612271248387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50375809609224598779991397 9445464301729612271248387)
    ·
      refine ⟨14168196452594418406872581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9445464301729612271248387 14168196452594418406872581)
      ·
        refine ⟨2656536834861453451288609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14168196452594418406872581 2656536834861453451288609)
        ·
          refine ⟨1992402626146090088466457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2656536834861453451288609 1992402626146090088466457)
          ·
            refine ⟨1494301969609567566349843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992402626146090088466457 1494301969609567566349843)
            ·
              refine ⟨2241452954414351349524765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494301969609567566349843 2241452954414351349524765)
              ·
                refine ⟨840544857905381756071787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2241452954414351349524765 840544857905381756071787)
                ·
                  refine ⟨1260817286858072634107681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840544857905381756071787 1260817286858072634107681)
                  ·
                    refine ⟨945612965143554475580761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260817286858072634107681 945612965143554475580761)
                    ·
                      refine ⟨709209723857665856685571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945612965143554475580761 709209723857665856685571)
                      ·
                        rfl

theorem cell23_1381181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1381181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381181 prefixEnd_1381181 := by exact prefixLift 1381181
  have htrace : WordTrace (prefixWord ++ tailWord_1381181) baseStart_1381181 baseEnd_1381181 := by
    simpa [prefixWord, tailWord_1381181, baseEnd_1381181] using wordTrace_append hprefix tailTrace_1381181
  have hstable : (prefixWord ++ tailWord_1381181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381181).length < 2 ^ (prefixWord ++ tailWord_1381181).sum := by decide
  have hdescent : baseEnd_1381181 < baseStart_1381181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381216 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1381216 : Nat := 118140960795 + 1381216 * 2 ^ 59
def prefixEnd_1381216 : Nat := 4983230072969 + 3 ^ 40 * 1381216 * 2
def baseEnd_1381216 : Nat := 709227695680573219747909

theorem tailTrace_1381216 : CollatzResearch.WordTrace tailWord_1381216 prefixEnd_1381216 709227695680573219747909 := by
  unfold tailWord_1381216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25188543082048899878757751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33584724109398533171677001 25188543082048899878757751)
  ·
    refine ⟨37782814623073349818136627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25188543082048899878757751 37782814623073349818136627)
    ·
      refine ⟨56674221934610024727204941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37782814623073349818136627 56674221934610024727204941)
      ·
        refine ⟨21252833225478759272701853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56674221934610024727204941 21252833225478759272701853)
        ·
          refine ⟨7969812459554534727263195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21252833225478759272701853 7969812459554534727263195)
          ·
            refine ⟨11954718689331802090894793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969812459554534727263195 11954718689331802090894793)
            ·
              refine ⟨8966039016998851568171095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11954718689331802090894793 8966039016998851568171095)
              ·
                refine ⟨13449058525498277352256643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8966039016998851568171095 13449058525498277352256643)
                ·
                  refine ⟨20173587788247416028384965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13449058525498277352256643 20173587788247416028384965)
                  ·
                    refine ⟨3782547710296390505322181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20173587788247416028384965 3782547710296390505322181)
                    ·
                      refine ⟨709227695680573219747909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3782547710296390505322181 709227695680573219747909)
                      ·
                        rfl

theorem cell23_1381216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1381216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381216 prefixEnd_1381216 := by exact prefixLift 1381216
  have htrace : WordTrace (prefixWord ++ tailWord_1381216) baseStart_1381216 baseEnd_1381216 := by
    simpa [prefixWord, tailWord_1381216, baseEnd_1381216] using wordTrace_append hprefix tailTrace_1381216
  have hstable : (prefixWord ++ tailWord_1381216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381216).length < 2 ^ (prefixWord ++ tailWord_1381216).sum := by decide
  have hdescent : baseEnd_1381216 < baseStart_1381216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381260 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 5]
def baseStart_1381260 : Nat := 118140960795 + 1381260 * 2 ^ 59
def prefixEnd_1381260 : Nat := 4983230072969 + 3 ^ 40 * 1381260 * 2
def baseEnd_1381260 : Nat := 78805587647707894177523

theorem tailTrace_1381260 : CollatzResearch.WordTrace tailWord_1381260 prefixEnd_1381260 78805587647707894177523 := by
  unfold tailWord_1381260
  simp only [CollatzResearch.WordTrace]
  refine ⟨25189345487969197636058617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33585793983958930181411489 25189345487969197636058617)
  ·
    refine ⟨18892009115976898227043963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25189345487969197636058617 18892009115976898227043963)
    ·
      refine ⟨28338013673965347340565945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18892009115976898227043963 28338013673965347340565945)
      ·
        refine ⟨21253510255474010505424459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28338013673965347340565945 21253510255474010505424459)
        ·
          refine ⟨31880265383211015758136689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21253510255474010505424459 31880265383211015758136689)
          ·
            refine ⟨23910199037408261818602517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31880265383211015758136689 23910199037408261818602517)
            ·
              refine ⟨1120790579878512272746993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23910199037408261818602517 1120790579878512272746993)
              ·
                refine ⟨840592934908884204560245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120790579878512272746993 840592934908884204560245)
                ·
                  refine ⟨78805587647707894177523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 840592934908884204560245 78805587647707894177523)
                  ·
                    rfl

theorem cell23_1381260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_1381260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381260 prefixEnd_1381260 := by exact prefixLift 1381260
  have htrace : WordTrace (prefixWord ++ tailWord_1381260) baseStart_1381260 baseEnd_1381260 := by
    simpa [prefixWord, tailWord_1381260, baseEnd_1381260] using wordTrace_append hprefix tailTrace_1381260
  have hstable : (prefixWord ++ tailWord_1381260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381260).length < 2 ^ (prefixWord ++ tailWord_1381260).sum := by decide
  have hdescent : baseEnd_1381260 < baseStart_1381260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381306 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1381306 : Nat := 118140960795 + 1381306 * 2 ^ 59
def prefixEnd_1381306 : Nat := 4983230072969 + 3 ^ 40 * 1381306 * 2
def baseEnd_1381306 : Nat := 709273908939477867622495

theorem tailTrace_1381306 : CollatzResearch.WordTrace tailWord_1381306 prefixEnd_1381306 709273908939477867622495 := by
  unfold tailWord_1381306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595092183442936282072943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33586912489181163418861181 12595092183442936282072943)
  ·
    refine ⟨18892638275164404423109415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12595092183442936282072943 18892638275164404423109415)
    ·
      refine ⟨28338957412746606634664123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18892638275164404423109415 28338957412746606634664123)
      ·
        refine ⟨42508436119119909951996185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28338957412746606634664123 42508436119119909951996185)
        ·
          refine ⟨31881327089339932463997139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42508436119119909951996185 31881327089339932463997139)
          ·
            refine ⟨47821990634009898695995709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31881327089339932463997139 47821990634009898695995709)
            ·
              refine ⟨17933246487753712010998391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47821990634009898695995709 17933246487753712010998391)
              ·
                refine ⟨26899869731630568016497587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17933246487753712010998391 26899869731630568016497587)
                ·
                  refine ⟨40349804597445852024746381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26899869731630568016497587 40349804597445852024746381)
                  ·
                    refine ⟨15131176724042194509279893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40349804597445852024746381 15131176724042194509279893)
                    ·
                      refine ⟨709273908939477867622495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15131176724042194509279893 709273908939477867622495)
                      ·
                        rfl

theorem cell23_1381306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1381306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381306 prefixEnd_1381306 := by exact prefixLift 1381306
  have htrace : WordTrace (prefixWord ++ tailWord_1381306) baseStart_1381306 baseEnd_1381306 := by
    simpa [prefixWord, tailWord_1381306, baseEnd_1381306] using wordTrace_append hprefix tailTrace_1381306
  have hstable : (prefixWord ++ tailWord_1381306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381306).length < 2 ^ (prefixWord ++ tailWord_1381306).sum := by decide
  have hdescent : baseEnd_1381306 < baseStart_1381306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381310 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_1381310 : Nat := 118140960795 + 1381310 * 2 ^ 59
def prefixEnd_1381310 : Nat := 4983230072969 + 3 ^ 40 * 1381310 * 2
def baseEnd_1381310 : Nat := 709275962862095851972477

theorem tailTrace_1381310 : CollatzResearch.WordTrace tailWord_1381310 prefixEnd_1381310 709275962862095851972477 := by
  unfold tailWord_1381310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297564328219656726429673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33587009750504835874291589 6297564328219656726429673)
  ·
    refine ⟨4723173246164742544822255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6297564328219656726429673 4723173246164742544822255)
    ·
      refine ⟨7084759869247113817233383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723173246164742544822255 7084759869247113817233383)
      ·
        refine ⟨10627139803870670725850075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084759869247113817233383 10627139803870670725850075)
        ·
          refine ⟨15940709705806006088775113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10627139803870670725850075 15940709705806006088775113)
          ·
            refine ⟨11955532279354504566581335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15940709705806006088775113 11955532279354504566581335)
            ·
              refine ⟨17933298419031756849872003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11955532279354504566581335 17933298419031756849872003)
              ·
                refine ⟨26899947628547635274808005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17933298419031756849872003 26899947628547635274808005)
                ·
                  refine ⟨5043740180352681614026501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26899947628547635274808005 5043740180352681614026501)
                  ·
                    refine ⟨945701283816127802629969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043740180352681614026501 945701283816127802629969)
                    ·
                      refine ⟨709275962862095851972477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945701283816127802629969 709275962862095851972477)
                      ·
                        rfl

theorem cell23_1381310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_1381310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381310 prefixEnd_1381310 := by exact prefixLift 1381310
  have htrace : WordTrace (prefixWord ++ tailWord_1381310) baseStart_1381310 baseEnd_1381310 := by
    simpa [prefixWord, tailWord_1381310, baseEnd_1381310] using wordTrace_append hprefix tailTrace_1381310
  have hstable : (prefixWord ++ tailWord_1381310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381310).length < 2 ^ (prefixWord ++ tailWord_1381310).sum := by decide
  have hdescent : baseEnd_1381310 < baseStart_1381310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381330 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1381330 : Nat := 118140960795 + 1381330 * 2 ^ 59
def prefixEnd_1381330 : Nat := 4983230072969 + 3 ^ 40 * 1381330 * 2
def baseEnd_1381330 : Nat := 709286232475185773722385

theorem tailTrace_1381330 : CollatzResearch.WordTrace tailWord_1381330 prefixEnd_1381330 709286232475185773722385 := by
  unfold tailWord_1381330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595311021421199306791361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33587496057123198151443629 12595311021421199306791361)
  ·
    refine ⟨9446483266065899480093521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12595311021421199306791361 9446483266065899480093521)
    ·
      refine ⟨7084862449549424610070141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9446483266065899480093521 7084862449549424610070141)
      ·
        refine ⟨2656823418581034228776303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7084862449549424610070141 2656823418581034228776303)
        ·
          refine ⟨3985235127871551343164455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656823418581034228776303 3985235127871551343164455)
          ·
            refine ⟨5977852691807327014746683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985235127871551343164455 5977852691807327014746683)
            ·
              refine ⟨8966779037710990522120025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977852691807327014746683 8966779037710990522120025)
              ·
                refine ⟨6725084278283242891590019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8966779037710990522120025 6725084278283242891590019)
                ·
                  refine ⟨10087626417424864337385029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725084278283242891590019 10087626417424864337385029)
                  ·
                    refine ⟨1891429953267162063259693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10087626417424864337385029 1891429953267162063259693)
                    ·
                      refine ⟨709286232475185773722385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1891429953267162063259693 709286232475185773722385)
                      ·
                        rfl

theorem cell23_1381330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1381330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381330 prefixEnd_1381330 := by exact prefixLift 1381330
  have htrace : WordTrace (prefixWord ++ tailWord_1381330) baseStart_1381330 baseEnd_1381330 := by
    simpa [prefixWord, tailWord_1381330, baseEnd_1381330] using wordTrace_append hprefix tailTrace_1381330
  have hstable : (prefixWord ++ tailWord_1381330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381330).length < 2 ^ (prefixWord ++ tailWord_1381330).sum := by decide
  have hdescent : baseEnd_1381330 < baseStart_1381330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381354 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_1381354 : Nat := 118140960795 + 1381354 * 2 ^ 59
def prefixEnd_1381354 : Nat := 4983230072969 + 3 ^ 40 * 1381354 * 2
def baseEnd_1381354 : Nat := 236432852003631226607425

theorem tailTrace_1381354 : CollatzResearch.WordTrace tailWord_1381354 prefixEnd_1381354 236432852003631226607425 := by
  unfold tailWord_1381354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595529859399462331509779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33588079625065232884026077 12595529859399462331509779)
  ·
    refine ⟨18893294789099193497264669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12595529859399462331509779 18893294789099193497264669)
    ·
      refine ⟨7084985545912197561474251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18893294789099193497264669 7084985545912197561474251)
      ·
        refine ⟨10627478318868296342211377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084985545912197561474251 10627478318868296342211377)
        ·
          refine ⟨7970608739151222256658533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10627478318868296342211377 7970608739151222256658533)
          ·
            refine ⟨1494489138590854173123475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7970608739151222256658533 1494489138590854173123475)
            ·
              refine ⟨2241733707886281259685213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494489138590854173123475 2241733707886281259685213)
              ·
                refine ⟨840650140457355472381955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2241733707886281259685213 840650140457355472381955)
                ·
                  refine ⟨1260975210686033208572933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840650140457355472381955 1260975210686033208572933)
                  ·
                    refine ⟨236432852003631226607425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260975210686033208572933 236432852003631226607425)
                    ·
                      rfl

theorem cell23_1381354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_1381354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381354 prefixEnd_1381354 := by exact prefixLift 1381354
  have htrace : WordTrace (prefixWord ++ tailWord_1381354) baseStart_1381354 baseEnd_1381354 := by
    simpa [prefixWord, tailWord_1381354, baseEnd_1381354] using wordTrace_append hprefix tailTrace_1381354
  have hstable : (prefixWord ++ tailWord_1381354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381354).length < 2 ^ (prefixWord ++ tailWord_1381354).sum := by decide
  have hdescent : baseEnd_1381354 < baseStart_1381354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381377 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1381377 : Nat := 118140960795 + 1381377 * 2 ^ 59
def prefixEnd_1381377 : Nat := 4983230072969 + 3 ^ 40 * 1381377 * 2
def baseEnd_1381377 : Nat := 709310366065947089834669

theorem tailTrace_1381377 : CollatzResearch.WordTrace tailWord_1381377 prefixEnd_1381377 709310366065947089834669 := by
  unfold tailWord_1381377
  simp only [CollatzResearch.WordTrace]
  refine ⟨50382958316514524254126385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33588638877676349502750923 50382958316514524254126385)
  ·
    refine ⟨37787218737385893190594789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50382958316514524254126385 37787218737385893190594789)
    ·
      refine ⟨7085103513259854973236523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37787218737385893190594789 7085103513259854973236523)
      ·
        refine ⟨10627655269889782459854785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085103513259854973236523 10627655269889782459854785)
        ·
          refine ⟨7970741452417336844891089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10627655269889782459854785 7970741452417336844891089)
          ·
            refine ⟨5978056089313002633668317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7970741452417336844891089 5978056089313002633668317)
            ·
              refine ⟨2241771033492375987625619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5978056089313002633668317 2241771033492375987625619)
              ·
                refine ⟨3362656550238563981438429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241771033492375987625619 3362656550238563981438429)
                ·
                  refine ⟨1260996206339461493039411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3362656550238563981438429 1260996206339461493039411)
                  ·
                    refine ⟨1891494309509192239559117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1260996206339461493039411 1891494309509192239559117)
                    ·
                      refine ⟨709310366065947089834669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1891494309509192239559117 709310366065947089834669)
                      ·
                        rfl

theorem cell23_1381377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1381377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381377 prefixEnd_1381377 := by exact prefixLift 1381377
  have htrace : WordTrace (prefixWord ++ tailWord_1381377) baseStart_1381377 baseEnd_1381377 := by
    simpa [prefixWord, tailWord_1381377, baseEnd_1381377] using wordTrace_append hprefix tailTrace_1381377
  have hstable : (prefixWord ++ tailWord_1381377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381377).length < 2 ^ (prefixWord ++ tailWord_1381377).sum := by decide
  have hdescent : baseEnd_1381377 < baseStart_1381377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381397 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1381397 : Nat := 118140960795 + 1381397 * 2 ^ 59
def prefixEnd_1381397 : Nat := 4983230072969 + 3 ^ 40 * 1381397 * 2
def baseEnd_1381397 : Nat := 236440211893012337194859

theorem tailTrace_1381397 : CollatzResearch.WordTrace tailWord_1381397 prefixEnd_1381397 236440211893012337194859 := by
  unfold tailWord_1381397
  simp only [CollatzResearch.WordTrace]
  refine ⟨50383687776442067669854445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33589125184294711779902963 50383687776442067669854445)
  ·
    refine ⟨18893882916165775376195417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50383687776442067669854445 18893882916165775376195417)
    ·
      refine ⟨14170412187124331532146563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18893882916165775376195417 14170412187124331532146563)
      ·
        refine ⟨21255618280686497298219845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14170412187124331532146563 21255618280686497298219845)
        ·
          refine ⟨3985428427628718243416221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21255618280686497298219845 3985428427628718243416221)
          ·
            refine ⟨1494535660360769341281083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3985428427628718243416221 1494535660360769341281083)
            ·
              refine ⟨2241803490541154011921625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494535660360769341281083 2241803490541154011921625)
              ·
                refine ⟨1681352617905865508941219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241803490541154011921625 1681352617905865508941219)
                ·
                  refine ⟨2522028926858798263411829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681352617905865508941219 2522028926858798263411829)
                  ·
                    refine ⟨236440211893012337194859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2522028926858798263411829 236440211893012337194859)
                    ·
                      rfl

theorem cell23_1381397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1381397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381397 prefixEnd_1381397 := by exact prefixLift 1381397
  have htrace : WordTrace (prefixWord ++ tailWord_1381397) baseStart_1381397 baseEnd_1381397 := by
    simpa [prefixWord, tailWord_1381397, baseEnd_1381397] using wordTrace_append hprefix tailTrace_1381397
  have hstable : (prefixWord ++ tailWord_1381397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381397).length < 2 ^ (prefixWord ++ tailWord_1381397).sum := by decide
  have hdescent : baseEnd_1381397 < baseStart_1381397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381400 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1381400 : Nat := 118140960795 + 1381400 * 2 ^ 59
def prefixEnd_1381400 : Nat := 4983230072969 + 3 ^ 40 * 1381400 * 2
def baseEnd_1381400 : Nat := 709322176121000499847063

theorem tailTrace_1381400 : CollatzResearch.WordTrace tailWord_1381400 prefixEnd_1381400 709322176121000499847063 := by
  unfold tailWord_1381400
  simp only [CollatzResearch.WordTrace]
  refine ⟨25191898597715599591106827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33589198130287466121475769 25191898597715599591106827)
  ·
    refine ⟨37787847896573399386660241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25191898597715599591106827 37787847896573399386660241)
    ·
      refine ⟨28340885922430049539995181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37787847896573399386660241 28340885922430049539995181)
      ·
        refine ⟨10627832220911268577498193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28340885922430049539995181 10627832220911268577498193)
        ·
          refine ⟨7970874165683451433123645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10627832220911268577498193 7970874165683451433123645)
          ·
            refine ⟨2989077812131294287421367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7970874165683451433123645 2989077812131294287421367)
            ·
              refine ⟨4483616718196941431132051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989077812131294287421367 4483616718196941431132051)
              ·
                refine ⟨6725425077295412146698077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483616718196941431132051 6725425077295412146698077)
                ·
                  refine ⟨2522034403985779555011779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6725425077295412146698077 2522034403985779555011779)
                  ·
                    refine ⟨3783051605978669332517669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522034403985779555011779 3783051605978669332517669)
                    ·
                      refine ⟨709322176121000499847063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3783051605978669332517669 709322176121000499847063)
                      ·
                        rfl

theorem cell23_1381400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1381400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381400 prefixEnd_1381400 := by exact prefixLift 1381400
  have htrace : WordTrace (prefixWord ++ tailWord_1381400) baseStart_1381400 baseEnd_1381400 := by
    simpa [prefixWord, tailWord_1381400, baseEnd_1381400] using wordTrace_append hprefix tailTrace_1381400
  have hstable : (prefixWord ++ tailWord_1381400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381400).length < 2 ^ (prefixWord ++ tailWord_1381400).sum := by decide
  have hdescent : baseEnd_1381400 < baseStart_1381400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381404 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_1381404 : Nat := 118140960795 + 1381404 * 2 ^ 59
def prefixEnd_1381404 : Nat := 4983230072969 + 3 ^ 40 * 1381404 * 2
def baseEnd_1381404 : Nat := 709324230043618484197045

theorem tailTrace_1381404 : CollatzResearch.WordTrace tailWord_1381404 prefixEnd_1381404 709324230043618484197045 := by
  unfold tailWord_1381404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25191971543708353932679633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33589295391611138576906177 25191971543708353932679633)
  ·
    refine ⟨18893978657781265449509725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25191971543708353932679633 18893978657781265449509725)
    ·
      refine ⟨7085241996667974543566147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18893978657781265449509725 7085241996667974543566147)
      ·
        refine ⟨10627862995001961815349221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085241996667974543566147 10627862995001961815349221)
        ·
          refine ⟨1992724311562867840377979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10627862995001961815349221 1992724311562867840377979)
          ·
            refine ⟨2989086467344301760566969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992724311562867840377979 2989086467344301760566969)
            ·
              refine ⟨2241814850508226320425227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989086467344301760566969 2241814850508226320425227)
              ·
                refine ⟨3362722275762339480637841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241814850508226320425227 3362722275762339480637841)
                ·
                  refine ⟨2522041706821754610478381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3362722275762339480637841 2522041706821754610478381)
                  ·
                    refine ⟨945765640058157978929393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522041706821754610478381 945765640058157978929393)
                    ·
                      refine ⟨709324230043618484197045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945765640058157978929393 709324230043618484197045)
                      ·
                        rfl

theorem cell23_1381404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_1381404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381404 prefixEnd_1381404 := by exact prefixLift 1381404
  have htrace : WordTrace (prefixWord ++ tailWord_1381404) baseStart_1381404 baseEnd_1381404 := by
    simpa [prefixWord, tailWord_1381404, baseEnd_1381404] using wordTrace_append hprefix tailTrace_1381404
  have hstable : (prefixWord ++ tailWord_1381404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381404).length < 2 ^ (prefixWord ++ tailWord_1381404).sum := by decide
  have hdescent : baseEnd_1381404 < baseStart_1381404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381410 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1381410 : Nat := 118140960795 + 1381410 * 2 ^ 59
def prefixEnd_1381410 : Nat := 4983230072969 + 3 ^ 40 * 1381410 * 2
def baseEnd_1381410 : Nat := 236442436975848486907339

theorem tailTrace_1381410 : CollatzResearch.WordTrace tailWord_1381410 prefixEnd_1381410 236442436975848486907339 := by
  unfold tailWord_1381410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12596040481348742722519421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33589441283596647260051789 12596040481348742722519421)
  ·
    refine ⟨4723515180505778520944783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12596040481348742722519421 4723515180505778520944783)
    ·
      refine ⟨7085272770758667781417175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723515180505778520944783 7085272770758667781417175)
      ·
        refine ⟨10627909156138001672125763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085272770758667781417175 10627909156138001672125763)
        ·
          refine ⟨15941863734207002508188645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10627909156138001672125763 15941863734207002508188645)
          ·
            refine ⟨2989099450163812970285371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15941863734207002508188645 2989099450163812970285371)
            ·
              refine ⟨4483649175245719455428057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989099450163812970285371 4483649175245719455428057)
              ·
                refine ⟨3362736881434289591571043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4483649175245719455428057 3362736881434289591571043)
                ·
                  refine ⟨5044105322151434387356565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362736881434289591571043 5044105322151434387356565)
                  ·
                    refine ⟨236442436975848486907339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5044105322151434387356565 236442436975848486907339)
                    ·
                      rfl

theorem cell23_1381410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1381410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381410 prefixEnd_1381410 := by exact prefixLift 1381410
  have htrace : WordTrace (prefixWord ++ tailWord_1381410) baseStart_1381410 baseEnd_1381410 := by
    simpa [prefixWord, tailWord_1381410, baseEnd_1381410] using wordTrace_append hprefix tailTrace_1381410
  have hstable : (prefixWord ++ tailWord_1381410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381410).length < 2 ^ (prefixWord ++ tailWord_1381410).sum := by decide
  have hdescent : baseEnd_1381410 < baseStart_1381410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381428 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1381428 : Nat := 118140960795 + 1381428 * 2 ^ 59
def prefixEnd_1381428 : Nat := 4983230072969 + 3 ^ 40 * 1381428 * 2
def baseEnd_1381428 : Nat := 709336553579326390296935

theorem tailTrace_1381428 : CollatzResearch.WordTrace tailWord_1381428 prefixEnd_1381428 709336553579326390296935 := by
  unfold tailWord_1381428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25192409219664879982116469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33589878959553173309488625 25192409219664879982116469)
  ·
    refine ⟨2361788364343582498323419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25192409219664879982116469 2361788364343582498323419)
    ·
      refine ⟨3542682546515373747485129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2361788364343582498323419 3542682546515373747485129)
      ·
        refine ⟨2657011909886530310613847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3542682546515373747485129 2657011909886530310613847)
        ·
          refine ⟨3985517864829795465920771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657011909886530310613847 3985517864829795465920771)
          ·
            refine ⟨5978276797244693198881157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985517864829795465920771 5978276797244693198881157)
            ·
              refine ⟨1120926899483379974790217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5978276797244693198881157 1120926899483379974790217)
              ·
                refine ⟨840695174612534981092663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120926899483379974790217 840695174612534981092663)
                ·
                  refine ⟨1261042761918802471638995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840695174612534981092663 1261042761918802471638995)
                  ·
                    refine ⟨1891564142878203707458493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261042761918802471638995 1891564142878203707458493)
                    ·
                      refine ⟨709336553579326390296935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1891564142878203707458493 709336553579326390296935)
                      ·
                        rfl

theorem cell23_1381428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1381428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381428 prefixEnd_1381428 := by exact prefixLift 1381428
  have htrace : WordTrace (prefixWord ++ tailWord_1381428) baseStart_1381428 baseEnd_1381428 := by
    simpa [prefixWord, tailWord_1381428, baseEnd_1381428] using wordTrace_append hprefix tailTrace_1381428
  have hstable : (prefixWord ++ tailWord_1381428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381428).length < 2 ^ (prefixWord ++ tailWord_1381428).sum := by decide
  have hdescent : baseEnd_1381428 < baseStart_1381428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381450 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1381450 : Nat := 118140960795 + 1381450 * 2 ^ 59
def prefixEnd_1381450 : Nat := 4983230072969 + 3 ^ 40 * 1381450 * 2
def baseEnd_1381450 : Nat := 709347850153725304221833

theorem tailTrace_1381450 : CollatzResearch.WordTrace tailWord_1381450 prefixEnd_1381450 709347850153725304221833 := by
  unfold tailWord_1381450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12596405211312514430383451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33590413896833371814355869 12596405211312514430383451)
  ·
    refine ⟨18894607816968771645575177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12596405211312514430383451 18894607816968771645575177)
    ·
      refine ⟨14170955862726578734181383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18894607816968771645575177 14170955862726578734181383)
      ·
        refine ⟨21256433794089868101272075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14170955862726578734181383 21256433794089868101272075)
        ·
          refine ⟨31884650691134802151908113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21256433794089868101272075 31884650691134802151908113)
          ·
            refine ⟨23913488018351101613931085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31884650691134802151908113 23913488018351101613931085)
            ·
              refine ⟨8967558006881663105224157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23913488018351101613931085 8967558006881663105224157)
              ·
                refine ⟨3362834252580623664459059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8967558006881663105224157 3362834252580623664459059)
                ·
                  refine ⟨5044251378870935496688589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362834252580623664459059 5044251378870935496688589)
                  ·
                    refine ⟨1891594267076600811258221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5044251378870935496688589 1891594267076600811258221)
                    ·
                      refine ⟨709347850153725304221833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1891594267076600811258221 709347850153725304221833)
                      ·
                        rfl

theorem cell23_1381450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1381450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381450 prefixEnd_1381450 := by exact prefixLift 1381450
  have htrace : WordTrace (prefixWord ++ tailWord_1381450) baseStart_1381450 baseEnd_1381450 := by
    simpa [prefixWord, tailWord_1381450, baseEnd_1381450] using wordTrace_append hprefix tailTrace_1381450
  have hstable : (prefixWord ++ tailWord_1381450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381450).length < 2 ^ (prefixWord ++ tailWord_1381450).sum := by decide
  have hdescent : baseEnd_1381450 < baseStart_1381450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381463 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1381463 : Nat := 118140960795 + 1381463 * 2 ^ 59
def prefixEnd_1381463 : Nat := 4983230072969 + 3 ^ 40 * 1381463 * 2
def baseEnd_1381463 : Nat := 709354525402233753359273

theorem tailTrace_1381463 : CollatzResearch.WordTrace tailWord_1381463 prefixEnd_1381463 709354525402233753359273 := by
  unfold tailWord_1381463
  simp only [CollatzResearch.WordTrace]
  refine ⟨50386094994202960941757043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33590729996135307294504695 50386094994202960941757043)
  ·
    refine ⟨75579142491304441412635565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50386094994202960941757043 75579142491304441412635565)
    ·
      refine ⟨28342178434239165529738337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75579142491304441412635565 28342178434239165529738337)
      ·
        refine ⟨21256633825679374147303753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28342178434239165529738337 21256633825679374147303753)
        ·
          refine ⟨15942475369259530610477815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21256633825679374147303753 15942475369259530610477815)
          ·
            refine ⟨23913713053889295915716723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15942475369259530610477815 23913713053889295915716723)
            ·
              refine ⟨35870569580833943873575085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23913713053889295915716723 35870569580833943873575085)
              ·
                refine ⟨13451463592812728952590657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35870569580833943873575085 13451463592812728952590657)
                ·
                  refine ⟨10088597694609546714442993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13451463592812728952590657 10088597694609546714442993)
                  ·
                    refine ⟨7566448270957160035832245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10088597694609546714442993 7566448270957160035832245)
                    ·
                      refine ⟨709354525402233753359273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7566448270957160035832245 709354525402233753359273)
                      ·
                        rfl

theorem cell23_1381463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1381463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381463 prefixEnd_1381463 := by exact prefixLift 1381463
  have htrace : WordTrace (prefixWord ++ tailWord_1381463) baseStart_1381463 baseEnd_1381463 := by
    simpa [prefixWord, tailWord_1381463, baseEnd_1381463] using wordTrace_append hprefix tailTrace_1381463
  have hstable : (prefixWord ++ tailWord_1381463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381463).length < 2 ^ (prefixWord ++ tailWord_1381463).sum := by decide
  have hdescent : baseEnd_1381463 < baseStart_1381463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381714 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1381714 : Nat := 118140960795 + 1381714 * 2 ^ 59
def prefixEnd_1381714 : Nat := 4983230072969 + 3 ^ 40 * 1381714 * 2
def baseEnd_1381714 : Nat := 236494469682170757106873

theorem tailTrace_1381714 : CollatzResearch.WordTrace tailWord_1381714 prefixEnd_1381714 236494469682170757106873 := by
  unfold tailWord_1381714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12598812429073407702286049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33596833144195753872762797 12598812429073407702286049)
  ·
    refine ⟨9449109321805055776714537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12598812429073407702286049 9449109321805055776714537)
    ·
      refine ⟨7086831991353791832535903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9449109321805055776714537 7086831991353791832535903)
      ·
        refine ⟨10630247987030687748803855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086831991353791832535903 10630247987030687748803855)
        ·
          refine ⟨15945371980546031623205783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10630247987030687748803855 15945371980546031623205783)
          ·
            refine ⟨23918057970819047434808675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15945371980546031623205783 23918057970819047434808675)
            ·
              refine ⟨35877086956228571152213013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23918057970819047434808675 35877086956228571152213013)
              ·
                refine ⟨1681738451073214272759985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35877086956228571152213013 1681738451073214272759985)
                ·
                  refine ⟨1261303838304910704569989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1681738451073214272759985 1261303838304910704569989)
                  ·
                    refine ⟨236494469682170757106873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1261303838304910704569989 236494469682170757106873)
                    ·
                      rfl

theorem cell23_1381714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1381714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381714 prefixEnd_1381714 := by exact prefixLift 1381714
  have htrace : WordTrace (prefixWord ++ tailWord_1381714) baseStart_1381714 baseEnd_1381714 := by
    simpa [prefixWord, tailWord_1381714, baseEnd_1381714] using wordTrace_append hprefix tailTrace_1381714
  have hstable : (prefixWord ++ tailWord_1381714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381714).length < 2 ^ (prefixWord ++ tailWord_1381714).sum := by decide
  have hdescent : baseEnd_1381714 < baseStart_1381714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381717 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1381717 : Nat := 118140960795 + 1381717 * 2 ^ 59
def prefixEnd_1381717 : Nat := 4983230072969 + 3 ^ 40 * 1381717 * 2
def baseEnd_1381717 : Nat := 709484949488475759583105

theorem tailTrace_1381717 : CollatzResearch.WordTrace tailWord_1381717 prefixEnd_1381717 709484949488475759583105 := by
  unfold tailWord_1381717
  simp only [CollatzResearch.WordTrace]
  refine ⟨50395359135282762321503405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33596906090188508214335603 50395359135282762321503405)
  ·
    refine ⟨18898259675731035870563777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50395359135282762321503405 18898259675731035870563777)
    ·
      refine ⟨14173694756798276902922833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18898259675731035870563777 14173694756798276902922833)
      ·
        refine ⟨10630271067598707677192125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14173694756798276902922833 10630271067598707677192125)
        ·
          refine ⟨3986351650349515378947047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10630271067598707677192125 3986351650349515378947047)
          ·
            refine ⟨5979527475524273068420571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986351650349515378947047 5979527475524273068420571)
            ·
              refine ⟨8969291213286409602630857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979527475524273068420571 8969291213286409602630857)
              ·
                refine ⟨6726968409964807201973143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8969291213286409602630857 6726968409964807201973143)
                ·
                  refine ⟨10090452614947210802959715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6726968409964807201973143 10090452614947210802959715)
                  ·
                    refine ⟨15135678922420816204439573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10090452614947210802959715 15135678922420816204439573)
                    ·
                      refine ⟨709484949488475759583105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15135678922420816204439573 709484949488475759583105)
                      ·
                        rfl

theorem cell23_1381717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1381717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381717 prefixEnd_1381717 := by exact prefixLift 1381717
  have htrace : WordTrace (prefixWord ++ tailWord_1381717) baseStart_1381717 baseEnd_1381717 := by
    simpa [prefixWord, tailWord_1381717, baseEnd_1381717] using wordTrace_append hprefix tailTrace_1381717
  have hstable : (prefixWord ++ tailWord_1381717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381717).length < 2 ^ (prefixWord ++ tailWord_1381717).sum := by decide
  have hdescent : baseEnd_1381717 < baseStart_1381717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381721 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 3, 2, 2]
def baseStart_1381721 : Nat := 118140960795 + 1381721 * 2 ^ 59
def prefixEnd_1381721 : Nat := 4983230072969 + 3 ^ 40 * 1381721 * 2
def baseEnd_1381721 : Nat := 709487003411093743933087

theorem tailTrace_1381721 : CollatzResearch.WordTrace tailWord_1381721 prefixEnd_1381721 709487003411093743933087 := by
  unfold tailWord_1381721
  simp only [CollatzResearch.WordTrace]
  refine ⟨50395505027268271004649017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33597003351512180669766011 50395505027268271004649017)
  ·
    refine ⟨37796628770451203253486763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50395505027268271004649017 37796628770451203253486763)
    ·
      refine ⟨56694943155676804880230145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37796628770451203253486763 56694943155676804880230145)
      ·
        refine ⟨42521207366757603660172609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56694943155676804880230145 42521207366757603660172609)
        ·
          refine ⟨31890905525068202745129457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42521207366757603660172609 31890905525068202745129457)
          ·
            refine ⟨23918179143801152058847093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31890905525068202745129457 23918179143801152058847093)
            ·
              refine ⟨2242329294731358005516915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23918179143801152058847093 2242329294731358005516915)
              ·
                refine ⟨3363493942097037008275373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242329294731358005516915 3363493942097037008275373)
                ·
                  refine ⟨1261310228286388878103265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3363493942097037008275373 1261310228286388878103265)
                  ·
                    refine ⟨945982671214791658577449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1261310228286388878103265 945982671214791658577449)
                    ·
                      refine ⟨709487003411093743933087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 945982671214791658577449 709487003411093743933087)
                      ·
                        rfl

theorem cell23_1381721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_1381721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381721 prefixEnd_1381721 := by exact prefixLift 1381721
  have htrace : WordTrace (prefixWord ++ tailWord_1381721) baseStart_1381721 baseEnd_1381721 := by
    simpa [prefixWord, tailWord_1381721, baseEnd_1381721] using wordTrace_append hprefix tailTrace_1381721
  have hstable : (prefixWord ++ tailWord_1381721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381721).length < 2 ^ (prefixWord ++ tailWord_1381721).sum := by decide
  have hdescent : baseEnd_1381721 < baseStart_1381721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381731 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 2, 4]
def baseStart_1381731 : Nat := 118140960795 + 1381731 * 2 ^ 59
def prefixEnd_1381731 : Nat := 4983230072969 + 3 ^ 40 * 1381731 * 2
def baseEnd_1381731 : Nat := 236497379405879568269347

theorem tailTrace_1381731 : CollatzResearch.WordTrace tailWord_1381731 prefixEnd_1381731 236497379405879568269347 := by
  unfold tailWord_1381731
  simp only [CollatzResearch.WordTrace]
  refine ⟨50395869757232042712513047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33597246504821361808342031 50395869757232042712513047)
  ·
    refine ⟨75593804635848064068769571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50395869757232042712513047 75593804635848064068769571)
    ·
      refine ⟨113390706953772096103154357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75593804635848064068769571 113390706953772096103154357)
      ·
        refine ⟨10630378776916134009670721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113390706953772096103154357 10630378776916134009670721)
        ·
          refine ⟨7972784082687100507253041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10630378776916134009670721 7972784082687100507253041)
          ·
            refine ⟨5979588062015325380439781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7972784082687100507253041 5979588062015325380439781)
            ·
              refine ⟨1121172761627873508832459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5979588062015325380439781 1121172761627873508832459)
              ·
                refine ⟨1681759142441810263248689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121172761627873508832459 1681759142441810263248689)
                ·
                  refine ⟨1261319356831357697436517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1681759142441810263248689 1261319356831357697436517)
                  ·
                    refine ⟨236497379405879568269347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1261319356831357697436517 236497379405879568269347)
                    ·
                      rfl

theorem cell23_1381731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 4].length) (baseStart_1381731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381731 prefixEnd_1381731 := by exact prefixLift 1381731
  have htrace : WordTrace (prefixWord ++ tailWord_1381731) baseStart_1381731 baseEnd_1381731 := by
    simpa [prefixWord, tailWord_1381731, baseEnd_1381731] using wordTrace_append hprefix tailTrace_1381731
  have hstable : (prefixWord ++ tailWord_1381731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381731).length < 2 ^ (prefixWord ++ tailWord_1381731).sum := by decide
  have hdescent : baseEnd_1381731 < baseStart_1381731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381738 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1381738 : Nat := 118140960795 + 1381738 * 2 ^ 59
def prefixEnd_1381738 : Nat := 4983230072969 + 3 ^ 40 * 1381738 * 2
def baseEnd_1381738 : Nat := 709495732582220177420509

theorem tailTrace_1381738 : CollatzResearch.WordTrace tailWord_1381738 prefixEnd_1381738 709495732582220177420509 := by
  unfold tailWord_1381738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599031267051670727004467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33597416712137788605345245 12599031267051670727004467)
  ·
    refine ⟨18898546900577506090506701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12599031267051670727004467 18898546900577506090506701)
    ·
      refine ⟨7086955087716564783940013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18898546900577506090506701 7086955087716564783940013)
      ·
        refine ⟨2657608157893711793977505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7086955087716564783940013 2657608157893711793977505)
        ·
          refine ⟨1993206118420283845483129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2657608157893711793977505 1993206118420283845483129)
          ·
            refine ⟨1494904588815212884112347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993206118420283845483129 1494904588815212884112347)
            ·
              refine ⟨2242356883222819326168521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494904588815212884112347 2242356883222819326168521)
              ·
                refine ⟨1681767662417114494626391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242356883222819326168521 1681767662417114494626391)
                ·
                  refine ⟨2522651493625671741939587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681767662417114494626391 2522651493625671741939587)
                  ·
                    refine ⟨3783977240438507612909381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522651493625671741939587 3783977240438507612909381)
                    ·
                      refine ⟨709495732582220177420509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3783977240438507612909381 709495732582220177420509)
                      ·
                        rfl

theorem cell23_1381738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1381738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381738 prefixEnd_1381738 := by exact prefixLift 1381738
  have htrace : WordTrace (prefixWord ++ tailWord_1381738) baseStart_1381738 baseEnd_1381738 := by
    simpa [prefixWord, tailWord_1381738, baseEnd_1381738] using wordTrace_append hprefix tailTrace_1381738
  have hstable : (prefixWord ++ tailWord_1381738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381738).length < 2 ^ (prefixWord ++ tailWord_1381738).sum := by decide
  have hdescent : baseEnd_1381738 < baseStart_1381738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381741 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1381741 : Nat := 118140960795 + 1381741 * 2 ^ 59
def prefixEnd_1381741 : Nat := 4983230072969 + 3 ^ 40 * 1381741 * 2
def baseEnd_1381741 : Nat := 709497273024183665682995

theorem tailTrace_1381741 : CollatzResearch.WordTrace tailWord_1381741 prefixEnd_1381741 709497273024183665682995 := by
  unfold tailWord_1381741
  simp only [CollatzResearch.WordTrace]
  refine ⟨50396234487195814420377077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33597489658130542946918051 50396234487195814420377077)
  ·
    refine ⟨4724646983174607601910351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50396234487195814420377077 4724646983174607601910351)
    ·
      refine ⟨7086970474761911402865527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4724646983174607601910351 7086970474761911402865527)
      ·
        refine ⟨10630455712142867104298291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086970474761911402865527 10630455712142867104298291)
        ·
          refine ⟨15945683568214300656447437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10630455712142867104298291 15945683568214300656447437)
          ·
            refine ⟨5979631338080362746167789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15945683568214300656447437 5979631338080362746167789)
            ·
              refine ⟨2242361751780136029812921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5979631338080362746167789 2242361751780136029812921)
              ·
                refine ⟨1681771313835102022359691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242361751780136029812921 1681771313835102022359691)
                ·
                  refine ⟨2522656970752653033539537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681771313835102022359691 2522656970752653033539537)
                  ·
                    refine ⟨1891992728064489775154653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2522656970752653033539537 1891992728064489775154653)
                    ·
                      refine ⟨709497273024183665682995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1891992728064489775154653 709497273024183665682995)
                      ·
                        rfl

theorem cell23_1381741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1381741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381741 prefixEnd_1381741 := by exact prefixLift 1381741
  have htrace : WordTrace (prefixWord ++ tailWord_1381741) baseStart_1381741 baseEnd_1381741 := by
    simpa [prefixWord, tailWord_1381741, baseEnd_1381741] using wordTrace_append hprefix tailTrace_1381741
  have hstable : (prefixWord ++ tailWord_1381741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381741).length < 2 ^ (prefixWord ++ tailWord_1381741).sum := by decide
  have hdescent : baseEnd_1381741 < baseStart_1381741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381771 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 3]
def baseStart_1381771 : Nat := 118140960795 + 1381771 * 2 ^ 59
def prefixEnd_1381771 : Nat := 4983230072969 + 3 ^ 40 * 1381771 * 2
def baseEnd_1381771 : Nat := 709512677443818548307857

theorem tailTrace_1381771 : CollatzResearch.WordTrace tailWord_1381771 prefixEnd_1381771 709512677443818548307857 := by
  unfold tailWord_1381771
  simp only [CollatzResearch.WordTrace]
  refine ⟨50397328677087129543969167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33598219118058086362646111 50397328677087129543969167)
  ·
    refine ⟨75595993015630694315953751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50397328677087129543969167 75595993015630694315953751)
    ·
      refine ⟨113393989523446041473930627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75595993015630694315953751 113393989523446041473930627)
      ·
        refine ⟨170090984285169062210895941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113393989523446041473930627 170090984285169062210895941)
        ·
          refine ⟨31892059553469199164542989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170090984285169062210895941 31892059553469199164542989)
          ·
            refine ⟨11959522332550949686703621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31892059553469199164542989 11959522332550949686703621)
            ·
              refine ⟨2242410437353303066256929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11959522332550949686703621 2242410437353303066256929)
              ·
                refine ⟨1681807828014977299692697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242410437353303066256929 1681807828014977299692697)
                ·
                  refine ⟨1261355871011232974769523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1681807828014977299692697 1261355871011232974769523)
                  ·
                    refine ⟨1892033806516849462154285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261355871011232974769523 1892033806516849462154285)
                    ·
                      refine ⟨709512677443818548307857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892033806516849462154285 709512677443818548307857)
                      ·
                        rfl

theorem cell23_1381771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 3].length) (baseStart_1381771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381771 prefixEnd_1381771 := by exact prefixLift 1381771
  have htrace : WordTrace (prefixWord ++ tailWord_1381771) baseStart_1381771 baseEnd_1381771 := by
    simpa [prefixWord, tailWord_1381771, baseEnd_1381771] using wordTrace_append hprefix tailTrace_1381771
  have hstable : (prefixWord ++ tailWord_1381771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381771).length < 2 ^ (prefixWord ++ tailWord_1381771).sum := by decide
  have hdescent : baseEnd_1381771 < baseStart_1381771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381778 : List Nat := [3, 2, 3, 3, 2, 1, 1, 8]
def baseStart_1381778 : Nat := 118140960795 + 1381778 * 2 ^ 59
def prefixEnd_1381778 : Nat := 4983230072969 + 3 ^ 40 * 1381778 * 2
def baseEnd_1381778 : Nat := 26278380437348148922975

theorem tailTrace_1381778 : CollatzResearch.WordTrace tailWord_1381778 prefixEnd_1381778 26278380437348148922975 := by
  unfold tailWord_1381778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599395997015442434868497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33598389325374513159649325 12599395997015442434868497)
  ·
    refine ⟨9449546997761581826151373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12599395997015442434868497 9449546997761581826151373)
    ·
      refine ⟨3543580124160593184806765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9449546997761581826151373 3543580124160593184806765)
      ·
        refine ⟨1328842546560222444302537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3543580124160593184806765 1328842546560222444302537)
        ·
          refine ⟨996631909920166833226903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328842546560222444302537 996631909920166833226903)
          ·
            refine ⟨1494947864880250249840355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996631909920166833226903 1494947864880250249840355)
            ·
              refine ⟨2242421797320375374760533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494947864880250249840355 2242421797320375374760533)
              ·
                refine ⟨26278380437348148922975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2242421797320375374760533 26278380437348148922975)
                ·
                  rfl

theorem cell23_1381778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_1381778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381778 prefixEnd_1381778 := by exact prefixLift 1381778
  have htrace : WordTrace (prefixWord ++ tailWord_1381778) baseStart_1381778 baseEnd_1381778 := by
    simpa [prefixWord, tailWord_1381778, baseEnd_1381778] using wordTrace_append hprefix tailTrace_1381778
  have hstable : (prefixWord ++ tailWord_1381778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381778).length < 2 ^ (prefixWord ++ tailWord_1381778).sum := by decide
  have hdescent : baseEnd_1381778 < baseStart_1381778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381788 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1381788 : Nat := 118140960795 + 1381788 * 2 ^ 59
def prefixEnd_1381788 : Nat := 4983230072969 + 3 ^ 40 * 1381788 * 2
def baseEnd_1381788 : Nat := 709521406614944981795279

theorem tailTrace_1381788 : CollatzResearch.WordTrace tailWord_1381788 prefixEnd_1381788 709521406614944981795279 := by
  unfold tailWord_1381788
  simp only [CollatzResearch.WordTrace]
  refine ⟨25198974359012770723669009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33598632478683694298225345 25198974359012770723669009)
  ·
    refine ⟨18899230769259578042751757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25198974359012770723669009 18899230769259578042751757)
    ·
      refine ⟨7087211538472341766031909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18899230769259578042751757 7087211538472341766031909)
      ·
        refine ⟨1328852163463564081130983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7087211538472341766031909 1328852163463564081130983)
        ·
          refine ⟨1993278245195346121696475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328852163463564081130983 1993278245195346121696475)
          ·
            refine ⟨2989917367793019182544713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993278245195346121696475 2989917367793019182544713)
            ·
              refine ⟨2242438025844764386908535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989917367793019182544713 2242438025844764386908535)
              ·
                refine ⟨3363657038767146580362803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242438025844764386908535 3363657038767146580362803)
                ·
                  refine ⟨5045485558150719870544205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363657038767146580362803 5045485558150719870544205)
                  ·
                    refine ⟨1892057084306519951454077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5045485558150719870544205 1892057084306519951454077)
                    ·
                      refine ⟨709521406614944981795279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892057084306519951454077 709521406614944981795279)
                      ·
                        rfl

theorem cell23_1381788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1381788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381788 prefixEnd_1381788 := by exact prefixLift 1381788
  have htrace : WordTrace (prefixWord ++ tailWord_1381788) baseStart_1381788 baseEnd_1381788 := by
    simpa [prefixWord, tailWord_1381788, baseEnd_1381788] using wordTrace_append hprefix tailTrace_1381788
  have hstable : (prefixWord ++ tailWord_1381788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381788).length < 2 ^ (prefixWord ++ tailWord_1381788).sum := by decide
  have hdescent : baseEnd_1381788 < baseStart_1381788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381797 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_1381797 : Nat := 118140960795 + 1381797 * 2 ^ 59
def prefixEnd_1381797 : Nat := 4983230072969 + 3 ^ 40 * 1381797 * 2
def baseEnd_1381797 : Nat := 709526027940835446582737

theorem tailTrace_1381797 : CollatzResearch.WordTrace tailWord_1381797 prefixEnd_1381797 709526027940835446582737 := by
  unfold tailWord_1381797
  simp only [CollatzResearch.WordTrace]
  refine ⟨50398276974992935984415645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33598851316661957322943763 50398276974992935984415645)
  ·
    refine ⟨18899353865622350994155867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50398276974992935984415645 18899353865622350994155867)
    ·
      refine ⟨28349030798433526491233801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18899353865622350994155867 28349030798433526491233801)
      ·
        refine ⟨21261773098825144868425351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28349030798433526491233801 21261773098825144868425351)
        ·
          refine ⟨31892659648237717302638027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21261773098825144868425351 31892659648237717302638027)
          ·
            refine ⟨47838989472356575953957041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31892659648237717302638027 47838989472356575953957041)
            ·
              refine ⟨35879242104267431965467781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47838989472356575953957041 35879242104267431965467781)
              ·
                refine ⟨6727357894550143493525209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35879242104267431965467781 6727357894550143493525209)
                ·
                  refine ⟨5045518420912607620143907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727357894550143493525209 5045518420912607620143907)
                  ·
                    refine ⟨7568277631368911430215861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045518420912607620143907 7568277631368911430215861)
                    ·
                      refine ⟨709526027940835446582737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7568277631368911430215861 709526027940835446582737)
                      ·
                        rfl

theorem cell23_1381797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_1381797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381797 prefixEnd_1381797 := by exact prefixLift 1381797
  have htrace : WordTrace (prefixWord ++ tailWord_1381797) baseStart_1381797 baseEnd_1381797 := by
    simpa [prefixWord, tailWord_1381797, baseEnd_1381797] using wordTrace_append hprefix tailTrace_1381797
  have hstable : (prefixWord ++ tailWord_1381797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381797).length < 2 ^ (prefixWord ++ tailWord_1381797).sum := by decide
  have hdescent : baseEnd_1381797 < baseStart_1381797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381834 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_1381834 : Nat := 118140960795 + 1381834 * 2 ^ 59
def prefixEnd_1381834 : Nat := 4983230072969 + 3 ^ 40 * 1381834 * 2
def baseEnd_1381834 : Nat := 78838336302783533535563

theorem tailTrace_1381834 : CollatzResearch.WordTrace tailWord_1381834 prefixEnd_1381834 78838336302783533535563 := by
  unfold tailWord_1381834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599906618964722825878139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33599750983905927535675037 12599906618964722825878139)
  ·
    refine ⟨18899859928447084238817209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12599906618964722825878139 18899859928447084238817209)
    ·
      refine ⟨14174894946335313179112907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18899859928447084238817209 14174894946335313179112907)
      ·
        refine ⟨21262342419502969768669361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14174894946335313179112907 21262342419502969768669361)
        ·
          refine ⟨15946756814627227326502021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21262342419502969768669361 15946756814627227326502021)
          ·
            refine ⟨2990016902742605123719129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15946756814627227326502021 2990016902742605123719129)
            ·
              refine ⟨2242512677056953842789347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2990016902742605123719129 2242512677056953842789347)
              ·
                refine ⟨3363769015585430764184021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242512677056953842789347 3363769015585430764184021)
                ·
                  refine ⟨78838336302783533535563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3363769015585430764184021 78838336302783533535563)
                  ·
                    rfl

theorem cell23_1381834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_1381834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381834 prefixEnd_1381834 := by exact prefixLift 1381834
  have htrace : WordTrace (prefixWord ++ tailWord_1381834) baseStart_1381834 baseEnd_1381834 := by
    simpa [prefixWord, tailWord_1381834, baseEnd_1381834] using wordTrace_append hprefix tailTrace_1381834
  have hstable : (prefixWord ++ tailWord_1381834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381834).length < 2 ^ (prefixWord ++ tailWord_1381834).sum := by decide
  have hdescent : baseEnd_1381834 < baseStart_1381834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381845 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1381845 : Nat := 118140960795 + 1381845 * 2 ^ 59
def prefixEnd_1381845 : Nat := 4983230072969 + 3 ^ 40 * 1381845 * 2
def baseEnd_1381845 : Nat := 709550675012251258782517

theorem tailTrace_1381845 : CollatzResearch.WordTrace tailWord_1381845 prefixEnd_1381845 709550675012251258782517 := by
  unfold tailWord_1381845
  simp only [CollatzResearch.WordTrace]
  refine ⟨50400027678819040182162989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33600018452546026788108659 50400027678819040182162989)
  ·
    refine ⟨18900010379557140068311121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50400027678819040182162989 18900010379557140068311121)
    ·
      refine ⟨14175007784667855051233341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18900010379557140068311121 14175007784667855051233341)
      ·
        refine ⟨5315627919250445644212503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14175007784667855051233341 5315627919250445644212503)
        ·
          refine ⟨7973441878875668466318755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315627919250445644212503 7973441878875668466318755)
          ·
            refine ⟨11960162818313502699478133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973441878875668466318755 11960162818313502699478133)
            ·
              refine ⟨1121265264216890878076075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11960162818313502699478133 1121265264216890878076075)
              ·
                refine ⟨1681897896325336317114113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121265264216890878076075 1681897896325336317114113)
                ·
                  refine ⟨1261423422244002237835585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1681897896325336317114113 1261423422244002237835585)
                  ·
                    refine ⟨946067566683001678376689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1261423422244002237835585 946067566683001678376689)
                    ·
                      refine ⟨709550675012251258782517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946067566683001678376689 709550675012251258782517)
                      ·
                        rfl

theorem cell23_1381845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1381845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381845 prefixEnd_1381845 := by exact prefixLift 1381845
  have htrace : WordTrace (prefixWord ++ tailWord_1381845) baseStart_1381845 baseEnd_1381845 := by
    simpa [prefixWord, tailWord_1381845, baseEnd_1381845] using wordTrace_append hprefix tailTrace_1381845
  have hstable : (prefixWord ++ tailWord_1381845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381845).length < 2 ^ (prefixWord ++ tailWord_1381845).sum := by decide
  have hdescent : baseEnd_1381845 < baseStart_1381845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381864 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1381864 : Nat := 118140960795 + 1381864 * 2 ^ 59
def prefixEnd_1381864 : Nat := 4983230072969 + 3 ^ 40 * 1381864 * 2
def baseEnd_1381864 : Nat := 236520143714895561481643

theorem tailTrace_1381864 : CollatzResearch.WordTrace tailWord_1381864 prefixEnd_1381864 236520143714895561481643 := by
  unfold tailWord_1381864
  simp only [CollatzResearch.WordTrace]
  refine ⟨25200360332875103213552323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33600480443833470951403097 25200360332875103213552323)
  ·
    refine ⟨37800540499312654820328485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25200360332875103213552323 37800540499312654820328485)
    ·
      refine ⟨7087601343621122778811591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37800540499312654820328485 7087601343621122778811591)
      ·
        refine ⟨10631402015431684168217387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087601343621122778811591 10631402015431684168217387)
        ·
          refine ⟨15947103023147526252326081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10631402015431684168217387 15947103023147526252326081)
          ·
            refine ⟨11960327267360644689244561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15947103023147526252326081 11960327267360644689244561)
            ·
              refine ⟨8970245450520483516933421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11960327267360644689244561 8970245450520483516933421)
              ·
                refine ⟨3363842043945181318850033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8970245450520483516933421 3363842043945181318850033)
                ·
                  refine ⟨2522881532958885989137525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3363842043945181318850033 2522881532958885989137525)
                  ·
                    refine ⟨236520143714895561481643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2522881532958885989137525 236520143714895561481643)
                    ·
                      rfl

theorem cell23_1381864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1381864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381864 prefixEnd_1381864 := by exact prefixLift 1381864
  have htrace : WordTrace (prefixWord ++ tailWord_1381864) baseStart_1381864 baseEnd_1381864 := by
    simpa [prefixWord, tailWord_1381864, baseEnd_1381864] using wordTrace_append hprefix tailTrace_1381864
  have hstable : (prefixWord ++ tailWord_1381864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381864).length < 2 ^ (prefixWord ++ tailWord_1381864).sum := by decide
  have hdescent : baseEnd_1381864 < baseStart_1381864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381884 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_1381884 : Nat := 118140960795 + 1381884 * 2 ^ 59
def prefixEnd_1381884 : Nat := 4983230072969 + 3 ^ 40 * 1381884 * 2
def baseEnd_1381884 : Nat := 709570700757776606194837

theorem tailTrace_1381884 : CollatzResearch.WordTrace tailWord_1381884 prefixEnd_1381884 709570700757776606194837 := by
  unfold tailWord_1381884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25200725062838874921416353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33600966750451833228555137 25200725062838874921416353)
  ·
    refine ⟨18900543797129156191062265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25200725062838874921416353 18900543797129156191062265)
    ·
      refine ⟨14175407847846867143296699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18900543797129156191062265 14175407847846867143296699)
      ·
        refine ⟨21263111771770300714945049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14175407847846867143296699 21263111771770300714945049)
        ·
          refine ⟨15947333828827725536208787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21263111771770300714945049 15947333828827725536208787)
          ·
            refine ⟨23921000743241588304313181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15947333828827725536208787 23921000743241588304313181)
            ·
              refine ⟨8970375278715595614117443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23921000743241588304313181 8970375278715595614117443)
              ·
                refine ⟨13455562918073393421176165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970375278715595614117443 13455562918073393421176165)
                ·
                  refine ⟨2522918047138761266470531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13455562918073393421176165 2522918047138761266470531)
                  ·
                    refine ⟨3784377070708141899705797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2522918047138761266470531 3784377070708141899705797)
                    ·
                      refine ⟨709570700757776606194837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3784377070708141899705797 709570700757776606194837)
                      ·
                        rfl

theorem cell23_1381884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_1381884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381884 prefixEnd_1381884 := by exact prefixLift 1381884
  have htrace : WordTrace (prefixWord ++ tailWord_1381884) baseStart_1381884 baseEnd_1381884 := by
    simpa [prefixWord, tailWord_1381884, baseEnd_1381884] using wordTrace_append hprefix tailTrace_1381884
  have hstable : (prefixWord ++ tailWord_1381884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381884).length < 2 ^ (prefixWord ++ tailWord_1381884).sum := by decide
  have hdescent : baseEnd_1381884 < baseStart_1381884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381887 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1381887 : Nat := 118140960795 + 1381887 * 2 ^ 59
def prefixEnd_1381887 : Nat := 4983230072969 + 3 ^ 40 * 1381887 * 2
def baseEnd_1381887 : Nat := 709572241199740094457323

theorem tailTrace_1381887 : CollatzResearch.WordTrace tailWord_1381887 prefixEnd_1381887 709572241199740094457323 := by
  unfold tailWord_1381887
  simp only [CollatzResearch.WordTrace]
  refine ⟨50401559544666881355191915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33601039696444587570127943 50401559544666881355191915)
  ·
    refine ⟨75602339317000322032787873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50401559544666881355191915 75602339317000322032787873)
    ·
      refine ⟨56701754487750241524590905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75602339317000322032787873 56701754487750241524590905)
      ·
        refine ⟨42526315865812681143443179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56701754487750241524590905 42526315865812681143443179)
        ·
          refine ⟨63789473798719021715164769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42526315865812681143443179 63789473798719021715164769)
          ·
            refine ⟨47842105349039266286373577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63789473798719021715164769 47842105349039266286373577)
            ·
              refine ⟨35881579011779449714780183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47842105349039266286373577 35881579011779449714780183)
              ·
                refine ⟨53822368517669174572170275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35881579011779449714780183 53822368517669174572170275)
                ·
                  refine ⟨80733552776503761858255413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53822368517669174572170275 80733552776503761858255413)
                  ·
                    refine ⟨7568770572797227674211445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80733552776503761858255413 7568770572797227674211445)
                    ·
                      refine ⟨709572241199740094457323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7568770572797227674211445 709572241199740094457323)
                      ·
                        rfl

theorem cell23_1381887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1381887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381887 prefixEnd_1381887 := by exact prefixLift 1381887
  have htrace : WordTrace (prefixWord ++ tailWord_1381887) baseStart_1381887 baseEnd_1381887 := by
    simpa [prefixWord, tailWord_1381887, baseEnd_1381887] using wordTrace_append hprefix tailTrace_1381887
  have hstable : (prefixWord ++ tailWord_1381887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381887).length < 2 ^ (prefixWord ++ tailWord_1381887).sum := by decide
  have hdescent : baseEnd_1381887 < baseStart_1381887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381921 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1381921 : Nat := 118140960795 + 1381921 * 2 ^ 59
def prefixEnd_1381921 : Nat := 4983230072969 + 3 ^ 40 * 1381921 * 2
def baseEnd_1381921 : Nat := 709589699541992961432167

theorem tailTrace_1381921 : CollatzResearch.WordTrace tailWord_1381921 prefixEnd_1381921 709589699541992961432167 := by
  unfold tailWord_1381921
  simp only [CollatzResearch.WordTrace]
  refine ⟨50402799626543705161929617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33601866417695803441286411 50402799626543705161929617)
  ·
    refine ⟨37802099719907778871447213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50402799626543705161929617 37802099719907778871447213)
    ·
      refine ⟨14175787394965417076792705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37802099719907778871447213 14175787394965417076792705)
      ·
        refine ⟨10631840546224062807594529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14175787394965417076792705 10631840546224062807594529)
        ·
          refine ⟨7973880409668047105695897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10631840546224062807594529 7973880409668047105695897)
          ·
            refine ⟨5980410307251035329271923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7973880409668047105695897 5980410307251035329271923)
            ·
              refine ⟨8970615460876552993907885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980410307251035329271923 8970615460876552993907885)
              ·
                refine ⟨3363980797828707372715457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8970615460876552993907885 3363980797828707372715457)
                ·
                  refine ⟨2522985598371530529536593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3363980797828707372715457 2522985598371530529536593)
                  ·
                    refine ⟨1892239198778647897152445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2522985598371530529536593 1892239198778647897152445)
                    ·
                      refine ⟨709589699541992961432167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892239198778647897152445 709589699541992961432167)
                      ·
                        rfl

theorem cell23_1381921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1381921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381921 prefixEnd_1381921 := by exact prefixLift 1381921
  have htrace : WordTrace (prefixWord ++ tailWord_1381921) baseStart_1381921 baseEnd_1381921 := by
    simpa [prefixWord, tailWord_1381921, baseEnd_1381921] using wordTrace_append hprefix tailTrace_1381921
  have hstable : (prefixWord ++ tailWord_1381921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381921).length < 2 ^ (prefixWord ++ tailWord_1381921).sum := by decide
  have hdescent : baseEnd_1381921 < baseStart_1381921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381941 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 6]
def baseStart_1381941 : Nat := 118140960795 + 1381941 * 2 ^ 59
def prefixEnd_1381941 : Nat := 4983230072969 + 3 ^ 40 * 1381941 * 2
def baseEnd_1381941 : Nat := 78844441017231431464675

theorem tailTrace_1381941 : CollatzResearch.WordTrace tailWord_1381941 prefixEnd_1381941 78844441017231431464675 := by
  unfold tailWord_1381941
  simp only [CollatzResearch.WordTrace]
  refine ⟨50403529086471248577657677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33602352724314165718438451 50403529086471248577657677)
  ·
    refine ⟨18901323407426718216621629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50403529086471248577657677 18901323407426718216621629)
    ·
      refine ⟨7087996277785019331233111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18901323407426718216621629 7087996277785019331233111)
      ·
        refine ⟨10631994416677528996849667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087996277785019331233111 10631994416677528996849667)
        ·
          refine ⟨15947991625016293495274501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10631994416677528996849667 15947991625016293495274501)
          ·
            refine ⟨2990248429690555030363969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15947991625016293495274501 2990248429690555030363969)
            ·
              refine ⟨2242686322267916272772977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2990248429690555030363969 2242686322267916272772977)
              ·
                refine ⟨1682014741700937204579733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242686322267916272772977 1682014741700937204579733)
                ·
                  refine ⟨78844441017231431464675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1682014741700937204579733 78844441017231431464675)
                  ·
                    rfl

theorem cell23_1381941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_1381941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381941 prefixEnd_1381941 := by exact prefixLift 1381941
  have htrace : WordTrace (prefixWord ++ tailWord_1381941) baseStart_1381941 baseEnd_1381941 := by
    simpa [prefixWord, tailWord_1381941, baseEnd_1381941] using wordTrace_append hprefix tailTrace_1381941
  have hstable : (prefixWord ++ tailWord_1381941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381941).length < 2 ^ (prefixWord ++ tailWord_1381941).sum := by decide
  have hdescent : baseEnd_1381941 < baseStart_1381941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381945 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 1, 4]
def baseStart_1381945 : Nat := 118140960795 + 1381945 * 2 ^ 59
def prefixEnd_1381945 : Nat := 4983230072969 + 3 ^ 40 * 1381945 * 2
def baseEnd_1381945 : Nat := 236534007692566955844019

theorem tailTrace_1381945 : CollatzResearch.WordTrace tailWord_1381945 prefixEnd_1381945 236534007692566955844019 := by
  unfold tailWord_1381945
  simp only [CollatzResearch.WordTrace]
  refine ⟨50403674978456757260803289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33602449985637838173868859 50403674978456757260803289)
  ·
    refine ⟨37802756233842567945602467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50403674978456757260803289 37802756233842567945602467)
    ·
      refine ⟨56704134350763851918403701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37802756233842567945602467 56704134350763851918403701)
      ·
        refine ⟨5316012595384111117350347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56704134350763851918403701 5316012595384111117350347)
        ·
          refine ⟨7974018893076166676025521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316012595384111117350347 7974018893076166676025521)
          ·
            refine ⟨5980514169807125007019141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7974018893076166676025521 5980514169807125007019141)
            ·
              refine ⟨1121346406838835938816089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5980514169807125007019141 1121346406838835938816089)
              ·
                refine ⟨841009805129126954112067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121346406838835938816089 841009805129126954112067)
                ·
                  refine ⟨1261514707693690431168101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841009805129126954112067 1261514707693690431168101)
                  ·
                    refine ⟨236534007692566955844019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1261514707693690431168101 236534007692566955844019)
                    ·
                      rfl

theorem cell23_1381945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 4].length) (baseStart_1381945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381945 prefixEnd_1381945 := by exact prefixLift 1381945
  have htrace : WordTrace (prefixWord ++ tailWord_1381945) baseStart_1381945 baseEnd_1381945 := by
    simpa [prefixWord, tailWord_1381945, baseEnd_1381945] using wordTrace_append hprefix tailTrace_1381945
  have hstable : (prefixWord ++ tailWord_1381945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381945).length < 2 ^ (prefixWord ++ tailWord_1381945).sum := by decide
  have hdescent : baseEnd_1381945 < baseStart_1381945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381961 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 4, 3, 2]
def baseStart_1381961 : Nat := 118140960795 + 1381961 * 2 ^ 59
def prefixEnd_1381961 : Nat := 4983230072969 + 3 ^ 40 * 1381961 * 2
def baseEnd_1381961 : Nat := 709610238768172804931983

theorem tailTrace_1381961 : CollatzResearch.WordTrace tailWord_1381961 prefixEnd_1381961 709610238768172804931983 := by
  unfold tailWord_1381961
  simp only [CollatzResearch.WordTrace]
  refine ⟨50404258546398791993385737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33602839030932527995590491 50404258546398791993385737)
  ·
    refine ⟨37803193909799093995039303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50404258546398791993385737 37803193909799093995039303)
    ·
      refine ⟨56704790864698640992558955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37803193909799093995039303 56704790864698640992558955)
      ·
        refine ⟨85057186297047961488838433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56704790864698640992558955 85057186297047961488838433)
        ·
          refine ⟨63792889722785971116628825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85057186297047961488838433 63792889722785971116628825)
          ·
            refine ⟨47844667292089478337471619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63792889722785971116628825 47844667292089478337471619)
            ·
              refine ⟨71767000938134217506207429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47844667292089478337471619 71767000938134217506207429)
              ·
                refine ⟨13456312675900165782413893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71767000938134217506207429 13456312675900165782413893)
                ·
                  refine ⟨2523058626731281084202605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13456312675900165782413893 2523058626731281084202605)
                  ·
                    refine ⟨946146985024230406575977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523058626731281084202605 946146985024230406575977)
                    ·
                      refine ⟨709610238768172804931983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946146985024230406575977 709610238768172804931983)
                      ·
                        rfl

theorem cell23_1381961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 3, 2].length) (baseStart_1381961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381961 prefixEnd_1381961 := by exact prefixLift 1381961
  have htrace : WordTrace (prefixWord ++ tailWord_1381961) baseStart_1381961 baseEnd_1381961 := by
    simpa [prefixWord, tailWord_1381961, baseEnd_1381961] using wordTrace_append hprefix tailTrace_1381961
  have hstable : (prefixWord ++ tailWord_1381961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381961).length < 2 ^ (prefixWord ++ tailWord_1381961).sum := by decide
  have hdescent : baseEnd_1381961 < baseStart_1381961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381985 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_1381985 : Nat := 118140960795 + 1381985 * 2 ^ 59
def prefixEnd_1381985 : Nat := 4983230072969 + 3 ^ 40 * 1381985 * 2
def baseEnd_1381985 : Nat := 709622562303880711031873

theorem tailTrace_1381985 : CollatzResearch.WordTrace tailWord_1381985 prefixEnd_1381985 709622562303880711031873 := by
  unfold tailWord_1381985
  simp only [CollatzResearch.WordTrace]
  refine ⟨50405133898311844092259409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33603422598874562728172939 50405133898311844092259409)
  ·
    refine ⟨37803850423733883069194557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50405133898311844092259409 37803850423733883069194557)
    ·
      refine ⟨14176443908900206150947959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37803850423733883069194557 14176443908900206150947959)
      ·
        refine ⟨21264665863350309226421939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14176443908900206150947959 21264665863350309226421939)
        ·
          refine ⟨31896998795025463839632909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21264665863350309226421939 31896998795025463839632909)
          ·
            refine ⟨11961374548134548939862341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31896998795025463839632909 11961374548134548939862341)
            ·
              refine ⟨2242757727775227926224189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11961374548134548939862341 2242757727775227926224189)
              ·
                refine ⟨841034147915710472334071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2242757727775227926224189 841034147915710472334071)
                ·
                  refine ⟨1261551221873565708501107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841034147915710472334071 1261551221873565708501107)
                  ·
                    refine ⟨1892326832810348562751661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261551221873565708501107 1892326832810348562751661)
                    ·
                      refine ⟨709622562303880711031873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892326832810348562751661 709622562303880711031873)
                      ·
                        rfl

theorem cell23_1381985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_1381985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381985 prefixEnd_1381985 := by exact prefixLift 1381985
  have htrace : WordTrace (prefixWord ++ tailWord_1381985) baseStart_1381985 baseEnd_1381985 := by
    simpa [prefixWord, tailWord_1381985, baseEnd_1381985] using wordTrace_append hprefix tailTrace_1381985
  have hstable : (prefixWord ++ tailWord_1381985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381985).length < 2 ^ (prefixWord ++ tailWord_1381985).sum := by decide
  have hdescent : baseEnd_1381985 < baseStart_1381985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1381988 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_1381988 : Nat := 118140960795 + 1381988 * 2 ^ 59
def prefixEnd_1381988 : Nat := 4983230072969 + 3 ^ 40 * 1381988 * 2
def baseEnd_1381988 : Nat := 236541367581948066431453

theorem tailTrace_1381988 : CollatzResearch.WordTrace tailWord_1381988 prefixEnd_1381988 236541367581948066431453 := by
  unfold tailWord_1381988
  simp only [CollatzResearch.WordTrace]
  refine ⟨25202621658650487802309309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33603495544867317069745745 25202621658650487802309309)
  ·
    refine ⟨9450983121993932925865991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25202621658650487802309309 9450983121993932925865991)
    ·
      refine ⟨14176474682990899388798987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450983121993932925865991 14176474682990899388798987)
      ·
        refine ⟨21264712024486349083198481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14176474682990899388798987 21264712024486349083198481)
        ·
          refine ⟨15948534018364761812398861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21264712024486349083198481 15948534018364761812398861)
          ·
            refine ⟨5980700256886785679649573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15948534018364761812398861 5980700256886785679649573)
            ·
              refine ⟨1121381298166272314934295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5980700256886785679649573 1121381298166272314934295)
              ·
                refine ⟨1682071947249408472401443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121381298166272314934295 1682071947249408472401443)
                ·
                  refine ⟨2523107920874112708602165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682071947249408472401443 2523107920874112708602165)
                  ·
                    refine ⟨236541367581948066431453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2523107920874112708602165 236541367581948066431453)
                    ·
                      rfl

theorem cell23_1381988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_1381988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1381988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1381988 prefixEnd_1381988 := by exact prefixLift 1381988
  have htrace : WordTrace (prefixWord ++ tailWord_1381988) baseStart_1381988 baseEnd_1381988 := by
    simpa [prefixWord, tailWord_1381988, baseEnd_1381988] using wordTrace_append hprefix tailTrace_1381988
  have hstable : (prefixWord ++ tailWord_1381988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1381988).length < 2 ^ (prefixWord ++ tailWord_1381988).sum := by decide
  have hdescent : baseEnd_1381988 < baseStart_1381988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1381988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382028 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1382028 : Nat := 118140960795 + 1382028 * 2 ^ 59
def prefixEnd_1382028 : Nat := 4983230072969 + 3 ^ 40 * 1382028 * 2
def baseEnd_1382028 : Nat := 709644641972024042794175

theorem tailTrace_1382028 : CollatzResearch.WordTrace tailWord_1382028 prefixEnd_1382028 709644641972024042794175 := by
  unfold tailWord_1382028
  simp only [CollatzResearch.WordTrace]
  refine ⟨25203351118578031218037369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33604468158104041624049825 25203351118578031218037369)
  ·
    refine ⟨18902513338933523413528027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25203351118578031218037369 18902513338933523413528027)
    ·
      refine ⟨28353770008400285120292041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18902513338933523413528027 28353770008400285120292041)
      ·
        refine ⟨21265327506300213840219031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28353770008400285120292041 21265327506300213840219031)
        ·
          refine ⟨31897991259450320760328547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21265327506300213840219031 31897991259450320760328547)
          ·
            refine ⟨47846986889175481140492821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31897991259450320760328547 47846986889175481140492821)
            ·
              refine ⟨2242827510430100678460601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47846986889175481140492821 2242827510430100678460601)
              ·
                refine ⟨1682120632822575508845451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242827510430100678460601 1682120632822575508845451)
                ·
                  refine ⟨2523180949233863263268177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682120632822575508845451 2523180949233863263268177)
                  ·
                    refine ⟨1892385711925397447451133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2523180949233863263268177 1892385711925397447451133)
                    ·
                      refine ⟨709644641972024042794175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892385711925397447451133 709644641972024042794175)
                      ·
                        rfl

theorem cell23_1382028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1382028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382028 prefixEnd_1382028 := by exact prefixLift 1382028
  have htrace : WordTrace (prefixWord ++ tailWord_1382028) baseStart_1382028 baseEnd_1382028 := by
    simpa [prefixWord, tailWord_1382028, baseEnd_1382028] using wordTrace_append hprefix tailTrace_1382028
  have hstable : (prefixWord ++ tailWord_1382028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382028).length < 2 ^ (prefixWord ++ tailWord_1382028).sum := by decide
  have hdescent : baseEnd_1382028 < baseStart_1382028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382036 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1382036 : Nat := 118140960795 + 1382036 * 2 ^ 59
def prefixEnd_1382036 : Nat := 4983230072969 + 3 ^ 40 * 1382036 * 2
def baseEnd_1382036 : Nat := 709648749817260011494139

theorem tailTrace_1382036 : CollatzResearch.WordTrace tailWord_1382036 prefixEnd_1382036 709648749817260011494139 := by
  unfold tailWord_1382036
  simp only [CollatzResearch.WordTrace]
  refine ⟨25203497010563539901182981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33604662680751386534910641 25203497010563539901182981)
  ·
    refine ⟨4725655689480663731471809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25203497010563539901182981 4725655689480663731471809)
    ·
      refine ⟨3544241767110497798603857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725655689480663731471809 3544241767110497798603857)
      ·
        refine ⟨2658181325332873348952893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3544241767110497798603857 2658181325332873348952893)
        ·
          refine ⟨996817996999827505857335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2658181325332873348952893 996817996999827505857335)
          ·
            refine ⟨1495226995499741258786003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996817996999827505857335 1495226995499741258786003)
            ·
              refine ⟨2242840493249611888179005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495226995499741258786003 2242840493249611888179005)
              ·
                refine ⟨841065184968604458067127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2242840493249611888179005 841065184968604458067127)
                ·
                  refine ⟨1261597777452906687100691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841065184968604458067127 1261597777452906687100691)
                  ·
                    refine ⟨1892396666179360030651037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261597777452906687100691 1892396666179360030651037)
                    ·
                      refine ⟨709648749817260011494139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892396666179360030651037 709648749817260011494139)
                      ·
                        rfl

theorem cell23_1382036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1382036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382036 prefixEnd_1382036 := by exact prefixLift 1382036
  have htrace : WordTrace (prefixWord ++ tailWord_1382036) baseStart_1382036 baseEnd_1382036 := by
    simpa [prefixWord, tailWord_1382036, baseEnd_1382036] using wordTrace_append hprefix tailTrace_1382036
  have hstable : (prefixWord ++ tailWord_1382036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382036).length < 2 ^ (prefixWord ++ tailWord_1382036).sum := by decide
  have hdescent : baseEnd_1382036 < baseStart_1382036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382061 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1382061 : Nat := 118140960795 + 1382061 * 2 ^ 59
def prefixEnd_1382061 : Nat := 4983230072969 + 3 ^ 40 * 1382061 * 2
def baseEnd_1382061 : Nat := 236553862277874137893841

theorem tailTrace_1382061 : CollatzResearch.WordTrace tailWord_1382061 prefixEnd_1382061 236553862277874137893841 := by
  unfold tailWord_1382061
  simp only [CollatzResearch.WordTrace]
  refine ⟨50407905846036509072026037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33605270564024339381350691 50407905846036509072026037)
  ·
    refine ⟨4725741173065922725502441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50407905846036509072026037 4725741173065922725502441)
    ·
      refine ⟨3544305879799442044126831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725741173065922725502441 3544305879799442044126831)
      ·
        refine ⟨5316458819699163066190247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544305879799442044126831 5316458819699163066190247)
        ·
          refine ⟨7974688229548744599285371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316458819699163066190247 7974688229548744599285371)
          ·
            refine ⟨11962032344323116898928057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974688229548744599285371 11962032344323116898928057)
            ·
              refine ⟨8971524258242337674196043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11962032344323116898928057 8971524258242337674196043)
              ·
                refine ⟨13457286387363506511294065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8971524258242337674196043 13457286387363506511294065)
                ·
                  refine ⟨10092964790522629883470549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13457286387363506511294065 10092964790522629883470549)
                  ·
                    refine ⟨236553862277874137893841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10092964790522629883470549 236553862277874137893841)
                    ·
                      rfl

theorem cell23_1382061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1382061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382061 prefixEnd_1382061 := by exact prefixLift 1382061
  have htrace : WordTrace (prefixWord ++ tailWord_1382061) baseStart_1382061 baseEnd_1382061 := by
    simpa [prefixWord, tailWord_1382061, baseEnd_1382061] using wordTrace_append hprefix tailTrace_1382061
  have hstable : (prefixWord ++ tailWord_1382061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382061).length < 2 ^ (prefixWord ++ tailWord_1382061).sum := by decide
  have hdescent : baseEnd_1382061 < baseStart_1382061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382069 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1382069 : Nat := 118140960795 + 1382069 * 2 ^ 59
def prefixEnd_1382069 : Nat := 4983230072969 + 3 ^ 40 * 1382069 * 2
def baseEnd_1382069 : Nat := 236555231559619460793829

theorem tailTrace_1382069 : CollatzResearch.WordTrace tailWord_1382069 prefixEnd_1382069 236555231559619460793829 := by
  unfold tailWord_1382069
  simp only [CollatzResearch.WordTrace]
  refine ⟨50408197630007526438317261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33605465086671684292211507 50408197630007526438317261)
  ·
    refine ⟨18903074111252822414368973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50408197630007526438317261 18903074111252822414368973)
    ·
      refine ⟨7088652791719808405388365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18903074111252822414368973 7088652791719808405388365)
      ·
        refine ⟨2658244796894928152020637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7088652791719808405388365 2658244796894928152020637)
        ·
          refine ⟨996841798835598057007739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2658244796894928152020637 996841798835598057007739)
          ·
            refine ⟨1495262698253397085511609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996841798835598057007739 1495262698253397085511609)
            ·
              refine ⟨1121447023690047814133707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495262698253397085511609 1121447023690047814133707)
              ·
                refine ⟨1682170535535071721200561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121447023690047814133707 1682170535535071721200561)
                ·
                  refine ⟨1261627901651303790900421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1682170535535071721200561 1261627901651303790900421)
                  ·
                    refine ⟨236555231559619460793829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1261627901651303790900421 236555231559619460793829)
                    ·
                      rfl

theorem cell23_1382069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1382069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382069 prefixEnd_1382069 := by exact prefixLift 1382069
  have htrace : WordTrace (prefixWord ++ tailWord_1382069) baseStart_1382069 baseEnd_1382069 := by
    simpa [prefixWord, tailWord_1382069, baseEnd_1382069] using wordTrace_append hprefix tailTrace_1382069
  have hstable : (prefixWord ++ tailWord_1382069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382069).length < 2 ^ (prefixWord ++ tailWord_1382069).sum := by decide
  have hdescent : baseEnd_1382069 < baseStart_1382069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382109 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1382109 : Nat := 118140960795 + 1382109 * 2 ^ 59
def prefixEnd_1382109 : Nat := 4983230072969 + 3 ^ 40 * 1382109 * 2
def baseEnd_1382109 : Nat := 709686233905038225881303

theorem tailTrace_1382109 : CollatzResearch.WordTrace tailWord_1382109 prefixEnd_1382109 709686233905038225881303 := by
  unfold tailWord_1382109
  simp only [CollatzResearch.WordTrace]
  refine ⟨50409656549862613269773381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33606437699908408846515587 50409656549862613269773381)
  ·
    refine ⟨9451810603099239988082509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50409656549862613269773381 9451810603099239988082509)
    ·
      refine ⟨3544428976162214995530941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9451810603099239988082509 3544428976162214995530941)
      ·
        refine ⟨1329160866060830623324103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3544428976162214995530941 1329160866060830623324103)
        ·
          refine ⟨1993741299091245934986155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329160866060830623324103 1993741299091245934986155)
          ·
            refine ⟨2990611948636868902479233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993741299091245934986155 2990611948636868902479233)
            ·
              refine ⟨2242958961477651676859425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2990611948636868902479233 2242958961477651676859425)
              ·
                refine ⟨1682219221108238757644569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242958961477651676859425 1682219221108238757644569)
                ·
                  refine ⟨1261664415831179068233427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1682219221108238757644569 1261664415831179068233427)
                  ·
                    refine ⟨1892496623746768602350141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261664415831179068233427 1892496623746768602350141)
                    ·
                      refine ⟨709686233905038225881303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892496623746768602350141 709686233905038225881303)
                      ·
                        rfl

theorem cell23_1382109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1382109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382109 prefixEnd_1382109 := by exact prefixLift 1382109
  have htrace : WordTrace (prefixWord ++ tailWord_1382109) baseStart_1382109 baseEnd_1382109 := by
    simpa [prefixWord, tailWord_1382109, baseEnd_1382109] using wordTrace_append hprefix tailTrace_1382109
  have hstable : (prefixWord ++ tailWord_1382109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382109).length < 2 ^ (prefixWord ++ tailWord_1382109).sum := by decide
  have hdescent : baseEnd_1382109 < baseStart_1382109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382111 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1382111 : Nat := 118140960795 + 1382111 * 2 ^ 59
def prefixEnd_1382111 : Nat := 4983230072969 + 3 ^ 40 * 1382111 * 2
def baseEnd_1382111 : Nat := 709687260866347218056293

theorem tailTrace_1382111 : CollatzResearch.WordTrace tailWord_1382111 prefixEnd_1382111 709687260866347218056293 := by
  unfold tailWord_1382111
  simp only [CollatzResearch.WordTrace]
  refine ⟨50409729495855367611346187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33606486330570245074230791 50409729495855367611346187)
  ·
    refine ⟨75614594243783051417019281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50409729495855367611346187 75614594243783051417019281)
    ·
      refine ⟨56710945682837288562764461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75614594243783051417019281 56710945682837288562764461)
      ·
        refine ⟨21266604631063983211036673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56710945682837288562764461 21266604631063983211036673)
        ·
          refine ⟨15949953473297987408277505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21266604631063983211036673 15949953473297987408277505)
          ·
            refine ⟨11962465104973490556208129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15949953473297987408277505 11962465104973490556208129)
            ·
              refine ⟨8971848828730117917156097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11962465104973490556208129 8971848828730117917156097)
              ·
                refine ⟨6728886621547588437867073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8971848828730117917156097 6728886621547588437867073)
                ·
                  refine ⟨5046664966160691328400305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728886621547588437867073 5046664966160691328400305)
                  ·
                    refine ⟨3784998724620518496300229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046664966160691328400305 3784998724620518496300229)
                    ·
                      refine ⟨709687260866347218056293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3784998724620518496300229 709687260866347218056293)
                      ·
                        rfl

theorem cell23_1382111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1382111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382111 prefixEnd_1382111 := by exact prefixLift 1382111
  have htrace : WordTrace (prefixWord ++ tailWord_1382111) baseStart_1382111 baseEnd_1382111 := by
    simpa [prefixWord, tailWord_1382111, baseEnd_1382111] using wordTrace_append hprefix tailTrace_1382111
  have hstable : (prefixWord ++ tailWord_1382111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382111).length < 2 ^ (prefixWord ++ tailWord_1382111).sum := by decide
  have hdescent : baseEnd_1382111 < baseStart_1382111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382131 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 3]
def baseStart_1382131 : Nat := 118140960795 + 1382131 * 2 ^ 59
def prefixEnd_1382131 : Nat := 4983230072969 + 3 ^ 40 * 1382131 * 2
def baseEnd_1382131 : Nat := 709697530479437139806201

theorem tailTrace_1382131 : CollatzResearch.WordTrace tailWord_1382131 prefixEnd_1382131 709697530479437139806201 := by
  unfold tailWord_1382131
  simp only [CollatzResearch.WordTrace]
  refine ⟨50410458955782911027074247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33606972637188607351382831 50410458955782911027074247)
  ·
    refine ⟨75615688433674366540611371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50410458955782911027074247 75615688433674366540611371)
    ·
      refine ⟨113423532650511549810917057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75615688433674366540611371 113423532650511549810917057)
      ·
        refine ⟨85067649487883662358187793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113423532650511549810917057 85067649487883662358187793)
        ·
          refine ⟨63800737115912746768640845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85067649487883662358187793 63800737115912746768640845)
          ·
            refine ⟨23925276418467280038240317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63800737115912746768640845 23925276418467280038240317)
            ·
              refine ⟨8971978656925230014340119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23925276418467280038240317 8971978656925230014340119)
              ·
                refine ⟨13457967985387845021510179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8971978656925230014340119 13457967985387845021510179)
                ·
                  refine ⟨20186951978081767532265269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13457967985387845021510179 20186951978081767532265269)
                  ·
                    refine ⟨1892526747945165706149869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20186951978081767532265269 1892526747945165706149869)
                    ·
                      refine ⟨709697530479437139806201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892526747945165706149869 709697530479437139806201)
                      ·
                        rfl

theorem cell23_1382131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_1382131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382131 prefixEnd_1382131 := by exact prefixLift 1382131
  have htrace : WordTrace (prefixWord ++ tailWord_1382131) baseStart_1382131 baseEnd_1382131 := by
    simpa [prefixWord, tailWord_1382131, baseEnd_1382131] using wordTrace_append hprefix tailTrace_1382131
  have hstable : (prefixWord ++ tailWord_1382131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382131).length < 2 ^ (prefixWord ++ tailWord_1382131).sum := by decide
  have hdescent : baseEnd_1382131 < baseStart_1382131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382211 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 8]
def baseStart_1382211 : Nat := 118140960795 + 1382211 * 2 ^ 59
def prefixEnd_1382211 : Nat := 4983230072969 + 3 ^ 40 * 1382211 * 2
def baseEnd_1382211 : Nat := 78859845436866314089537

theorem tailTrace_1382211 : CollatzResearch.WordTrace tailWord_1382211 prefixEnd_1382211 78859845436866314089537 := by
  unfold tailWord_1382211
  simp only [CollatzResearch.WordTrace]
  refine ⟨50413376795493084689986487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33608917863662056459990991 50413376795493084689986487)
  ·
    refine ⟨75620065193239627034979731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50413376795493084689986487 75620065193239627034979731)
    ·
      refine ⟨113430097789859440552469597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75620065193239627034979731 113430097789859440552469597)
      ·
        refine ⟨42536286671197290207176099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113430097789859440552469597 42536286671197290207176099)
        ·
          refine ⟨63804430006795935310764149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42536286671197290207176099 63804430006795935310764149)
          ·
            refine ⟨5981665313137118935384139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63804430006795935310764149 5981665313137118935384139)
            ·
              refine ⟨8972497969705678403076209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5981665313137118935384139 8972497969705678403076209)
              ·
                refine ⟨6729373477279258802307157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8972497969705678403076209 6729373477279258802307157)
                ·
                  refine ⟨78859845436866314089537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6729373477279258802307157 78859845436866314089537)
                  ·
                    rfl

theorem cell23_1382211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 8].length) (baseStart_1382211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382211 prefixEnd_1382211 := by exact prefixLift 1382211
  have htrace : WordTrace (prefixWord ++ tailWord_1382211) baseStart_1382211 baseEnd_1382211 := by
    simpa [prefixWord, tailWord_1382211, baseEnd_1382211] using wordTrace_append hprefix tailTrace_1382211
  have hstable : (prefixWord ++ tailWord_1382211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382211).length < 2 ^ (prefixWord ++ tailWord_1382211).sum := by decide
  have hdescent : baseEnd_1382211 < baseStart_1382211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382225 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_1382225 : Nat := 118140960795 + 1382225 * 2 ^ 59
def prefixEnd_1382225 : Nat := 4983230072969 + 3 ^ 40 * 1382225 * 2
def baseEnd_1382225 : Nat := 709745797660959772030769

theorem tailTrace_1382225 : CollatzResearch.WordTrace tailWord_1382225 prefixEnd_1382225 709745797660959772030769 := by
  unfold tailWord_1382225
  simp only [CollatzResearch.WordTrace]
  refine ⟨50413887417442365080996129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33609258278294910053997419 50413887417442365080996129)
  ·
    refine ⟨37810415563081773810747097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50413887417442365080996129 37810415563081773810747097)
    ·
      refine ⟨28357811672311330358060323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37810415563081773810747097 28357811672311330358060323)
      ·
        refine ⟨42536717508466995537090485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28357811672311330358060323 42536717508466995537090485)
        ·
          refine ⟨3987817266418780831602233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42536717508466995537090485 3987817266418780831602233)
          ·
            refine ⟨2990862949814085623701675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3987817266418780831602233 2990862949814085623701675)
            ·
              refine ⟨4486294424721128435552513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990862949814085623701675 4486294424721128435552513)
              ·
                refine ⟨3364720818540846326664385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4486294424721128435552513 3364720818540846326664385)
                ·
                  refine ⟨2523540613905634744998289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3364720818540846326664385 2523540613905634744998289)
                  ·
                    refine ⟨1892655460429226058748717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2523540613905634744998289 1892655460429226058748717)
                    ·
                      refine ⟨709745797660959772030769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892655460429226058748717 709745797660959772030769)
                      ·
                        rfl

theorem cell23_1382225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_1382225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382225 prefixEnd_1382225 := by exact prefixLift 1382225
  have htrace : WordTrace (prefixWord ++ tailWord_1382225) baseStart_1382225 baseEnd_1382225 := by
    simpa [prefixWord, tailWord_1382225, baseEnd_1382225] using wordTrace_append hprefix tailTrace_1382225
  have hstable : (prefixWord ++ tailWord_1382225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382225).length < 2 ^ (prefixWord ++ tailWord_1382225).sum := by decide
  have hdescent : baseEnd_1382225 < baseStart_1382225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382228 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 8]
def baseStart_1382228 : Nat := 118140960795 + 1382228 * 2 ^ 59
def prefixEnd_1382228 : Nat := 4983230072969 + 3 ^ 40 * 1382228 * 2
def baseEnd_1382228 : Nat := 78860815344769251143695

theorem tailTrace_1382228 : CollatzResearch.WordTrace tailWord_1382228 prefixEnd_1382228 78860815344769251143695 := by
  unfold tailWord_1382228
  simp only [CollatzResearch.WordTrace]
  refine ⟨25206998418215748296677669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33609331224287664395570225 25206998418215748296677669)
  ·
    refine ⟨4726312203415452805627063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25206998418215748296677669 4726312203415452805627063)
    ·
      refine ⟨7089468305123179208440595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726312203415452805627063 7089468305123179208440595)
      ·
        refine ⟨10634202457684768812660893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089468305123179208440595 10634202457684768812660893)
        ·
          refine ⟨3987825921631788304747835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10634202457684768812660893 3987825921631788304747835)
          ·
            refine ⟨5981738882447682457121753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987825921631788304747835 5981738882447682457121753)
            ·
              refine ⟨4486304161835761842841315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5981738882447682457121753 4486304161835761842841315)
              ·
                refine ⟨6729456242753642764261973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486304161835761842841315 6729456242753642764261973)
                ·
                  refine ⟨78860815344769251143695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6729456242753642764261973 78860815344769251143695)
                  ·
                    rfl

theorem cell23_1382228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_1382228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382228 prefixEnd_1382228 := by exact prefixLift 1382228
  have htrace : WordTrace (prefixWord ++ tailWord_1382228) baseStart_1382228 baseEnd_1382228 := by
    simpa [prefixWord, tailWord_1382228, baseEnd_1382228] using wordTrace_append hprefix tailTrace_1382228
  have hstable : (prefixWord ++ tailWord_1382228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382228).length < 2 ^ (prefixWord ++ tailWord_1382228).sum := by decide
  have hdescent : baseEnd_1382228 < baseStart_1382228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382272 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 1, 1, 3]
def baseStart_1382272 : Nat := 118140960795 + 1382272 * 2 ^ 59
def prefixEnd_1382272 : Nat := 4983230072969 + 3 ^ 40 * 1382272 * 2
def baseEnd_1382272 : Nat := 709769931251721088143053

theorem tailTrace_1382272 : CollatzResearch.WordTrace tailWord_1382272 prefixEnd_1382272 709769931251721088143053 := by
  unfold tailWord_1382272
  simp only [CollatzResearch.WordTrace]
  refine ⟨25207800824136046053978535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33610401098848061405304713 25207800824136046053978535)
  ·
    refine ⟨37811701236204069080967803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25207800824136046053978535 37811701236204069080967803)
    ·
      refine ⟨56717551854306103621451705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37811701236204069080967803 56717551854306103621451705)
      ·
        refine ⟨42538163890729577716088779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56717551854306103621451705 42538163890729577716088779)
        ·
          refine ⟨63807245836094366574133169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42538163890729577716088779 63807245836094366574133169)
          ·
            refine ⟨47855434377070774930599877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63807245836094366574133169 47855434377070774930599877)
            ·
              refine ⟨8972893945700770299487477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47855434377070774930599877 8972893945700770299487477)
              ·
                refine ⟨841208807409447215576951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8972893945700770299487477 841208807409447215576951)
                ·
                  refine ⟨1261813211114170823365427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841208807409447215576951 1261813211114170823365427)
                  ·
                    refine ⟨1892719816671256235048141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261813211114170823365427 1892719816671256235048141)
                    ·
                      refine ⟨709769931251721088143053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892719816671256235048141 709769931251721088143053)
                      ·
                        rfl

theorem cell23_1382272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_1382272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382272 prefixEnd_1382272 := by exact prefixLift 1382272
  have htrace : WordTrace (prefixWord ++ tailWord_1382272) baseStart_1382272 baseEnd_1382272 := by
    simpa [prefixWord, tailWord_1382272, baseEnd_1382272] using wordTrace_append hprefix tailTrace_1382272
  have hstable : (prefixWord ++ tailWord_1382272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382272).length < 2 ^ (prefixWord ++ tailWord_1382272).sum := by decide
  have hdescent : baseEnd_1382272 < baseStart_1382272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382289 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 1, 1, 3]
def baseStart_1382289 : Nat := 118140960795 + 1382289 * 2 ^ 59
def prefixEnd_1382289 : Nat := 4983230072969 + 3 ^ 40 * 1382289 * 2
def baseEnd_1382289 : Nat := 709778660422847521630475

theorem tailTrace_1382289 : CollatzResearch.WordTrace tailWord_1382289 prefixEnd_1382289 709778660422847521630475 := by
  unfold tailWord_1382289
  simp only [CollatzResearch.WordTrace]
  refine ⟨50416221689210504011325921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33610814459473669340883947 50416221689210504011325921)
  ·
    refine ⟨37812166266907878008494441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50416221689210504011325921 37812166266907878008494441)
    ·
      refine ⟨28359124700180908506370831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37812166266907878008494441 28359124700180908506370831)
      ·
        refine ⟨42538687050271362759556247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28359124700180908506370831 42538687050271362759556247)
        ·
          refine ⟨63808030575407044139334371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42538687050271362759556247 63808030575407044139334371)
          ·
            refine ⟨95712045863110566209001557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63808030575407044139334371 95712045863110566209001557)
            ·
              refine ⟨1121625537458326947761737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 95712045863110566209001557 1121625537458326947761737)
              ·
                refine ⟨841219153093745210821303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121625537458326947761737 841219153093745210821303)
                ·
                  refine ⟨1261828729640617816231955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841219153093745210821303 1261828729640617816231955)
                  ·
                    refine ⟨1892743094460926724347933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261828729640617816231955 1892743094460926724347933)
                    ·
                      refine ⟨709778660422847521630475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892743094460926724347933 709778660422847521630475)
                      ·
                        rfl

theorem cell23_1382289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_1382289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382289 prefixEnd_1382289 := by exact prefixLift 1382289
  have htrace : WordTrace (prefixWord ++ tailWord_1382289) baseStart_1382289 baseEnd_1382289 := by
    simpa [prefixWord, tailWord_1382289, baseEnd_1382289] using wordTrace_append hprefix tailTrace_1382289
  have hstable : (prefixWord ++ tailWord_1382289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382289).length < 2 ^ (prefixWord ++ tailWord_1382289).sum := by decide
  have hdescent : baseEnd_1382289 < baseStart_1382289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382325 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1382325 : Nat := 118140960795 + 1382325 * 2 ^ 59
def prefixEnd_1382325 : Nat := 4983230072969 + 3 ^ 40 * 1382325 * 2
def baseEnd_1382325 : Nat := 709797145726409380780309

theorem tailTrace_1382325 : CollatzResearch.WordTrace tailWord_1382325 prefixEnd_1382325 709797145726409380780309 := by
  unfold tailWord_1382325
  simp only [CollatzResearch.WordTrace]
  refine ⟨50417534717080082159636429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33611689811386721439757619 50417534717080082159636429)
  ·
    refine ⟨18906575518905030809863661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50417534717080082159636429 18906575518905030809863661)
    ·
      refine ⟨7089965819589386553698873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18906575518905030809863661 7089965819589386553698873)
      ·
        refine ⟨5317474364692039915274155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7089965819589386553698873 5317474364692039915274155)
        ·
          refine ⟨7976211547038059872911233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5317474364692039915274155 7976211547038059872911233)
          ·
            refine ⟨5982158660278544904683425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7976211547038059872911233 5982158660278544904683425)
            ·
              refine ⟨4486618995208908678512569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982158660278544904683425 4486618995208908678512569)
              ·
                refine ⟨3364964246406681508884427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4486618995208908678512569 3364964246406681508884427)
                ·
                  refine ⟨5047446369610022263326641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364964246406681508884427 5047446369610022263326641)
                  ·
                    refine ⟨3785584777207516697494981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5047446369610022263326641 3785584777207516697494981)
                    ·
                      refine ⟨709797145726409380780309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3785584777207516697494981 709797145726409380780309)
                      ·
                        rfl

theorem cell23_1382325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1382325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382325 prefixEnd_1382325 := by exact prefixLift 1382325
  have htrace : WordTrace (prefixWord ++ tailWord_1382325) baseStart_1382325 baseEnd_1382325 := by
    simpa [prefixWord, tailWord_1382325, baseEnd_1382325] using wordTrace_append hprefix tailTrace_1382325
  have hstable : (prefixWord ++ tailWord_1382325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382325).length < 2 ^ (prefixWord ++ tailWord_1382325).sum := by decide
  have hdescent : baseEnd_1382325 < baseStart_1382325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382345 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 3]
def baseStart_1382345 : Nat := 118140960795 + 1382345 * 2 ^ 59
def prefixEnd_1382345 : Nat := 4983230072969 + 3 ^ 40 * 1382345 * 2
def baseEnd_1382345 : Nat := 709807415339499302530217

theorem tailTrace_1382345 : CollatzResearch.WordTrace tailWord_1382345 prefixEnd_1382345 709807415339499302530217 := by
  unfold tailWord_1382345
  simp only [CollatzResearch.WordTrace]
  refine ⟨50418264177007625575364489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33612176118005083716909659 50418264177007625575364489)
  ·
    refine ⟨37813698132755719181523367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50418264177007625575364489 37813698132755719181523367)
    ·
      refine ⟨56720547199133578772285051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37813698132755719181523367 56720547199133578772285051)
      ·
        refine ⟨85080820798700368158427577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56720547199133578772285051 85080820798700368158427577)
        ·
          refine ⟨63810615599025276118820683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85080820798700368158427577 63810615599025276118820683)
          ·
            refine ⟨95715923398537914178231025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63810615599025276118820683 95715923398537914178231025)
            ·
              refine ⟨71786942548903435633673269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95715923398537914178231025 71786942548903435633673269)
              ·
                refine ⟨6730025863959697090656869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71786942548903435633673269 6730025863959697090656869)
                ·
                  refine ⟨1261879849492443204498163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6730025863959697090656869 1261879849492443204498163)
                  ·
                    refine ⟨1892819774238664806747245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261879849492443204498163 1892819774238664806747245)
                    ·
                      refine ⟨709807415339499302530217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1892819774238664806747245 709807415339499302530217)
                      ·
                        rfl

theorem cell23_1382345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_1382345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382345 prefixEnd_1382345 := by exact prefixLift 1382345
  have htrace : WordTrace (prefixWord ++ tailWord_1382345) baseStart_1382345 baseEnd_1382345 := by
    simpa [prefixWord, tailWord_1382345, baseEnd_1382345] using wordTrace_append hprefix tailTrace_1382345
  have hstable : (prefixWord ++ tailWord_1382345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382345).length < 2 ^ (prefixWord ++ tailWord_1382345).sum := by decide
  have hdescent : baseEnd_1382345 < baseStart_1382345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382368 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1382368 : Nat := 118140960795 + 1382368 * 2 ^ 59
def prefixEnd_1382368 : Nat := 4983230072969 + 3 ^ 40 * 1382368 * 2
def baseEnd_1382368 : Nat := 709819225394552712542611

theorem tailTrace_1382368 : CollatzResearch.WordTrace tailWord_1382368 prefixEnd_1382368 709819225394552712542611 := by
  unfold tailWord_1382368
  simp only [CollatzResearch.WordTrace]
  refine ⟨25209551527962150251725879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33612735370616200335634505 25209551527962150251725879)
  ·
    refine ⟨37814327291943225377588819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25209551527962150251725879 37814327291943225377588819)
    ·
      refine ⟨56721490937914838066383229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37814327291943225377588819 56721490937914838066383229)
      ·
        refine ⟨21270559101718064274893711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56721490937914838066383229 21270559101718064274893711)
        ·
          refine ⟨31905838652577096412340567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21270559101718064274893711 31905838652577096412340567)
          ·
            refine ⟨47858757978865644618510851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31905838652577096412340567 47858757978865644618510851)
            ·
              refine ⟨71788136968298466927766277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47858757978865644618510851 71788136968298466927766277)
              ·
                refine ⟨13460275681555962548956177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71788136968298466927766277 13460275681555962548956177)
                ·
                  refine ⟨10095206761166971911717133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13460275681555962548956177 10095206761166971911717133)
                  ·
                    refine ⟨3785702535437614466893925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10095206761166971911717133 3785702535437614466893925)
                    ·
                      refine ⟨709819225394552712542611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3785702535437614466893925 709819225394552712542611)
                      ·
                        rfl

theorem cell23_1382368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1382368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382368 prefixEnd_1382368 := by exact prefixLift 1382368
  have htrace : WordTrace (prefixWord ++ tailWord_1382368) baseStart_1382368 baseEnd_1382368 := by
    simpa [prefixWord, tailWord_1382368, baseEnd_1382368] using wordTrace_append hprefix tailTrace_1382368
  have hstable : (prefixWord ++ tailWord_1382368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382368).length < 2 ^ (prefixWord ++ tailWord_1382368).sum := by decide
  have hdescent : baseEnd_1382368 < baseStart_1382368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382423 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1382423 : Nat := 118140960795 + 1382423 * 2 ^ 59
def prefixEnd_1382423 : Nat := 4983230072969 + 3 ^ 40 * 1382423 * 2
def baseEnd_1382423 : Nat := 709847466830549997354859

theorem tailTrace_1382423 : CollatzResearch.WordTrace tailWord_1382423 prefixEnd_1382423 709847466830549997354859 := by
  unfold tailWord_1382423
  simp only [CollatzResearch.WordTrace]
  refine ⟨50421109070725044896703923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33614072713816696597802615 50421109070725044896703923)
  ·
    refine ⟨75631663606087567345055885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50421109070725044896703923 75631663606087567345055885)
    ·
      refine ⟨28361873852282837754395957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75631663606087567345055885 28361873852282837754395957)
      ·
        refine ⟨2658925673651516039474621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28361873852282837754395957 2658925673651516039474621)
        ·
          refine ⟨997097127619318514802983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2658925673651516039474621 997097127619318514802983)
          ·
            refine ⟨1495645691428977772204475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997097127619318514802983 1495645691428977772204475)
            ·
              refine ⟨2243468537143466658306713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495645691428977772204475 2243468537143466658306713)
              ·
                refine ⟨1682601402857599993730035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243468537143466658306713 1682601402857599993730035)
                ·
                  refine ⟨2523902104286399990595053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682601402857599993730035 2523902104286399990595053)
                  ·
                    refine ⟨946463289107399996473145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523902104286399990595053 946463289107399996473145)
                    ·
                      refine ⟨709847466830549997354859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946463289107399996473145 709847466830549997354859)
                      ·
                        rfl

theorem cell23_1382423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1382423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382423 prefixEnd_1382423 := by exact prefixLift 1382423
  have htrace : WordTrace (prefixWord ++ tailWord_1382423) baseStart_1382423 baseEnd_1382423 := by
    simpa [prefixWord, tailWord_1382423, baseEnd_1382423] using wordTrace_append hprefix tailTrace_1382423
  have hstable : (prefixWord ++ tailWord_1382423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382423).length < 2 ^ (prefixWord ++ tailWord_1382423).sum := by decide
  have hdescent : baseEnd_1382423 < baseStart_1382423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382455 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 2, 5]
def baseStart_1382455 : Nat := 118140960795 + 1382455 * 2 ^ 59
def prefixEnd_1382455 : Nat := 4983230072969 + 3 ^ 40 * 1382455 * 2
def baseEnd_1382455 : Nat := 236621299403831290718237

theorem tailTrace_1382455 : CollatzResearch.WordTrace tailWord_1382455 prefixEnd_1382455 236621299403831290718237 := by
  unfold tailWord_1382455
  simp only [CollatzResearch.WordTrace]
  refine ⟨50422276206609114361868819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33614850804406076241245879 50422276206609114361868819)
  ·
    refine ⟨75633414309913671542803229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50422276206609114361868819 75633414309913671542803229)
    ·
      refine ⟨28362530366217626828551211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75633414309913671542803229 28362530366217626828551211)
      ·
        refine ⟨42543795549326440242826817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28362530366217626828551211 42543795549326440242826817)
        ·
          refine ⟨31907846661994830182120113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42543795549326440242826817 31907846661994830182120113)
          ·
            refine ⟨23930884996496122636590085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31907846661994830182120113 23930884996496122636590085)
            ·
              refine ⟨4487040936843022994360641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23930884996496122636590085 4487040936843022994360641)
              ·
                refine ⟨3365280702632267245770481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487040936843022994360641 3365280702632267245770481)
                ·
                  refine ⟨2523960526974200434327861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365280702632267245770481 2523960526974200434327861)
                  ·
                    refine ⟨236621299403831290718237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2523960526974200434327861 236621299403831290718237)
                    ·
                      rfl

theorem cell23_1382455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_1382455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382455 prefixEnd_1382455 := by exact prefixLift 1382455
  have htrace : WordTrace (prefixWord ++ tailWord_1382455) baseStart_1382455 baseEnd_1382455 := by
    simpa [prefixWord, tailWord_1382455, baseEnd_1382455] using wordTrace_append hprefix tailTrace_1382455
  have hstable : (prefixWord ++ tailWord_1382455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382455).length < 2 ^ (prefixWord ++ tailWord_1382455).sum := by decide
  have hdescent : baseEnd_1382455 < baseStart_1382455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382492 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1382492 : Nat := 118140960795 + 1382492 * 2 ^ 59
def prefixEnd_1382492 : Nat := 4983230072969 + 3 ^ 40 * 1382492 * 2
def baseEnd_1382492 : Nat := 709882896995710227392041

theorem tailTrace_1382492 : CollatzResearch.WordTrace tailWord_1382492 prefixEnd_1382492 709882896995710227392041 := by
  unfold tailWord_1382492
  simp only [CollatzResearch.WordTrace]
  refine ⟨25211812853737534840482865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33615750471650046453977153 25211812853737534840482865)
  ·
    refine ⟨18908859640303151130362149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25211812853737534840482865 18908859640303151130362149)
    ·
      refine ⟨3545411182556840836942903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18908859640303151130362149 3545411182556840836942903)
      ·
        refine ⟨5318116773835261255414355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545411182556840836942903 5318116773835261255414355)
        ·
          refine ⟨7977175160752891883121533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5318116773835261255414355 7977175160752891883121533)
          ·
            refine ⟨2991440685282334456170575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7977175160752891883121533 2991440685282334456170575)
            ·
              refine ⟨4487161027923501684255863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991440685282334456170575 4487161027923501684255863)
              ·
                refine ⟨6730741541885252526383795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4487161027923501684255863 6730741541885252526383795)
                ·
                  refine ⟨10096112312827878789575693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6730741541885252526383795 10096112312827878789575693)
                  ·
                    refine ⟨3786042117310454546090885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10096112312827878789575693 3786042117310454546090885)
                    ·
                      refine ⟨709882896995710227392041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3786042117310454546090885 709882896995710227392041)
                      ·
                        rfl

theorem cell23_1382492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1382492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382492 prefixEnd_1382492 := by exact prefixLift 1382492
  have htrace : WordTrace (prefixWord ++ tailWord_1382492) baseStart_1382492 baseEnd_1382492 := by
    simpa [prefixWord, tailWord_1382492, baseEnd_1382492] using wordTrace_append hprefix tailTrace_1382492
  have hstable : (prefixWord ++ tailWord_1382492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382492).length < 2 ^ (prefixWord ++ tailWord_1382492).sum := by decide
  have hdescent : baseEnd_1382492 < baseStart_1382492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382519 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 1, 4]
def baseStart_1382519 : Nat := 118140960795 + 1382519 * 2 ^ 59
def prefixEnd_1382519 : Nat := 4983230072969 + 3 ^ 40 * 1382519 * 2
def baseEnd_1382519 : Nat := 236632253657793873918139

theorem tailTrace_1382519 : CollatzResearch.WordTrace tailWord_1382519 prefixEnd_1382519 236632253657793873918139 := by
  unfold tailWord_1382519
  simp only [CollatzResearch.WordTrace]
  refine ⟨50424610478377253292198611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33616406985584835528132407 50424610478377253292198611)
  ·
    refine ⟨75636915717565879938297917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50424610478377253292198611 75636915717565879938297917)
    ·
      refine ⟨28363843394087204976861719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75636915717565879938297917 28363843394087204976861719)
      ·
        refine ⟨42545765091130807465292579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28363843394087204976861719 42545765091130807465292579)
        ·
          refine ⟨63818647636696211197938869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42545765091130807465292579 63818647636696211197938869)
          ·
            refine ⟨5982998215940269799806769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63818647636696211197938869 5982998215940269799806769)
            ·
              refine ⟨4487248661955202349855077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982998215940269799806769 4487248661955202349855077)
              ·
                refine ⟨841359124116600440597827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4487248661955202349855077 841359124116600440597827)
                ·
                  refine ⟨1262038686174900660896741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841359124116600440597827 1262038686174900660896741)
                  ·
                    refine ⟨236632253657793873918139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262038686174900660896741 236632253657793873918139)
                    ·
                      rfl

theorem cell23_1382519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_1382519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382519 prefixEnd_1382519 := by exact prefixLift 1382519
  have htrace : WordTrace (prefixWord ++ tailWord_1382519) baseStart_1382519 baseEnd_1382519 := by
    simpa [prefixWord, tailWord_1382519, baseEnd_1382519] using wordTrace_append hprefix tailTrace_1382519
  have hstable : (prefixWord ++ tailWord_1382519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382519).length < 2 ^ (prefixWord ++ tailWord_1382519).sum := by decide
  have hdescent : baseEnd_1382519 < baseStart_1382519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382570 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1382570 : Nat := 118140960795 + 1382570 * 2 ^ 59
def prefixEnd_1382570 : Nat := 4983230072969 + 3 ^ 40 * 1382570 * 2
def baseEnd_1382570 : Nat := 236640982828920307405561

theorem tailTrace_1382570 : CollatzResearch.WordTrace tailWord_1382570 prefixEnd_1382570 236640982828920307405561 := by
  unfold tailWord_1382570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12606617650298122250576291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33617647067461659334870109 12606617650298122250576291)
  ·
    refine ⟨18909926475447183375864437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12606617650298122250576291 18909926475447183375864437)
    ·
      refine ⟨1772805607073173441487291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18909926475447183375864437 1772805607073173441487291)
      ·
        refine ⟨2659208410609760162230937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772805607073173441487291 2659208410609760162230937)
        ·
          refine ⟨1994406307957320121673203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2659208410609760162230937 1994406307957320121673203)
          ·
            refine ⟨2991609461935980182509805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994406307957320121673203 2991609461935980182509805)
            ·
              refine ⟨1121853548225992568441177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2991609461935980182509805 1121853548225992568441177)
              ·
                refine ⟨841390161169494426330883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121853548225992568441177 841390161169494426330883)
                ·
                  refine ⟨1262085241754241639496325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841390161169494426330883 1262085241754241639496325)
                  ·
                    refine ⟨236640982828920307405561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262085241754241639496325 236640982828920307405561)
                    ·
                      rfl

theorem cell23_1382570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1382570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382570 prefixEnd_1382570 := by exact prefixLift 1382570
  have htrace : WordTrace (prefixWord ++ tailWord_1382570) baseStart_1382570 baseEnd_1382570 := by
    simpa [prefixWord, tailWord_1382570, baseEnd_1382570] using wordTrace_append hprefix tailTrace_1382570
  have hstable : (prefixWord ++ tailWord_1382570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382570).length < 2 ^ (prefixWord ++ tailWord_1382570).sum := by decide
  have hdescent : baseEnd_1382570 < baseStart_1382570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382596 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1382596 : Nat := 118140960795 + 1382596 * 2 ^ 59
def prefixEnd_1382596 : Nat := 4983230072969 + 3 ^ 40 * 1382596 * 2
def baseEnd_1382596 : Nat := 236645432994592606830521

theorem tailTrace_1382596 : CollatzResearch.WordTrace tailWord_1382596 prefixEnd_1382596 236645432994592606830521 := by
  unfold tailWord_1382596
  simp only [CollatzResearch.WordTrace]
  refine ⟨25213709449549147721375821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33618279266065530295167761 25213709449549147721375821)
  ·
    refine ⟨9455141043580930395515933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25213709449549147721375821 9455141043580930395515933)
    ·
      refine ⟨3545677891342848898318475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9455141043580930395515933 3545677891342848898318475)
      ·
        refine ⟨5318516837014273347477713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545677891342848898318475 5318516837014273347477713)
        ·
          refine ⟨3988887627760705010608285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5318516837014273347477713 3988887627760705010608285)
          ·
            refine ⟨1495832860410264378978107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3988887627760705010608285 1495832860410264378978107)
            ·
              refine ⟨2243749290615396568467161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495832860410264378978107 2243749290615396568467161)
              ·
                refine ⟨1682811967961547426350371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243749290615396568467161 1682811967961547426350371)
                ·
                  refine ⟨2524217951942321139525557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682811967961547426350371 2524217951942321139525557)
                  ·
                    refine ⟨236645432994592606830521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2524217951942321139525557 236645432994592606830521)
                    ·
                      rfl

theorem cell23_1382596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1382596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382596 prefixEnd_1382596 := by exact prefixLift 1382596
  have htrace : WordTrace (prefixWord ++ tailWord_1382596) baseStart_1382596 baseEnd_1382596 := by
    simpa [prefixWord, tailWord_1382596, baseEnd_1382596] using wordTrace_append hprefix tailTrace_1382596
  have hstable : (prefixWord ++ tailWord_1382596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382596).length < 2 ^ (prefixWord ++ tailWord_1382596).sum := by decide
  have hdescent : baseEnd_1382596 < baseStart_1382596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382616 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 1, 1, 4]
def baseStart_1382616 : Nat := 118140960795 + 1382616 * 2 ^ 59
def prefixEnd_1382616 : Nat := 4983230072969 + 3 ^ 40 * 1382616 * 2
def baseEnd_1382616 : Nat := 709946568596867742241471

theorem tailTrace_1382616 : CollatzResearch.WordTrace tailWord_1382616 prefixEnd_1382616 709946568596867742241471 := by
  unfold tailWord_1382616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25214074179512919429239851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33618765572683892572319801 25214074179512919429239851)
  ·
    refine ⟨37821111269269379143859777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25214074179512919429239851 37821111269269379143859777)
    ·
      refine ⟨28365833451952034357894833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37821111269269379143859777 28365833451952034357894833)
      ·
        refine ⟨21274375088964025768421125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28365833451952034357894833 21274375088964025768421125)
        ·
          refine ⟨3988945329180754831578961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21274375088964025768421125 3988945329180754831578961)
          ·
            refine ⟨2991708996885566123684221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988945329180754831578961 2991708996885566123684221)
            ·
              refine ⟨1121890873832087296381583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2991708996885566123684221 1121890873832087296381583)
              ·
                refine ⟨1682836310748130944572375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121890873832087296381583 1682836310748130944572375)
                ·
                  refine ⟨2524254466122196416858563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682836310748130944572375 2524254466122196416858563)
                  ·
                    refine ⟨3786381699183294625287845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524254466122196416858563 3786381699183294625287845)
                    ·
                      refine ⟨709946568596867742241471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3786381699183294625287845 709946568596867742241471)
                      ·
                        rfl

theorem cell23_1382616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_1382616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382616 prefixEnd_1382616 := by exact prefixLift 1382616
  have htrace : WordTrace (prefixWord ++ tailWord_1382616) baseStart_1382616 baseEnd_1382616 := by
    simpa [prefixWord, tailWord_1382616, baseEnd_1382616] using wordTrace_append hprefix tailTrace_1382616
  have hstable : (prefixWord ++ tailWord_1382616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382616).length < 2 ^ (prefixWord ++ tailWord_1382616).sum := by decide
  have hdescent : baseEnd_1382616 < baseStart_1382616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382627 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1382627 : Nat := 118140960795 + 1382627 * 2 ^ 59
def prefixEnd_1382627 : Nat := 4983230072969 + 3 ^ 40 * 1382627 * 2
def baseEnd_1382627 : Nat := 709952216884067199203921

theorem tailTrace_1382627 : CollatzResearch.WordTrace tailWord_1382627 prefixEnd_1382627 709952216884067199203921 := by
  unfold tailWord_1382627
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428549561985987737130135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33619033041323991824753423 50428549561985987737130135)
  ·
    refine ⟨75642824342978981605695203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50428549561985987737130135 75642824342978981605695203)
    ·
      refine ⟨113464236514468472408542805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75642824342978981605695203 113464236514468472408542805)
      ·
        refine ⟨1329659021653927411037611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 113464236514468472408542805 1329659021653927411037611)
        ·
          refine ⟨1994488532480891116556417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329659021653927411037611 1994488532480891116556417)
          ·
            refine ⟨1495866399360668337417313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994488532480891116556417 1495866399360668337417313)
            ·
              refine ⟨1121899799520501253062985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495866399360668337417313 1121899799520501253062985)
              ·
                refine ⟨841424849640375939797239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121899799520501253062985 841424849640375939797239)
                ·
                  refine ⟨1262137274460563909695859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841424849640375939797239 1262137274460563909695859)
                  ·
                    refine ⟨1893205911690845864543789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1262137274460563909695859 1893205911690845864543789)
                    ·
                      refine ⟨709952216884067199203921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1893205911690845864543789 709952216884067199203921)
                      ·
                        rfl

theorem cell23_1382627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1382627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382627 prefixEnd_1382627 := by exact prefixLift 1382627
  have htrace : WordTrace (prefixWord ++ tailWord_1382627) baseStart_1382627 baseEnd_1382627 := by
    simpa [prefixWord, tailWord_1382627, baseEnd_1382627] using wordTrace_append hprefix tailTrace_1382627
  have hstable : (prefixWord ++ tailWord_1382627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382627).length < 2 ^ (prefixWord ++ tailWord_1382627).sum := by decide
  have hdescent : baseEnd_1382627 < baseStart_1382627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382635 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 9]
def baseStart_1382635 : Nat := 118140960795 + 1382635 * 2 ^ 59
def prefixEnd_1382635 : Nat := 4983230072969 + 3 ^ 40 * 1382635 * 2
def baseEnd_1382635 : Nat := 236652108243101055967961

theorem tailTrace_1382635 : CollatzResearch.WordTrace tailWord_1382635 prefixEnd_1382635 236652108243101055967961 := by
  unfold tailWord_1382635
  simp only [CollatzResearch.WordTrace]
  refine ⟨50428841345957005103421359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33619227563971336735614239 50428841345957005103421359)
  ·
    refine ⟨75643262018935507655132039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50428841345957005103421359 75643262018935507655132039)
    ·
      refine ⟨113464893028403261482698059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75643262018935507655132039 113464893028403261482698059)
      ·
        refine ⟨170197339542604892224047089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113464893028403261482698059 170197339542604892224047089)
        ·
          refine ⟨127648004656953669168035317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170197339542604892224047089 127648004656953669168035317)
          ·
            refine ⟨11967000436589406484503311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127648004656953669168035317 11967000436589406484503311)
            ·
              refine ⟨17950500654884109726754967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11967000436589406484503311 17950500654884109726754967)
              ·
                refine ⟨26925750982326164590132451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17950500654884109726754967 26925750982326164590132451)
                ·
                  refine ⟨40388626473489246885198677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26925750982326164590132451 40388626473489246885198677)
                  ·
                    refine ⟨236652108243101055967961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 40388626473489246885198677 236652108243101055967961)
                    ·
                      rfl

theorem cell23_1382635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_1382635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382635 prefixEnd_1382635 := by exact prefixLift 1382635
  have htrace : WordTrace (prefixWord ++ tailWord_1382635) baseStart_1382635 baseEnd_1382635 := by
    simpa [prefixWord, tailWord_1382635, baseEnd_1382635] using wordTrace_append hprefix tailTrace_1382635
  have hstable : (prefixWord ++ tailWord_1382635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382635).length < 2 ^ (prefixWord ++ tailWord_1382635).sum := by decide
  have hdescent : baseEnd_1382635 < baseStart_1382635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382659 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 3, 3, 2]
def baseStart_1382659 : Nat := 118140960795 + 1382659 * 2 ^ 59
def prefixEnd_1382659 : Nat := 4983230072969 + 3 ^ 40 * 1382659 * 2
def baseEnd_1382659 : Nat := 709968648265011074003773

theorem tailTrace_1382659 : CollatzResearch.WordTrace tailWord_1382659 prefixEnd_1382659 709968648265011074003773 := by
  unfold tailWord_1382659
  simp only [CollatzResearch.WordTrace]
  refine ⟨50429716697870057202295031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33619811131913371468196687 50429716697870057202295031)
  ·
    refine ⟨75644575046805085803442547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50429716697870057202295031 75644575046805085803442547)
    ·
      refine ⟨113466862570207628705163821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75644575046805085803442547 113466862570207628705163821)
      ·
        refine ⟨42550073463827860764436433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113466862570207628705163821 42550073463827860764436433)
        ·
          refine ⟨31912555097870895573327325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42550073463827860764436433 31912555097870895573327325)
          ·
            refine ⟨11967208161701585839997747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31912555097870895573327325 11967208161701585839997747)
            ·
              refine ⟨17950812242552378759996621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11967208161701585839997747 17950812242552378759996621)
              ·
                refine ⟨6731554590957142034998733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17950812242552378759996621 6731554590957142034998733)
                ·
                  refine ⟨2524332971608928263124525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6731554590957142034998733 2524332971608928263124525)
                  ·
                    refine ⟨946624864353348098671697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524332971608928263124525 946624864353348098671697)
                    ·
                      refine ⟨709968648265011074003773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946624864353348098671697 709968648265011074003773)
                      ·
                        rfl

theorem cell23_1382659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_1382659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382659 prefixEnd_1382659 := by exact prefixLift 1382659
  have htrace : WordTrace (prefixWord ++ tailWord_1382659) baseStart_1382659 baseEnd_1382659 := by
    simpa [prefixWord, tailWord_1382659, baseEnd_1382659] using wordTrace_append hprefix tailTrace_1382659
  have hstable : (prefixWord ++ tailWord_1382659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382659).length < 2 ^ (prefixWord ++ tailWord_1382659).sum := by decide
  have hdescent : baseEnd_1382659 < baseStart_1382659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382689 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_1382689 : Nat := 118140960795 + 1382689 * 2 ^ 59
def prefixEnd_1382689 : Nat := 4983230072969 + 3 ^ 40 * 1382689 * 2
def baseEnd_1382689 : Nat := 709984052684645956628635

theorem tailTrace_1382689 : CollatzResearch.WordTrace tailWord_1382689 prefixEnd_1382689 709984052684645956628635 := by
  unfold tailWord_1382689
  simp only [CollatzResearch.WordTrace]
  refine ⟨50430810887761372325887121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33620540591840914883924747 50430810887761372325887121)
  ·
    refine ⟨37823108165821029244415341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50430810887761372325887121 37823108165821029244415341)
    ·
      refine ⟨14183665562182885966655753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37823108165821029244415341 14183665562182885966655753)
      ·
        refine ⟨10637749171637164474991815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14183665562182885966655753 10637749171637164474991815)
        ·
          refine ⟨15956623757455746712487723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637749171637164474991815 15956623757455746712487723)
          ·
            refine ⟨23934935636183620068731585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15956623757455746712487723 23934935636183620068731585)
            ·
              refine ⟨17951201727137715051548689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23934935636183620068731585 17951201727137715051548689)
              ·
                refine ⟨13463401295353286288661517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17951201727137715051548689 13463401295353286288661517)
                ·
                  refine ⟨5048775485757482358248069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13463401295353286288661517 5048775485757482358248069)
                  ·
                    refine ⟨946645403579527942171513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048775485757482358248069 946645403579527942171513)
                    ·
                      refine ⟨709984052684645956628635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946645403579527942171513 709984052684645956628635)
                      ·
                        rfl

theorem cell23_1382689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_1382689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382689 prefixEnd_1382689 := by exact prefixLift 1382689
  have htrace : WordTrace (prefixWord ++ tailWord_1382689) baseStart_1382689 baseEnd_1382689 := by
    simpa [prefixWord, tailWord_1382689, baseEnd_1382689] using wordTrace_append hprefix tailTrace_1382689
  have hstable : (prefixWord ++ tailWord_1382689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382689).length < 2 ^ (prefixWord ++ tailWord_1382689).sum := by decide
  have hdescent : baseEnd_1382689 < baseStart_1382689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382712 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 7]
def baseStart_1382712 : Nat := 118140960795 + 1382712 * 2 ^ 59
def prefixEnd_1382712 : Nat := 4983230072969 + 3 ^ 40 * 1382712 * 2
def baseEnd_1382712 : Nat := 78888429193299929626781

theorem tailTrace_1382712 : CollatzResearch.WordTrace tailWord_1382712 prefixEnd_1382712 78888429193299929626781 := by
  unfold tailWord_1382712
  simp only [CollatzResearch.WordTrace]
  refine ⟨25215824883339023626987195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33621099844452031502649593 25215824883339023626987195)
  ·
    refine ⟨37823737325008535440480793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25215824883339023626987195 37823737325008535440480793)
    ·
      refine ⟨28367802993756401580360595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37823737325008535440480793 28367802993756401580360595)
      ·
        refine ⟨42551704490634602370540893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28367802993756401580360595 42551704490634602370540893)
        ·
          refine ⟨15956889183987975888952835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42551704490634602370540893 15956889183987975888952835)
          ·
            refine ⟨23935333775981963833429253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15956889183987975888952835 23935333775981963833429253)
            ·
              refine ⟨4487875082996618218767985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23935333775981963833429253 4487875082996618218767985)
              ·
                refine ⟨3365906312247463664075989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487875082996618218767985 3365906312247463664075989)
                ·
                  refine ⟨78888429193299929626781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3365906312247463664075989 78888429193299929626781)
                  ·
                    rfl

theorem cell23_1382712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_1382712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382712 prefixEnd_1382712 := by exact prefixLift 1382712
  have htrace : WordTrace (prefixWord ++ tailWord_1382712) baseStart_1382712 baseEnd_1382712 := by
    simpa [prefixWord, tailWord_1382712, baseEnd_1382712] using wordTrace_append hprefix tailTrace_1382712
  have hstable : (prefixWord ++ tailWord_1382712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382712).length < 2 ^ (prefixWord ++ tailWord_1382712).sum := by decide
  have hdescent : baseEnd_1382712 < baseStart_1382712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382779 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 4]
def baseStart_1382779 : Nat := 118140960795 + 1382779 * 2 ^ 59
def prefixEnd_1382779 : Nat := 4983230072969 + 3 ^ 40 * 1382779 * 2
def baseEnd_1382779 : Nat := 710030265943550604503221

theorem tailTrace_1382779 : CollatzResearch.WordTrace tailWord_1382779 prefixEnd_1382779 710030265943550604503221 := by
  unfold tailWord_1382779
  simp only [CollatzResearch.WordTrace]
  refine ⟨50434093457435317696663391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33622728971623545131108927 50434093457435317696663391)
  ·
    refine ⟨75651140186152976544995087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50434093457435317696663391 75651140186152976544995087)
    ·
      refine ⟨113476710279229464817492631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75651140186152976544995087 113476710279229464817492631)
      ·
        refine ⟨170215065418844197226238947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113476710279229464817492631 170215065418844197226238947)
        ·
          refine ⟨255322598128266295839358421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170215065418844197226238947 255322598128266295839358421)
          ·
            refine ⟨5984123393631241308734963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 255322598128266295839358421 5984123393631241308734963)
            ·
              refine ⟨8976185090446861963102445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984123393631241308734963 8976185090446861963102445)
              ·
                refine ⟨3366069408917573236163417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8976185090446861963102445 3366069408917573236163417)
                ·
                  refine ⟨2524552056688179927122563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366069408917573236163417 2524552056688179927122563)
                  ·
                    refine ⟨3786828085032269890683845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524552056688179927122563 3786828085032269890683845)
                    ·
                      refine ⟨710030265943550604503221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3786828085032269890683845 710030265943550604503221)
                      ·
                        rfl

theorem cell23_1382779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 4].length) (baseStart_1382779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382779 prefixEnd_1382779 := by exact prefixLift 1382779
  have htrace : WordTrace (prefixWord ++ tailWord_1382779) baseStart_1382779 baseEnd_1382779 := by
    simpa [prefixWord, tailWord_1382779, baseEnd_1382779] using wordTrace_append hprefix tailTrace_1382779
  have hstable : (prefixWord ++ tailWord_1382779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382779).length < 2 ^ (prefixWord ++ tailWord_1382779).sum := by decide
  have hdescent : baseEnd_1382779 < baseStart_1382779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382813 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_1382813 : Nat := 118140960795 + 1382813 * 2 ^ 59
def prefixEnd_1382813 : Nat := 4983230072969 + 3 ^ 40 * 1382813 * 2
def baseEnd_1382813 : Nat := 710047724285803471478065

theorem tailTrace_1382813 : CollatzResearch.WordTrace tailWord_1382813 prefixEnd_1382813 710047724285803471478065 := by
  unfold tailWord_1382813
  simp only [CollatzResearch.WordTrace]
  refine ⟨50435333539312141503401093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33623555692874761002267395 50435333539312141503401093)
  ·
    refine ⟨9456625038621026531887705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50435333539312141503401093 9456625038621026531887705)
    ·
      refine ⟨7092468778965769898915779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9456625038621026531887705 7092468778965769898915779)
      ·
        refine ⟨10638703168448654848373669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7092468778965769898915779 10638703168448654848373669)
        ·
          refine ⟨1994756844084122784070063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10638703168448654848373669 1994756844084122784070063)
          ·
            refine ⟨2992135266126184176105095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994756844084122784070063 2992135266126184176105095)
            ·
              refine ⟨4488202899189276264157643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992135266126184176105095 4488202899189276264157643)
              ·
                refine ⟨6732304348783914396236465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488202899189276264157643 6732304348783914396236465)
                ·
                  refine ⟨5049228261587935797177349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6732304348783914396236465 5049228261587935797177349)
                  ·
                    refine ⟨946730299047737961970753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049228261587935797177349 946730299047737961970753)
                    ·
                      refine ⟨710047724285803471478065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946730299047737961970753 710047724285803471478065)
                      ·
                        rfl

theorem cell23_1382813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_1382813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382813 prefixEnd_1382813 := by exact prefixLift 1382813
  have htrace : WordTrace (prefixWord ++ tailWord_1382813) baseStart_1382813 baseEnd_1382813 := by
    simpa [prefixWord, tailWord_1382813, baseEnd_1382813] using wordTrace_append hprefix tailTrace_1382813
  have hstable : (prefixWord ++ tailWord_1382813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382813).length < 2 ^ (prefixWord ++ tailWord_1382813).sum := by decide
  have hdescent : baseEnd_1382813 < baseStart_1382813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382819 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 6]
def baseStart_1382819 : Nat := 118140960795 + 1382819 * 2 ^ 59
def prefixEnd_1382819 : Nat := 4983230072969 + 3 ^ 40 * 1382819 * 2
def baseEnd_1382819 : Nat := 78894533907747827555893

theorem tailTrace_1382819 : CollatzResearch.WordTrace tailWord_1382819 prefixEnd_1382819 78894533907747827555893 := by
  unfold tailWord_1382819
  simp only [CollatzResearch.WordTrace]
  refine ⟨50435552377290404528119511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33623701584860269685413007 50435552377290404528119511)
  ·
    refine ⟨75653328565935606792179267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50435552377290404528119511 75653328565935606792179267)
    ·
      refine ⟨113479992848903410188268901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75653328565935606792179267 113479992848903410188268901)
      ·
        refine ⟨21277498659169389410300419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113479992848903410188268901 21277498659169389410300419)
        ·
          refine ⟨31916247988754084115450629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277498659169389410300419 31916247988754084115450629)
          ·
            refine ⟨5984296497891390771646993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31916247988754084115450629 5984296497891390771646993)
            ·
              refine ⟨4488222373418543078735245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5984296497891390771646993 4488222373418543078735245)
              ·
                refine ⟨1683083390031953654525717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4488222373418543078735245 1683083390031953654525717)
                ·
                  refine ⟨78894533907747827555893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1683083390031953654525717 78894533907747827555893)
                  ·
                    rfl

theorem cell23_1382819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 6].length) (baseStart_1382819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382819 prefixEnd_1382819 := by exact prefixLift 1382819
  have htrace : WordTrace (prefixWord ++ tailWord_1382819) baseStart_1382819 baseEnd_1382819 := by
    simpa [prefixWord, tailWord_1382819, baseEnd_1382819] using wordTrace_append hprefix tailTrace_1382819
  have hstable : (prefixWord ++ tailWord_1382819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382819).length < 2 ^ (prefixWord ++ tailWord_1382819).sum := by decide
  have hdescent : baseEnd_1382819 < baseStart_1382819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382833 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1382833 : Nat := 118140960795 + 1382833 * 2 ^ 59
def prefixEnd_1382833 : Nat := 4983230072969 + 3 ^ 40 * 1382833 * 2
def baseEnd_1382833 : Nat := 710057993898893393227973

theorem tailTrace_1382833 : CollatzResearch.WordTrace tailWord_1382833 prefixEnd_1382833 710057993898893393227973 := by
  unfold tailWord_1382833
  simp only [CollatzResearch.WordTrace]
  refine ⟨50436062999239684919129153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33624041999493123279419435 50436062999239684919129153)
  ·
    refine ⟨37827047249429763689346865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50436062999239684919129153 37827047249429763689346865)
    ·
      refine ⟨28370285437072322767010149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37827047249429763689346865 28370285437072322767010149)
      ·
        refine ⟨5319428519451060518814403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28370285437072322767010149 5319428519451060518814403)
        ·
          refine ⟨7979142779176590778221605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319428519451060518814403 7979142779176590778221605)
          ·
            refine ⟨1496089271095610770916551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7979142779176590778221605 1496089271095610770916551)
            ·
              refine ⟨2244133906643416156374827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496089271095610770916551 2244133906643416156374827)
              ·
                refine ⟨3366200859965124234562241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244133906643416156374827 3366200859965124234562241)
                ·
                  refine ⟨2524650644973843175921681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366200859965124234562241 2524650644973843175921681)
                  ·
                    refine ⟨1893487983730382381941261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524650644973843175921681 1893487983730382381941261)
                    ·
                      refine ⟨710057993898893393227973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1893487983730382381941261 710057993898893393227973)
                      ·
                        rfl

theorem cell23_1382833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1382833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382833 prefixEnd_1382833 := by exact prefixLift 1382833
  have htrace : WordTrace (prefixWord ++ tailWord_1382833) baseStart_1382833 baseEnd_1382833 := by
    simpa [prefixWord, tailWord_1382833, baseEnd_1382833] using wordTrace_append hprefix tailTrace_1382833
  have hstable : (prefixWord ++ tailWord_1382833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382833).length < 2 ^ (prefixWord ++ tailWord_1382833).sum := by decide
  have hdescent : baseEnd_1382833 < baseStart_1382833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382883 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 1, 5]
def baseStart_1382883 : Nat := 118140960795 + 1382883 * 2 ^ 59
def prefixEnd_1382883 : Nat := 4983230072969 + 3 ^ 40 * 1382883 * 2
def baseEnd_1382883 : Nat := 236694555977206065867581

theorem tailTrace_1382883 : CollatzResearch.WordTrace tailWord_1382883 prefixEnd_1382883 236694555977206065867581 := by
  unfold tailWord_1382883
  simp only [CollatzResearch.WordTrace]
  refine ⟨50437886649058543458449303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33625257766039028972299535 50437886649058543458449303)
  ·
    refine ⟨75656829973587815187673955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50437886649058543458449303 75656829973587815187673955)
    ·
      refine ⟨113485244960381722781510933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75656829973587815187673955 113485244960381722781510933)
      ·
        refine ⟨5319620857517893255383325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113485244960381722781510933 5319620857517893255383325)
        ·
          refine ⟨1994857821569209970768747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5319620857517893255383325 1994857821569209970768747)
          ·
            refine ⟨2992286732353814956153121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994857821569209970768747 2992286732353814956153121)
            ·
              refine ⟨2244215049265361217114841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992286732353814956153121 2244215049265361217114841)
              ·
                refine ⟨1683161286949020912836131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244215049265361217114841 1683161286949020912836131)
                ·
                  refine ⟨2524741930423531369254197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683161286949020912836131 2524741930423531369254197)
                  ·
                    refine ⟨236694555977206065867581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2524741930423531369254197 236694555977206065867581)
                    ·
                      rfl

theorem cell23_1382883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 5].length) (baseStart_1382883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382883 prefixEnd_1382883 := by exact prefixLift 1382883
  have htrace : WordTrace (prefixWord ++ tailWord_1382883) baseStart_1382883 baseEnd_1382883 := by
    simpa [prefixWord, tailWord_1382883, baseEnd_1382883] using wordTrace_append hprefix tailTrace_1382883
  have hstable : (prefixWord ++ tailWord_1382883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382883).length < 2 ^ (prefixWord ++ tailWord_1382883).sum := by decide
  have hdescent : baseEnd_1382883 < baseStart_1382883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382899 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4]
def baseStart_1382899 : Nat := 118140960795 + 1382899 * 2 ^ 59
def prefixEnd_1382899 : Nat := 4983230072969 + 3 ^ 40 * 1382899 * 2
def baseEnd_1382899 : Nat := 710091883622090135002669

theorem tailTrace_1382899 : CollatzResearch.WordTrace tailWord_1382899 prefixEnd_1382899 710091883622090135002669 := by
  unfold tailWord_1382899
  simp only [CollatzResearch.WordTrace]
  refine ⟨50438470217000578191031751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33625646811333718794021167 50438470217000578191031751)
  ·
    refine ⟨75657705325500867286547627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50438470217000578191031751 75657705325500867286547627)
    ·
      refine ⟨113486557988251300929821441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75657705325500867286547627 113486557988251300929821441)
      ·
        refine ⟨85114918491188475697366081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113486557988251300929821441 85114918491188475697366081)
        ·
          refine ⟨63836188868391356773024561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85114918491188475697366081 63836188868391356773024561)
          ·
            refine ⟨47877141651293517579768421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63836188868391356773024561 47877141651293517579768421)
            ·
              refine ⟨8976964059617534546206579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47877141651293517579768421 8976964059617534546206579)
              ·
                refine ⟨13465446089426301819309869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976964059617534546206579 13465446089426301819309869)
                ·
                  refine ⟨5049542283534863182241201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13465446089426301819309869 5049542283534863182241201)
                  ·
                    refine ⟨3787156712651147386680901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5049542283534863182241201 3787156712651147386680901)
                    ·
                      refine ⟨710091883622090135002669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3787156712651147386680901 710091883622090135002669)
                      ·
                        rfl

theorem cell23_1382899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_1382899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382899 prefixEnd_1382899 := by exact prefixLift 1382899
  have htrace : WordTrace (prefixWord ++ tailWord_1382899) baseStart_1382899 baseEnd_1382899 := by
    simpa [prefixWord, tailWord_1382899, baseEnd_1382899] using wordTrace_append hprefix tailTrace_1382899
  have hstable : (prefixWord ++ tailWord_1382899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382899).length < 2 ^ (prefixWord ++ tailWord_1382899).sum := by decide
  have hdescent : baseEnd_1382899 < baseStart_1382899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382914 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1382914 : Nat := 118140960795 + 1382914 * 2 ^ 59
def prefixEnd_1382914 : Nat := 4983230072969 + 3 ^ 40 * 1382914 * 2
def baseEnd_1382914 : Nat := 710099585831907576315101

theorem tailTrace_1382914 : CollatzResearch.WordTrace tailWord_1382914 prefixEnd_1382914 710099585831907576315101 := by
  unfold tailWord_1382914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12609754327986558938206949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33626011541297490501885197 12609754327986558938206949)
  ·
    refine ⟨2364328936497479800913803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12609754327986558938206949 2364328936497479800913803)
    ·
      refine ⟨3546493404746219701370705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364328936497479800913803 3546493404746219701370705)
      ·
        refine ⟨2659870053559664776028029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3546493404746219701370705 2659870053559664776028029)
        ·
          refine ⟨997451270084874291010511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2659870053559664776028029 997451270084874291010511)
          ·
            refine ⟨1496176905127311436515767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997451270084874291010511 1496176905127311436515767)
            ·
              refine ⟨2244265357690967154773651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496176905127311436515767 2244265357690967154773651)
              ·
                refine ⟨3366398036536450732160477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244265357690967154773651 3366398036536450732160477)
                ·
                  refine ⟨1262399263701169024560179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3366398036536450732160477 1262399263701169024560179)
                  ·
                    refine ⟨1893598895551753536840269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1262399263701169024560179 1893598895551753536840269)
                    ·
                      refine ⟨710099585831907576315101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1893598895551753536840269 710099585831907576315101)
                      ·
                        rfl

theorem cell23_1382914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1382914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382914 prefixEnd_1382914 := by exact prefixLift 1382914
  have htrace : WordTrace (prefixWord ++ tailWord_1382914) baseStart_1382914 baseEnd_1382914 := by
    simpa [prefixWord, tailWord_1382914, baseEnd_1382914] using wordTrace_append hprefix tailTrace_1382914
  have hstable : (prefixWord ++ tailWord_1382914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382914).length < 2 ^ (prefixWord ++ tailWord_1382914).sum := by decide
  have hdescent : baseEnd_1382914 < baseStart_1382914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382916 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1382916 : Nat := 118140960795 + 1382916 * 2 ^ 59
def prefixEnd_1382916 : Nat := 4983230072969 + 3 ^ 40 * 1382916 * 2
def baseEnd_1382916 : Nat := 710100612793216568490091

theorem tailTrace_1382916 : CollatzResearch.WordTrace tailWord_1382916 prefixEnd_1382916 710100612793216568490091 := by
  unfold tailWord_1382916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219545128969495047200301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33626060171959326729600401 25219545128969495047200301)
  ·
    refine ⟨9457329423363560642700113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25219545128969495047200301 9457329423363560642700113)
    ·
      refine ⟨7092997067522670482025085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9457329423363560642700113 7092997067522670482025085)
      ·
        refine ⟨2659873900321001430759407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7092997067522670482025085 2659873900321001430759407)
        ·
          refine ⟨3989810850481502146139111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659873900321001430759407 3989810850481502146139111)
          ·
            refine ⟨5984716275722253219208667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989810850481502146139111 5984716275722253219208667)
            ·
              refine ⟨8977074413583379828813001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984716275722253219208667 8977074413583379828813001)
              ·
                refine ⟨6732805810187534871609751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8977074413583379828813001 6732805810187534871609751)
                ·
                  refine ⟨10099208715281302307414627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6732805810187534871609751 10099208715281302307414627)
                  ·
                    refine ⟨15148813072921953461121941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10099208715281302307414627 15148813072921953461121941)
                    ·
                      refine ⟨710100612793216568490091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15148813072921953461121941 710100612793216568490091)
                      ·
                        rfl

theorem cell23_1382916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1382916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382916 prefixEnd_1382916 := by exact prefixLift 1382916
  have htrace : WordTrace (prefixWord ++ tailWord_1382916) baseStart_1382916 baseEnd_1382916 := by
    simpa [prefixWord, tailWord_1382916, baseEnd_1382916] using wordTrace_append hprefix tailTrace_1382916
  have hstable : (prefixWord ++ tailWord_1382916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382916).length < 2 ^ (prefixWord ++ tailWord_1382916).sum := by decide
  have hdescent : baseEnd_1382916 < baseStart_1382916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382926 : List Nat := [4, 1, 1, 2, 3, 2, 2, 8]
def baseStart_1382926 : Nat := 118140960795 + 1382926 * 2 ^ 59
def prefixEnd_1382926 : Nat := 4983230072969 + 3 ^ 40 * 1382926 * 2
def baseEnd_1382926 : Nat := 26300212874065241828335

theorem tailTrace_1382926 : CollatzResearch.WordTrace tailWord_1382926 prefixEnd_1382926 26300212874065241828335 := by
  unfold tailWord_1382926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304931873487845225283079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33626303325268507868176421 6304931873487845225283079)
  ·
    refine ⟨9457397810231767837924619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6304931873487845225283079 9457397810231767837924619)
    ·
      refine ⟨14186096715347651756886929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9457397810231767837924619 14186096715347651756886929)
      ·
        refine ⟨10639572536510738817665197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14186096715347651756886929 10639572536510738817665197)
        ·
          refine ⟨3989839701191527056624449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10639572536510738817665197 3989839701191527056624449)
          ·
            refine ⟨2992379775893645292468337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3989839701191527056624449 2992379775893645292468337)
            ·
              refine ⟨2244284831920233969351253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992379775893645292468337 2244284831920233969351253)
              ·
                refine ⟨26300212874065241828335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2244284831920233969351253 26300212874065241828335)
                ·
                  rfl

theorem cell23_1382926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_1382926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382926 prefixEnd_1382926 := by exact prefixLift 1382926
  have htrace : WordTrace (prefixWord ++ tailWord_1382926) baseStart_1382926 baseEnd_1382926 := by
    simpa [prefixWord, tailWord_1382926, baseEnd_1382926] using wordTrace_append hprefix tailTrace_1382926
  have hstable : (prefixWord ++ tailWord_1382926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382926).length < 2 ^ (prefixWord ++ tailWord_1382926).sum := by decide
  have hdescent : baseEnd_1382926 < baseStart_1382926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382940 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1382940 : Nat := 118140960795 + 1382940 * 2 ^ 59
def prefixEnd_1382940 : Nat := 4983230072969 + 3 ^ 40 * 1382940 * 2
def baseEnd_1382940 : Nat := 710112936328924474589981

theorem tailTrace_1382940 : CollatzResearch.WordTrace tailWord_1382940 prefixEnd_1382940 710112936328924474589981 := by
  unfold tailWord_1382940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219982804926021096637137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33626643739901361462182849 25219982804926021096637137)
  ·
    refine ⟨18914987103694515822477853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25219982804926021096637137 18914987103694515822477853)
    ·
      refine ⟨7093120163885443433429195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18914987103694515822477853 7093120163885443433429195)
      ·
        refine ⟨10639680245828165150143793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7093120163885443433429195 10639680245828165150143793)
        ·
          refine ⟨7979760184371123862607845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10639680245828165150143793 7979760184371123862607845)
          ·
            refine ⟨1496205034569585724238971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7979760184371123862607845 1496205034569585724238971)
            ·
              refine ⟨2244307551854378586358457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496205034569585724238971 2244307551854378586358457)
              ·
                refine ⟨1683230663890783939768843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244307551854378586358457 1683230663890783939768843)
                ·
                  refine ⟨2524845995836175909653265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683230663890783939768843 2524845995836175909653265)
                  ·
                    refine ⟨1893634496877131932239949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524845995836175909653265 1893634496877131932239949)
                    ·
                      refine ⟨710112936328924474589981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1893634496877131932239949 710112936328924474589981)
                      ·
                        rfl

theorem cell23_1382940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1382940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382940 prefixEnd_1382940 := by exact prefixLift 1382940
  have htrace : WordTrace (prefixWord ++ tailWord_1382940) baseStart_1382940 baseEnd_1382940 := by
    simpa [prefixWord, tailWord_1382940, baseEnd_1382940] using wordTrace_append hprefix tailTrace_1382940
  have hstable : (prefixWord ++ tailWord_1382940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382940).length < 2 ^ (prefixWord ++ tailWord_1382940).sum := by decide
  have hdescent : baseEnd_1382940 < baseStart_1382940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382949 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1382949 : Nat := 118140960795 + 1382949 * 2 ^ 59
def prefixEnd_1382949 : Nat := 4983230072969 + 3 ^ 40 * 1382949 * 2
def baseEnd_1382949 : Nat := 710117557654814939377439

theorem tailTrace_1382949 : CollatzResearch.WordTrace tailWord_1382949 prefixEnd_1382949 710117557654814939377439 := by
  unfold tailWord_1382949
  simp only [CollatzResearch.WordTrace]
  refine ⟨50440293866819436730351901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33626862577879624486901267 50440293866819436730351901)
  ·
    refine ⟨18915110200057288773881963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50440293866819436730351901 18915110200057288773881963)
    ·
      refine ⟨28372665300085933160822945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18915110200057288773881963 28372665300085933160822945)
      ·
        refine ⟨21279498975064449870617209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28372665300085933160822945 21279498975064449870617209)
        ·
          refine ⟨15959624231298337402962907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21279498975064449870617209 15959624231298337402962907)
          ·
            refine ⟨23939436346947506104444361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15959624231298337402962907 23939436346947506104444361)
            ·
              refine ⟨17954577260210629578333271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23939436346947506104444361 17954577260210629578333271)
              ·
                refine ⟨26931865890315944367499907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17954577260210629578333271 26931865890315944367499907)
                ·
                  refine ⟨40397798835473916551249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26931865890315944367499907 40397798835473916551249861)
                  ·
                    refine ⟨7574587281651359353359349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40397798835473916551249861 7574587281651359353359349)
                    ·
                      refine ⟨710117557654814939377439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7574587281651359353359349 710117557654814939377439)
                      ·
                        rfl

theorem cell23_1382949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1382949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382949 prefixEnd_1382949 := by exact prefixLift 1382949
  have htrace : WordTrace (prefixWord ++ tailWord_1382949) baseStart_1382949 baseEnd_1382949 := by
    simpa [prefixWord, tailWord_1382949, baseEnd_1382949] using wordTrace_append hprefix tailTrace_1382949
  have hstable : (prefixWord ++ tailWord_1382949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382949).length < 2 ^ (prefixWord ++ tailWord_1382949).sum := by decide
  have hdescent : baseEnd_1382949 < baseStart_1382949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382959 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_1382959 : Nat := 118140960795 + 1382959 * 2 ^ 59
def prefixEnd_1382959 : Nat := 4983230072969 + 3 ^ 40 * 1382959 * 2
def baseEnd_1382959 : Nat := 710122692461359900252393

theorem tailTrace_1382959 : CollatzResearch.WordTrace tailWord_1382959 prefixEnd_1382959 710122692461359900252393 := by
  unfold tailWord_1382959
  simp only [CollatzResearch.WordTrace]
  refine ⟨50440658596783208438215931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33627105731188805625477287 50440658596783208438215931)
  ·
    refine ⟨75660987895174812657323897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50440658596783208438215931 75660987895174812657323897)
    ·
      refine ⟨56745740921381109492992923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75660987895174812657323897 56745740921381109492992923)
      ·
        refine ⟨85118611382071664239489385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56745740921381109492992923 85118611382071664239489385)
        ·
          refine ⟨63838958536553748179617039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85118611382071664239489385 63838958536553748179617039)
          ·
            refine ⟨95758437804830622269425559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63838958536553748179617039 95758437804830622269425559)
            ·
              refine ⟨143637656707245933404138339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95758437804830622269425559 143637656707245933404138339)
              ·
                refine ⟨215456485060868900106207509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143637656707245933404138339 215456485060868900106207509)
                ·
                  refine ⟨10099522737228229692478477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215456485060868900106207509 10099522737228229692478477)
                  ·
                    refine ⟨3787321026460586134679429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10099522737228229692478477 3787321026460586134679429)
                    ·
                      refine ⟨710122692461359900252393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3787321026460586134679429 710122692461359900252393)
                      ·
                        rfl

theorem cell23_1382959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_1382959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382959 prefixEnd_1382959 := by exact prefixLift 1382959
  have htrace : WordTrace (prefixWord ++ tailWord_1382959) baseStart_1382959 baseEnd_1382959 := by
    simpa [prefixWord, tailWord_1382959, baseEnd_1382959] using wordTrace_append hprefix tailTrace_1382959
  have hstable : (prefixWord ++ tailWord_1382959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382959).length < 2 ^ (prefixWord ++ tailWord_1382959).sum := by decide
  have hdescent : baseEnd_1382959 < baseStart_1382959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382970 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_1382970 : Nat := 118140960795 + 1382970 * 2 ^ 59
def prefixEnd_1382970 : Nat := 4983230072969 + 3 ^ 40 * 1382970 * 2
def baseEnd_1382970 : Nat := 710128340748559357214843

theorem tailTrace_1382970 : CollatzResearch.WordTrace tailWord_1382970 prefixEnd_1382970 710128340748559357214843 := by
  unfold tailWord_1382970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610264949935839329216591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33627373199828904877910909 12610264949935839329216591)
  ·
    refine ⟨18915397424903758993824887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12610264949935839329216591 18915397424903758993824887)
    ·
      refine ⟨28373096137355638490737331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18915397424903758993824887 28373096137355638490737331)
      ·
        refine ⟨42559644206033457736105997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28373096137355638490737331 42559644206033457736105997)
        ·
          refine ⟨15959866577262546651039749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42559644206033457736105997 15959866577262546651039749)
          ·
            refine ⟨2992474983236727497069953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15959866577262546651039749 2992474983236727497069953)
            ·
              refine ⟨2244356237427545622802465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992474983236727497069953 2244356237427545622802465)
              ·
                refine ⟨1683267178070659217101849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244356237427545622802465 1683267178070659217101849)
                ·
                  refine ⟨1262450383552994412826387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683267178070659217101849 1262450383552994412826387)
                  ·
                    refine ⟨1893675575329491619239581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1262450383552994412826387 1893675575329491619239581)
                    ·
                      refine ⟨710128340748559357214843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1893675575329491619239581 710128340748559357214843)
                      ·
                        rfl

theorem cell23_1382970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_1382970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382970 prefixEnd_1382970 := by exact prefixLift 1382970
  have htrace : WordTrace (prefixWord ++ tailWord_1382970) baseStart_1382970 baseEnd_1382970 := by
    simpa [prefixWord, tailWord_1382970, baseEnd_1382970] using wordTrace_append hprefix tailTrace_1382970
  have hstable : (prefixWord ++ tailWord_1382970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382970).length < 2 ^ (prefixWord ++ tailWord_1382970).sum := by decide
  have hdescent : baseEnd_1382970 < baseStart_1382970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382979 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1382979 : Nat := 118140960795 + 1382979 * 2 ^ 59
def prefixEnd_1382979 : Nat := 4983230072969 + 3 ^ 40 * 1382979 * 2
def baseEnd_1382979 : Nat := 710132962074449822002301

theorem tailTrace_1382979 : CollatzResearch.WordTrace tailWord_1382979 prefixEnd_1382979 710132962074449822002301 := by
  unfold tailWord_1382979
  simp only [CollatzResearch.WordTrace]
  refine ⟨50441388056710751853943991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33627592037807167902629327 50441388056710751853943991)
  ·
    refine ⟨75662082085066127780915987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50441388056710751853943991 75662082085066127780915987)
    ·
      refine ⟨113493123127599191671373981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75662082085066127780915987 113493123127599191671373981)
      ·
        refine ⟨42559921172849696876765243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113493123127599191671373981 42559921172849696876765243)
        ·
          refine ⟨63839881759274545315147865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42559921172849696876765243 63839881759274545315147865)
          ·
            refine ⟨47879911319455908986360899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63839881759274545315147865 47879911319455908986360899)
            ·
              refine ⟨71819866979183863479541349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47879911319455908986360899 71819866979183863479541349)
              ·
                refine ⟨13466225058596974402414003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71819866979183863479541349 13466225058596974402414003)
                ·
                  refine ⟨20199337587895461603621005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13466225058596974402414003 20199337587895461603621005)
                  ·
                    refine ⟨7574751595460798101357877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20199337587895461603621005 7574751595460798101357877)
                    ·
                      refine ⟨710132962074449822002301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7574751595460798101357877 710132962074449822002301)
                      ·
                        rfl

theorem cell23_1382979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1382979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382979 prefixEnd_1382979 := by exact prefixLift 1382979
  have htrace : WordTrace (prefixWord ++ tailWord_1382979) baseStart_1382979 baseEnd_1382979 := by
    simpa [prefixWord, tailWord_1382979, baseEnd_1382979] using wordTrace_append hprefix tailTrace_1382979
  have hstable : (prefixWord ++ tailWord_1382979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382979).length < 2 ^ (prefixWord ++ tailWord_1382979).sum := by decide
  have hdescent : baseEnd_1382979 < baseStart_1382979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382986 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_1382986 : Nat := 118140960795 + 1382986 * 2 ^ 59
def prefixEnd_1382986 : Nat := 4983230072969 + 3 ^ 40 * 1382986 * 2
def baseEnd_1382986 : Nat := 236712185479677098204923

theorem tailTrace_1382986 : CollatzResearch.WordTrace tailWord_1382986 prefixEnd_1382986 236712185479677098204923 := by
  unfold tailWord_1382986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610410841921348012362203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33627762245123594699632541 12610410841921348012362203)
  ·
    refine ⟨18915616262882022018543305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12610410841921348012362203 18915616262882022018543305)
    ·
      refine ⟨14186712197161516513907479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18915616262882022018543305 14186712197161516513907479)
      ·
        refine ⟨21280068295742274770861219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14186712197161516513907479 21280068295742274770861219)
        ·
          refine ⟨31920102443613412156291829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21280068295742274770861219 31920102443613412156291829)
          ·
            refine ⟨2992509604088757389652359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31920102443613412156291829 2992509604088757389652359)
            ·
              refine ⟨4488764406133136084478539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992509604088757389652359 4488764406133136084478539)
              ·
                refine ⟨6733146609199704126717809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488764406133136084478539 6733146609199704126717809)
                ·
                  refine ⟨5049859956899778095038357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6733146609199704126717809 5049859956899778095038357)
                  ·
                    refine ⟨236712185479677098204923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5049859956899778095038357 236712185479677098204923)
                    ·
                      rfl

theorem cell23_1382986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_1382986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382986 prefixEnd_1382986 := by exact prefixLift 1382986
  have htrace : WordTrace (prefixWord ++ tailWord_1382986) baseStart_1382986 baseEnd_1382986 := by
    simpa [prefixWord, tailWord_1382986, baseEnd_1382986] using wordTrace_append hprefix tailTrace_1382986
  have hstable : (prefixWord ++ tailWord_1382986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382986).length < 2 ^ (prefixWord ++ tailWord_1382986).sum := by decide
  have hdescent : baseEnd_1382986 < baseStart_1382986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382993 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 1, 4, 2]
def baseStart_1382993 : Nat := 118140960795 + 1382993 * 2 ^ 59
def prefixEnd_1382993 : Nat := 4983230072969 + 3 ^ 40 * 1382993 * 2
def baseEnd_1382993 : Nat := 710140150803612767227237

theorem tailTrace_1382993 : CollatzResearch.WordTrace tailWord_1382993 prefixEnd_1382993 710140150803612767227237 := by
  unfold tailWord_1382993
  simp only [CollatzResearch.WordTrace]
  refine ⟨50441898678660032244953633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33627932452440021496635755 50441898678660032244953633)
  ·
    refine ⟨37831424008995024183715225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50441898678660032244953633 37831424008995024183715225)
    ·
      refine ⟨28373568006746268137786419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37831424008995024183715225 28373568006746268137786419)
      ·
        refine ⟨42560352010119402206679629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28373568006746268137786419 42560352010119402206679629)
        ·
          refine ⟨15960132003794775827504861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42560352010119402206679629 15960132003794775827504861)
          ·
            refine ⟨5985049501423040935314323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15960132003794775827504861 5985049501423040935314323)
            ·
              refine ⟨8977574252134561402971485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985049501423040935314323 8977574252134561402971485)
              ·
                refine ⟨3366590344550460526114307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8977574252134561402971485 3366590344550460526114307)
                ·
                  refine ⟨5049885516825690789171461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366590344550460526114307 5049885516825690789171461)
                  ·
                    refine ⟨946853534404817022969649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049885516825690789171461 946853534404817022969649)
                    ·
                      refine ⟨710140150803612767227237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946853534404817022969649 710140150803612767227237)
                      ·
                        rfl

theorem cell23_1382993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_1382993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1382993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1382993 prefixEnd_1382993 := by exact prefixLift 1382993
  have htrace : WordTrace (prefixWord ++ tailWord_1382993) baseStart_1382993 baseEnd_1382993 := by
    simpa [prefixWord, tailWord_1382993, baseEnd_1382993] using wordTrace_append hprefix tailTrace_1382993
  have hstable : (prefixWord ++ tailWord_1382993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382993).length < 2 ^ (prefixWord ++ tailWord_1382993).sum := by decide
  have hdescent : baseEnd_1382993 < baseStart_1382993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383033 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 5]
def baseStart_1383033 : Nat := 118140960795 + 1383033 * 2 ^ 59
def prefixEnd_1383033 : Nat := 4983230072969 + 3 ^ 40 * 1383033 * 2
def baseEnd_1383033 : Nat := 78906743336643623414117

theorem tailTrace_1383033 : CollatzResearch.WordTrace tailWord_1383033 prefixEnd_1383033 78906743336643623414117 := by
  unfold tailWord_1383033
  simp only [CollatzResearch.WordTrace]
  refine ⟨50443357598515119076409753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33628905065676746050939835 50443357598515119076409753)
  ·
    refine ⟨37832518198886339307307315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50443357598515119076409753 37832518198886339307307315)
    ·
      refine ⟨56748777298329508960960973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37832518198886339307307315 56748777298329508960960973)
      ·
        refine ⟨21280791486873565860360365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56748777298329508960960973 21280791486873565860360365)
        ·
          refine ⟨7980296807577587197635137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21280791486873565860360365 7980296807577587197635137)
          ·
            refine ⟨5985222605683190398226353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980296807577587197635137 5985222605683190398226353)
            ·
              refine ⟨4488916954262392798669765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985222605683190398226353 4488916954262392798669765)
              ·
                refine ⟨841671928924198649750581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4488916954262392798669765 841671928924198649750581)
                ·
                  refine ⟨78906743336643623414117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 841671928924198649750581 78906743336643623414117)
                  ·
                    rfl

theorem cell23_1383033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 5].length) (baseStart_1383033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383033 prefixEnd_1383033 := by exact prefixLift 1383033
  have htrace : WordTrace (prefixWord ++ tailWord_1383033) baseStart_1383033 baseEnd_1383033 := by
    simpa [prefixWord, tailWord_1383033, baseEnd_1383033] using wordTrace_append hprefix tailTrace_1383033
  have hstable : (prefixWord ++ tailWord_1383033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383033).length < 2 ^ (prefixWord ++ tailWord_1383033).sum := by decide
  have hdescent : baseEnd_1383033 < baseStart_1383033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383044 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_1383044 : Nat := 118140960795 + 1383044 * 2 ^ 59
def prefixEnd_1383044 : Nat := 4983230072969 + 3 ^ 40 * 1383044 * 2
def baseEnd_1383044 : Nat := 710166338316992067689503

theorem tailTrace_1383044 : CollatzResearch.WordTrace tailWord_1383044 prefixEnd_1383044 710166338316992067689503 := by
  unfold tailWord_1383044
  simp only [CollatzResearch.WordTrace]
  refine ⟨25221879400737633977530093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33629172534316845303373457 25221879400737633977530093)
  ·
    refine ⟨9458204775276612741573785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25221879400737633977530093 9458204775276612741573785)
    ·
      refine ⟨7093653581457459556180339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9458204775276612741573785 7093653581457459556180339)
      ·
        refine ⟨10640480372186189334270509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7093653581457459556180339 10640480372186189334270509)
        ·
          refine ⟨3990180139569821000351441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10640480372186189334270509 3990180139569821000351441)
          ·
            refine ⟨2992635104677365750263581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3990180139569821000351441 2992635104677365750263581)
            ·
              refine ⟨1122238164254012156348843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2992635104677365750263581 1122238164254012156348843)
              ·
                refine ⟨1683357246381018234523265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122238164254012156348843 1683357246381018234523265)
                ·
                  refine ⟨1262517934785763675892449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683357246381018234523265 1262517934785763675892449)
                  ·
                    refine ⟨946888451089322756919337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1262517934785763675892449 946888451089322756919337)
                    ·
                      refine ⟨710166338316992067689503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 946888451089322756919337 710166338316992067689503)
                      ·
                        rfl

theorem cell23_1383044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_1383044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383044 prefixEnd_1383044 := by exact prefixLift 1383044
  have htrace : WordTrace (prefixWord ++ tailWord_1383044) baseStart_1383044 baseEnd_1383044 := by
    simpa [prefixWord, tailWord_1383044, baseEnd_1383044] using wordTrace_append hprefix tailTrace_1383044
  have hstable : (prefixWord ++ tailWord_1383044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383044).length < 2 ^ (prefixWord ++ tailWord_1383044).sum := by decide
  have hdescent : baseEnd_1383044 < baseStart_1383044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383170 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1383170 : Nat := 118140960795 + 1383170 * 2 ^ 59
def prefixEnd_1383170 : Nat := 4983230072969 + 3 ^ 40 * 1383170 * 2
def baseEnd_1383170 : Nat := 236743678959819524904641

theorem tailTrace_1383170 : CollatzResearch.WordTrace tailWord_1383170 prefixEnd_1383170 236743678959819524904641 := by
  unfold tailWord_1383170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612088599754697868536741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33632236266012527649431309 12612088599754697868536741)
  ·
    refine ⟨2364766612454005850350639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12612088599754697868536741 2364766612454005850350639)
    ·
      refine ⟨3547149918681008775525959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364766612454005850350639 3547149918681008775525959)
      ·
        refine ⟨5320724878021513163288939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3547149918681008775525959 5320724878021513163288939)
        ·
          refine ⟨7981087317032269744933409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320724878021513163288939 7981087317032269744933409)
          ·
            refine ⟨5985815487774202308700057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7981087317032269744933409 5985815487774202308700057)
            ·
              refine ⟨4489361615830651731525043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985815487774202308700057 4489361615830651731525043)
              ·
                refine ⟨6734042423745977597287565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489361615830651731525043 6734042423745977597287565)
                ·
                  refine ⟨2525265908904741598982837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6734042423745977597287565 2525265908904741598982837)
                  ·
                    refine ⟨236743678959819524904641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2525265908904741598982837 236743678959819524904641)
                    ·
                      rfl

theorem cell23_1383170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1383170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383170 prefixEnd_1383170 := by exact prefixLift 1383170
  have htrace : WordTrace (prefixWord ++ tailWord_1383170) baseStart_1383170 baseEnd_1383170 := by
    simpa [prefixWord, tailWord_1383170, baseEnd_1383170] using wordTrace_append hprefix tailTrace_1383170
  have hstable : (prefixWord ++ tailWord_1383170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383170).length < 2 ^ (prefixWord ++ tailWord_1383170).sum := by decide
  have hdescent : baseEnd_1383170 < baseStart_1383170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383183 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 4, 4]
def baseStart_1383183 : Nat := 118140960795 + 1383183 * 2 ^ 59
def prefixEnd_1383183 : Nat := 4983230072969 + 3 ^ 40 * 1383183 * 2
def baseEnd_1383183 : Nat := 236745904042655674617121

theorem tailTrace_1383183 : CollatzResearch.WordTrace tailWord_1383183 prefixEnd_1383183 236745904042655674617121 := by
  unfold tailWord_1383183
  simp only [CollatzResearch.WordTrace]
  refine ⟨50448828547971694694370203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33632552365314463129580135 50448828547971694694370203)
  ·
    refine ⟨75673242821957542041555305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50448828547971694694370203 75673242821957542041555305)
    ·
      refine ⟨56754932116468156531166479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75673242821957542041555305 56754932116468156531166479)
      ·
        refine ⟨85132398174702234796749719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56754932116468156531166479 85132398174702234796749719)
        ·
          refine ⟨127698597262053352195124579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85132398174702234796749719 127698597262053352195124579)
          ·
            refine ⟨191547895893080028292686869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127698597262053352195124579 191547895893080028292686869)
            ·
              refine ⟨8978807619988126326219697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191547895893080028292686869 8978807619988126326219697)
              ·
                refine ⟨6734105714991094744664773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8978807619988126326219697 6734105714991094744664773)
                ·
                  refine ⟨1262644821560830264624645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6734105714991094744664773 1262644821560830264624645)
                  ·
                    refine ⟨236745904042655674617121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262644821560830264624645 236745904042655674617121)
                    ·
                      rfl

theorem cell23_1383183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_1383183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383183 prefixEnd_1383183 := by exact prefixLift 1383183
  have htrace : WordTrace (prefixWord ++ tailWord_1383183) baseStart_1383183 baseEnd_1383183 := by
    simpa [prefixWord, tailWord_1383183, baseEnd_1383183] using wordTrace_append hprefix tailTrace_1383183
  have hstable : (prefixWord ++ tailWord_1383183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383183).length < 2 ^ (prefixWord ++ tailWord_1383183).sum := by decide
  have hdescent : baseEnd_1383183 < baseStart_1383183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383193 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_1383193 : Nat := 118140960795 + 1383193 * 2 ^ 59
def prefixEnd_1383193 : Nat := 4983230072969 + 3 ^ 40 * 1383193 * 2
def baseEnd_1383193 : Nat := 710242846934511984726317

theorem tailTrace_1383193 : CollatzResearch.WordTrace tailWord_1383193 prefixEnd_1383193 710242846934511984726317 := by
  unfold tailWord_1383193
  simp only [CollatzResearch.WordTrace]
  refine ⟨50449193277935466402234233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33632795518623644268156155 50449193277935466402234233)
  ·
    refine ⟨37836894958451599801675675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50449193277935466402234233 37836894958451599801675675)
    ·
      refine ⟨56755342437677399702513513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37836894958451599801675675 56755342437677399702513513)
      ·
        refine ⟨42566506828258049776885135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56755342437677399702513513 42566506828258049776885135)
        ·
          refine ⟨63849760242387074665327703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42566506828258049776885135 63849760242387074665327703)
          ·
            refine ⟨95774640363580611997991555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63849760242387074665327703 95774640363580611997991555)
            ·
              refine ⟨143661960545370917996987333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95774640363580611997991555 143661960545370917996987333)
              ·
                refine ⟨26936617602257047124435125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143661960545370917996987333 26936617602257047124435125)
                ·
                  refine ⟨2525307900211598167915793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26936617602257047124435125 2525307900211598167915793)
                  ·
                    refine ⟨1893980925158698625936845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2525307900211598167915793 1893980925158698625936845)
                    ·
                      refine ⟨710242846934511984726317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1893980925158698625936845 710242846934511984726317)
                      ·
                        rfl

theorem cell23_1383193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_1383193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383193 prefixEnd_1383193 := by exact prefixLift 1383193
  have htrace : WordTrace (prefixWord ++ tailWord_1383193) baseStart_1383193 baseEnd_1383193 := by
    simpa [prefixWord, tailWord_1383193, baseEnd_1383193] using wordTrace_append hprefix tailTrace_1383193
  have hstable : (prefixWord ++ tailWord_1383193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383193).length < 2 ^ (prefixWord ++ tailWord_1383193).sum := by decide
  have hdescent : baseEnd_1383193 < baseStart_1383193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383200 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 4, 4]
def baseStart_1383200 : Nat := 118140960795 + 1383200 * 2 ^ 59
def prefixEnd_1383200 : Nat := 4983230072969 + 3 ^ 40 * 1383200 * 2
def baseEnd_1383200 : Nat := 236748813766364485779595

theorem tailTrace_1383200 : CollatzResearch.WordTrace tailWord_1383200 prefixEnd_1383200 236748813766364485779595 := by
  unfold tailWord_1383200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25224724294455053298869527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33632965725940071065159369 25224724294455053298869527)
  ·
    refine ⟨37837086441682579948304291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25224724294455053298869527 37837086441682579948304291)
    ·
      refine ⟨56755629662523869922456437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37837086441682579948304291 56755629662523869922456437)
      ·
        refine ⟨5320840280861612805230291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56755629662523869922456437 5320840280861612805230291)
        ·
          refine ⟨7981260421292419207845437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320840280861612805230291 7981260421292419207845437)
          ·
            refine ⟨2992972657984657202942039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7981260421292419207845437 2992972657984657202942039)
            ·
              refine ⟨4489458986976985804413059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992972657984657202942039 4489458986976985804413059)
              ·
                refine ⟨6734188480465478706619589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489458986976985804413059 6734188480465478706619589)
                ·
                  refine ⟨1262660340087277257491173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6734188480465478706619589 1262660340087277257491173)
                  ·
                    refine ⟨236748813766364485779595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262660340087277257491173 236748813766364485779595)
                    ·
                      rfl

theorem cell23_1383200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_1383200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383200 prefixEnd_1383200 := by exact prefixLift 1383200
  have htrace : WordTrace (prefixWord ++ tailWord_1383200) baseStart_1383200 baseEnd_1383200 := by
    simpa [prefixWord, tailWord_1383200, baseEnd_1383200] using wordTrace_append hprefix tailTrace_1383200
  have hstable : (prefixWord ++ tailWord_1383200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383200).length < 2 ^ (prefixWord ++ tailWord_1383200).sum := by decide
  have hdescent : baseEnd_1383200 < baseStart_1383200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383217 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 2, 4]
def baseStart_1383217 : Nat := 118140960795 + 1383217 * 2 ^ 59
def prefixEnd_1383217 : Nat := 4983230072969 + 3 ^ 40 * 1383217 * 2
def baseEnd_1383217 : Nat := 236751723490073296942069

theorem tailTrace_1383217 : CollatzResearch.WordTrace tailWord_1383217 prefixEnd_1383217 236751723490073296942069 := by
  unfold tailWord_1383217
  simp only [CollatzResearch.WordTrace]
  refine ⟨50450068629848518501107905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33633379086565679000738603 50450068629848518501107905)
  ·
    refine ⟨37837551472386388875830929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50450068629848518501107905 37837551472386388875830929)
    ·
      refine ⟨28378163604289791656873197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37837551472386388875830929 28378163604289791656873197)
      ·
        refine ⟨10641811351608671871327449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28378163604289791656873197 10641811351608671871327449)
        ·
          refine ⟨7981358513706503903495587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641811351608671871327449 7981358513706503903495587)
          ·
            refine ⟨11972037770559755855243381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981358513706503903495587 11972037770559755855243381)
            ·
              refine ⟨1122378540989977111429067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11972037770559755855243381 1122378540989977111429067)
              ·
                refine ⟨1683567811484965667143601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122378540989977111429067 1683567811484965667143601)
                ·
                  refine ⟨1262675858613724250357701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683567811484965667143601 1262675858613724250357701)
                  ·
                    refine ⟨236751723490073296942069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262675858613724250357701 236751723490073296942069)
                    ·
                      rfl

theorem cell23_1383217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_1383217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383217 prefixEnd_1383217 := by exact prefixLift 1383217
  have htrace : WordTrace (prefixWord ++ tailWord_1383217) baseStart_1383217 baseEnd_1383217 := by
    simpa [prefixWord, tailWord_1383217, baseEnd_1383217] using wordTrace_append hprefix tailTrace_1383217
  have hstable : (prefixWord ++ tailWord_1383217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383217).length < 2 ^ (prefixWord ++ tailWord_1383217).sum := by decide
  have hdescent : baseEnd_1383217 < baseStart_1383217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383230 : List Nat := [4, 2, 1, 2, 3, 1, 1, 9]
def baseStart_1383230 : Nat := 118140960795 + 1383230 * 2 ^ 59
def prefixEnd_1383230 : Nat := 4983230072969 + 3 ^ 40 * 1383230 * 2
def baseEnd_1383230 : Nat := 26305994285878827406061

theorem tailTrace_1383230 : CollatzResearch.WordTrace tailWord_1383230 prefixEnd_1383230 26305994285878827406061 := by
  unfold tailWord_1383230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306317847350177715166393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33633695185867614480887429 6306317847350177715166393)
  ·
    refine ⟨4729738385512633286374795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6306317847350177715166393 4729738385512633286374795)
    ·
      refine ⟨7094607578268949929562193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4729738385512633286374795 7094607578268949929562193)
      ·
        refine ⟨5320955683701712447171645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7094607578268949929562193 5320955683701712447171645)
        ·
          refine ⟨1995358381388142167689367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5320955683701712447171645 1995358381388142167689367)
          ·
            refine ⟨2993037572082213251534051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995358381388142167689367 2993037572082213251534051)
            ·
              refine ⟨4489556358123319877301077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993037572082213251534051 4489556358123319877301077)
              ·
                refine ⟨26305994285878827406061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4489556358123319877301077 26305994285878827406061)
                ·
                  rfl

theorem cell23_1383230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_1383230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383230 prefixEnd_1383230 := by exact prefixLift 1383230
  have htrace : WordTrace (prefixWord ++ tailWord_1383230) baseStart_1383230 baseEnd_1383230 := by
    simpa [prefixWord, tailWord_1383230, baseEnd_1383230] using wordTrace_append hprefix tailTrace_1383230
  have hstable : (prefixWord ++ tailWord_1383230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383230).length < 2 ^ (prefixWord ++ tailWord_1383230).sum := by decide
  have hdescent : baseEnd_1383230 < baseStart_1383230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383240 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_1383240 : Nat := 118140960795 + 1383240 * 2 ^ 59
def prefixEnd_1383240 : Nat := 4983230072969 + 3 ^ 40 * 1383240 * 2
def baseEnd_1383240 : Nat := 710266980525273300838601

theorem tailTrace_1383240 : CollatzResearch.WordTrace tailWord_1383240 prefixEnd_1383240 710266980525273300838601 := by
  unfold tailWord_1383240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25225453754382596714597587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33633938339176795619463449 25225453754382596714597587)
  ·
    refine ⟨37838180631573895071896381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25225453754382596714597587 37838180631573895071896381)
    ·
      refine ⟨14189317736840210651961143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37838180631573895071896381 14189317736840210651961143)
      ·
        refine ⟨21283976605260315977941715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14189317736840210651961143 21283976605260315977941715)
        ·
          refine ⟨31925964907890473966912573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21283976605260315977941715 31925964907890473966912573)
          ·
            refine ⟨11972236840458927737592215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31925964907890473966912573 11972236840458927737592215)
            ·
              refine ⟨17958355260688391606388323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11972236840458927737592215 17958355260688391606388323)
              ·
                refine ⟨26937532891032587409582485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17958355260688391606388323 26937532891032587409582485)
                ·
                  refine ⟨1262696854267152534824179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26937532891032587409582485 1262696854267152534824179)
                  ·
                    refine ⟨1894045281400728802236269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1262696854267152534824179 1894045281400728802236269)
                    ·
                      refine ⟨710266980525273300838601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1894045281400728802236269 710266980525273300838601)
                      ·
                        rfl

theorem cell23_1383240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_1383240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383240 prefixEnd_1383240 := by exact prefixLift 1383240
  have htrace : WordTrace (prefixWord ++ tailWord_1383240) baseStart_1383240 baseEnd_1383240 := by
    simpa [prefixWord, tailWord_1383240, baseEnd_1383240] using wordTrace_append hprefix tailTrace_1383240
  have hstable : (prefixWord ++ tailWord_1383240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383240).length < 2 ^ (prefixWord ++ tailWord_1383240).sum := by decide
  have hdescent : baseEnd_1383240 < baseStart_1383240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383241 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 1, 2, 2]
def baseStart_1383241 : Nat := 118140960795 + 1383241 * 2 ^ 59
def prefixEnd_1383241 : Nat := 4983230072969 + 3 ^ 40 * 1383241 * 2
def baseEnd_1383241 : Nat := 710267494005927796926097

theorem tailTrace_1383241 : CollatzResearch.WordTrace tailWord_1383241 prefixEnd_1383241 710267494005927796926097 := by
  unfold tailWord_1383241
  simp only [CollatzResearch.WordTrace]
  refine ⟨50450943981761570599981577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33633962654507713733321051 50450943981761570599981577)
  ·
    refine ⟨37838207986321177949986183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50450943981761570599981577 37838207986321177949986183)
    ·
      refine ⟨56757311979481766924979275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37838207986321177949986183 56757311979481766924979275)
      ·
        refine ⟨85135967969222650387468913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56757311979481766924979275 85135967969222650387468913)
        ·
          refine ⟨63851975976916987790601685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85135967969222650387468913 63851975976916987790601685)
          ·
            refine ⟨1496530686958991901342227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 63851975976916987790601685 1496530686958991901342227)
            ·
              refine ⟨2244796030438487852013341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496530686958991901342227 2244796030438487852013341)
              ·
                refine ⟨841798511414432944505003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2244796030438487852013341 841798511414432944505003)
                ·
                  refine ⟨1262697767121649416757505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841798511414432944505003 1262697767121649416757505)
                  ·
                    refine ⟨947023325341237062568129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1262697767121649416757505 947023325341237062568129)
                    ·
                      refine ⟨710267494005927796926097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947023325341237062568129 710267494005927796926097)
                      ·
                        rfl

theorem cell23_1383241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 2, 2].length) (baseStart_1383241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383241 prefixEnd_1383241 := by exact prefixLift 1383241
  have htrace : WordTrace (prefixWord ++ tailWord_1383241) baseStart_1383241 baseEnd_1383241 := by
    simpa [prefixWord, tailWord_1383241, baseEnd_1383241] using wordTrace_append hprefix tailTrace_1383241
  have hstable : (prefixWord ++ tailWord_1383241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383241).length < 2 ^ (prefixWord ++ tailWord_1383241).sum := by decide
  have hdescent : baseEnd_1383241 < baseStart_1383241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383253 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1383253 : Nat := 118140960795 + 1383253 * 2 ^ 59
def prefixEnd_1383253 : Nat := 4983230072969 + 3 ^ 40 * 1383253 * 2
def baseEnd_1383253 : Nat := 710273655773781749976041

theorem tailTrace_1383253 : CollatzResearch.WordTrace tailWord_1383253 prefixEnd_1383253 710273655773781749976041 := by
  unfold tailWord_1383253
  simp only [CollatzResearch.WordTrace]
  refine ⟨50451381657718096649418413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33634254438478731099612275 50451381657718096649418413)
  ·
    refine ⟨18919268121644286243531905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50451381657718096649418413 18919268121644286243531905)
    ·
      refine ⟨14189451091233214682648929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18919268121644286243531905 14189451091233214682648929)
      ·
        refine ⟨10642088318424911011986697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14189451091233214682648929 10642088318424911011986697)
        ·
          refine ⟨7981566238818683258990023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10642088318424911011986697 7981566238818683258990023)
          ·
            refine ⟨11972349358228024888485035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981566238818683258990023 11972349358228024888485035)
            ·
              refine ⟨17958524037342037332727553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11972349358228024888485035 17958524037342037332727553)
              ·
                refine ⟨13468893028006527999545665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17958524037342037332727553 13468893028006527999545665)
                ·
                  refine ⟨10101669771004895999659249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13468893028006527999545665 10101669771004895999659249)
                  ·
                    refine ⟨7576252328253671999744437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10101669771004895999659249 7576252328253671999744437)
                    ·
                      refine ⟨710273655773781749976041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7576252328253671999744437 710273655773781749976041)
                      ·
                        rfl

theorem cell23_1383253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1383253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383253 prefixEnd_1383253 := by exact prefixLift 1383253
  have htrace : WordTrace (prefixWord ++ tailWord_1383253) baseStart_1383253 baseEnd_1383253 := by
    simpa [prefixWord, tailWord_1383253, baseEnd_1383253] using wordTrace_append hprefix tailTrace_1383253
  have hstable : (prefixWord ++ tailWord_1383253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383253).length < 2 ^ (prefixWord ++ tailWord_1383253).sum := by decide
  have hdescent : baseEnd_1383253 < baseStart_1383253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383263 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1383263 : Nat := 118140960795 + 1383263 * 2 ^ 59
def prefixEnd_1383263 : Nat := 4983230072969 + 3 ^ 40 * 1383263 * 2
def baseEnd_1383263 : Nat := 710278790580326710850995

theorem tailTrace_1383263 : CollatzResearch.WordTrace tailWord_1383263 prefixEnd_1383263 710278790580326710850995 := by
  unfold tailWord_1383263
  simp only [CollatzResearch.WordTrace]
  refine ⟨50451746387681868357282443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33634497591787912238188295 50451746387681868357282443)
  ·
    refine ⟨75677619581522802535923665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50451746387681868357282443 75677619581522802535923665)
    ·
      refine ⟨56758214686142101901942749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75677619581522802535923665 56758214686142101901942749)
      ·
        refine ⟨21284330507303288213228531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56758214686142101901942749 21284330507303288213228531)
        ·
          refine ⟨31926495760954932319842797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21284330507303288213228531 31926495760954932319842797)
          ·
            refine ⟨11972435910358099619941049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31926495760954932319842797 11972435910358099619941049)
            ·
              refine ⟨8979326932768574714955787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11972435910358099619941049 8979326932768574714955787)
              ·
                refine ⟨13468990399152862072433681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8979326932768574714955787 13468990399152862072433681)
                ·
                  refine ⟨10101742799364646554325261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13468990399152862072433681 10101742799364646554325261)
                  ·
                    refine ⟨3788153549761742457871973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10101742799364646554325261 3788153549761742457871973)
                    ·
                      refine ⟨710278790580326710850995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3788153549761742457871973 710278790580326710850995)
                      ·
                        rfl

theorem cell23_1383263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1383263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383263 prefixEnd_1383263 := by exact prefixLift 1383263
  have htrace : WordTrace (prefixWord ++ tailWord_1383263) baseStart_1383263 baseEnd_1383263 := by
    simpa [prefixWord, tailWord_1383263, baseEnd_1383263] using wordTrace_append hprefix tailTrace_1383263
  have hstable : (prefixWord ++ tailWord_1383263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383263).length < 2 ^ (prefixWord ++ tailWord_1383263).sum := by decide
  have hdescent : baseEnd_1383263 < baseStart_1383263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383283 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5]
def baseStart_1383283 : Nat := 118140960795 + 1383283 * 2 ^ 59
def prefixEnd_1383283 : Nat := 4983230072969 + 3 ^ 40 * 1383283 * 2
def baseEnd_1383283 : Nat := 710289060193416632600903

theorem tailTrace_1383283 : CollatzResearch.WordTrace tailWord_1383283 prefixEnd_1383283 710289060193416632600903 := by
  unfold tailWord_1383283
  simp only [CollatzResearch.WordTrace]
  refine ⟨50452475847609411773010503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33634983898406274515340335 50452475847609411773010503)
  ·
    refine ⟨75678713771414117659515755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50452475847609411773010503 75678713771414117659515755)
    ·
      refine ⟨113518070657121176489273633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75678713771414117659515755 113518070657121176489273633)
      ·
        refine ⟨85138552992840882366955225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113518070657121176489273633 85138552992840882366955225)
        ·
          refine ⟨63853914744630661775216419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85138552992840882366955225 63853914744630661775216419)
          ·
            refine ⟨95780872116945992662824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63853914744630661775216419 95780872116945992662824629)
            ·
              refine ⟨8979456760963686812139809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95780872116945992662824629 8979456760963686812139809)
              ·
                refine ⟨6734592570722765109104857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8979456760963686812139809 6734592570722765109104857)
                ·
                  refine ⟨5050944428042073831828643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6734592570722765109104857 5050944428042073831828643)
                  ·
                    refine ⟨7576416642063110747742965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5050944428042073831828643 7576416642063110747742965)
                    ·
                      refine ⟨710289060193416632600903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7576416642063110747742965 710289060193416632600903)
                      ·
                        rfl

theorem cell23_1383283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_1383283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383283 prefixEnd_1383283 := by exact prefixLift 1383283
  have htrace : WordTrace (prefixWord ++ tailWord_1383283) baseStart_1383283 baseEnd_1383283 := by
    simpa [prefixWord, tailWord_1383283, baseEnd_1383283] using wordTrace_append hprefix tailTrace_1383283
  have hstable : (prefixWord ++ tailWord_1383283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383283).length < 2 ^ (prefixWord ++ tailWord_1383283).sum := by decide
  have hdescent : baseEnd_1383283 < baseStart_1383283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383343 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_1383343 : Nat := 118140960795 + 1383343 * 2 ^ 59
def prefixEnd_1383343 : Nat := 4983230072969 + 3 ^ 40 * 1383343 * 2
def baseEnd_1383343 : Nat := 710319869032686397850627

theorem tailTrace_1383343 : CollatzResearch.WordTrace tailWord_1383343 prefixEnd_1383343 710319869032686397850627 := by
  unfold tailWord_1383343
  simp only [CollatzResearch.WordTrace]
  refine ⟨50454664227392042020194683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33636442818261361346796455 50454664227392042020194683)
  ·
    refine ⟨75681996341088063030292025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50454664227392042020194683 75681996341088063030292025)
    ·
      refine ⟨56761497255816047272719019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75681996341088063030292025 56761497255816047272719019)
      ·
        refine ⟨85142245883724070909078529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56761497255816047272719019 85142245883724070909078529)
        ·
          refine ⟨63856684412793053181808897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85142245883724070909078529 63856684412793053181808897)
          ·
            refine ⟨47892513309594789886356673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63856684412793053181808897 47892513309594789886356673)
            ·
              refine ⟨35919384982196092414767505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47892513309594789886356673 35919384982196092414767505)
              ·
                refine ⟨26939538736647069311075629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35919384982196092414767505 26939538736647069311075629)
                ·
                  refine ⟨10102327026242650991653361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26939538736647069311075629 10102327026242650991653361)
                  ·
                    refine ⟨7576745269681988243740021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10102327026242650991653361 7576745269681988243740021)
                    ·
                      refine ⟨710319869032686397850627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7576745269681988243740021 710319869032686397850627)
                      ·
                        rfl

theorem cell23_1383343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_1383343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383343 prefixEnd_1383343 := by exact prefixLift 1383343
  have htrace : WordTrace (prefixWord ++ tailWord_1383343) baseStart_1383343 baseEnd_1383343 := by
    simpa [prefixWord, tailWord_1383343, baseEnd_1383343] using wordTrace_append hprefix tailTrace_1383343
  have hstable : (prefixWord ++ tailWord_1383343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383343).length < 2 ^ (prefixWord ++ tailWord_1383343).sum := by decide
  have hdescent : baseEnd_1383343 < baseStart_1383343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383370 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1383370 : Nat := 118140960795 + 1383370 * 2 ^ 59
def prefixEnd_1383370 : Nat := 4983230072969 + 3 ^ 40 * 1383370 * 2
def baseEnd_1383370 : Nat := 710333733010357792213003

theorem tailTrace_1383370 : CollatzResearch.WordTrace tailWord_1383370 prefixEnd_1383370 710333733010357792213003 := by
  unfold tailWord_1383370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613912249573556407856891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33637099332196150420951709 12613912249573556407856891)
  ·
    refine ⟨18920868374360334611785337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12613912249573556407856891 18920868374360334611785337)
    ·
      refine ⟨14190651280770250958839003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18920868374360334611785337 14190651280770250958839003)
      ·
        refine ⟨21285976921155376438258505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14190651280770250958839003 21285976921155376438258505)
        ·
          refine ⟨15964482690866532328693879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21285976921155376438258505 15964482690866532328693879)
          ·
            refine ⟨23946724036299798493040819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15964482690866532328693879 23946724036299798493040819)
            ·
              refine ⟨35920086054449697739561229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23946724036299798493040819 35920086054449697739561229)
              ·
                refine ⟨13470032270418636652335461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35920086054449697739561229 13470032270418636652335461)
                ·
                  refine ⟨2525631050703494372312899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13470032270418636652335461 2525631050703494372312899)
                  ·
                    refine ⟨3788446576055241558469349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525631050703494372312899 3788446576055241558469349)
                    ·
                      refine ⟨710333733010357792213003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3788446576055241558469349 710333733010357792213003)
                      ·
                        rfl

theorem cell23_1383370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1383370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383370 prefixEnd_1383370 := by exact prefixLift 1383370
  have htrace : WordTrace (prefixWord ++ tailWord_1383370) baseStart_1383370 baseEnd_1383370 := by
    simpa [prefixWord, tailWord_1383370, baseEnd_1383370] using wordTrace_append hprefix tailTrace_1383370
  have hstable : (prefixWord ++ tailWord_1383370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383370).length < 2 ^ (prefixWord ++ tailWord_1383370).sum := by decide
  have hdescent : baseEnd_1383370 < baseStart_1383370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383403 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_1383403 : Nat := 118140960795 + 1383403 * 2 ^ 59
def prefixEnd_1383403 : Nat := 4983230072969 + 3 ^ 40 * 1383403 * 2
def baseEnd_1383403 : Nat := 710350677871956163100351

theorem tailTrace_1383403 : CollatzResearch.WordTrace tailWord_1383403 prefixEnd_1383403 710350677871956163100351 := by
  unfold tailWord_1383403
  simp only [CollatzResearch.WordTrace]
  refine ⟨50456852607174672267378863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33637901738116448178252575 50456852607174672267378863)
  ·
    refine ⟨75685278910762008401068295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50456852607174672267378863 75685278910762008401068295)
    ·
      refine ⟨113527918366143012601602443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75685278910762008401068295 113527918366143012601602443)
      ·
        refine ⟨170291877549214518902403665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113527918366143012601602443 170291877549214518902403665)
        ·
          refine ⟨127718908161910889176802749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170291877549214518902403665 127718908161910889176802749)
          ·
            refine ⟨47894590560716583441301031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127718908161910889176802749 47894590560716583441301031)
            ·
              refine ⟨71841885841074875161951547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47894590560716583441301031 71841885841074875161951547)
              ·
                refine ⟨107762828761612312742927321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71841885841074875161951547 107762828761612312742927321)
                ·
                  refine ⟨80822121571209234557195491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107762828761612312742927321 80822121571209234557195491)
                  ·
                    refine ⟨121233182356813851835793237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80822121571209234557195491 121233182356813851835793237)
                    ·
                      refine ⟨710350677871956163100351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 121233182356813851835793237 710350677871956163100351)
                      ·
                        rfl

theorem cell23_1383403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_1383403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383403 prefixEnd_1383403 := by exact prefixLift 1383403
  have htrace : WordTrace (prefixWord ++ tailWord_1383403) baseStart_1383403 baseEnd_1383403 := by
    simpa [prefixWord, tailWord_1383403, baseEnd_1383403] using wordTrace_append hprefix tailTrace_1383403
  have hstable : (prefixWord ++ tailWord_1383403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383403).length < 2 ^ (prefixWord ++ tailWord_1383403).sum := by decide
  have hdescent : baseEnd_1383403 < baseStart_1383403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383431 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 1, 4]
def baseStart_1383431 : Nat := 118140960795 + 1383431 * 2 ^ 59
def prefixEnd_1383431 : Nat := 4983230072969 + 3 ^ 40 * 1383431 * 2
def baseEnd_1383431 : Nat := 236788351776760684516741

theorem tailTrace_1383431 : CollatzResearch.WordTrace tailWord_1383431 prefixEnd_1383431 236788351776760684516741 := by
  unfold tailWord_1383431
  simp only [CollatzResearch.WordTrace]
  refine ⟨50457873851073233049398147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33638582567382155366265431 50457873851073233049398147)
  ·
    refine ⟨75686810776609849574097221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50457873851073233049398147 75686810776609849574097221)
    ·
      refine ⟨14191277020614346795143229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75686810776609849574097221 14191277020614346795143229)
      ·
        refine ⟨5321728882730380048178711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14191277020614346795143229 5321728882730380048178711)
        ·
          refine ⟨7982593324095570072268067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5321728882730380048178711 7982593324095570072268067)
          ·
            refine ⟨11973889986143355108402101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982593324095570072268067 11973889986143355108402101)
            ·
              refine ⟨1122552186200939541412697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11973889986143355108402101 1122552186200939541412697)
              ·
                refine ⟨841914139650704656059523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122552186200939541412697 841914139650704656059523)
                ·
                  refine ⟨1262871209476056984089285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841914139650704656059523 1262871209476056984089285)
                  ·
                    refine ⟨236788351776760684516741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262871209476056984089285 236788351776760684516741)
                    ·
                      rfl

theorem cell23_1383431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_1383431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383431 prefixEnd_1383431 := by exact prefixLift 1383431
  have htrace : WordTrace (prefixWord ++ tailWord_1383431) baseStart_1383431 baseEnd_1383431 := by
    simpa [prefixWord, tailWord_1383431, baseEnd_1383431] using wordTrace_append hprefix tailTrace_1383431
  have hstable : (prefixWord ++ tailWord_1383431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383431).length < 2 ^ (prefixWord ++ tailWord_1383431).sum := by decide
  have hdescent : baseEnd_1383431 < baseStart_1383431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383457 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1383457 : Nat := 118140960795 + 1383457 * 2 ^ 59
def prefixEnd_1383457 : Nat := 4983230072969 + 3 ^ 40 * 1383457 * 2
def baseEnd_1383457 : Nat := 236792801942432983941701

theorem tailTrace_1383457 : CollatzResearch.WordTrace tailWord_1383457 prefixEnd_1383457 236792801942432983941701 := by
  unfold tailWord_1383457
  simp only [CollatzResearch.WordTrace]
  refine ⟨50458822148979039489844625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33639214765986026326563083 50458822148979039489844625)
  ·
    refine ⟨37844116611734279617383469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50458822148979039489844625 37844116611734279617383469)
    ·
      refine ⟨14191543729400354856518801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37844116611734279617383469 14191543729400354856518801)
      ·
        refine ⟨10643657797050266142389101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14191543729400354856518801 10643657797050266142389101)
        ·
          refine ⟨3991371673893849803395913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10643657797050266142389101 3991371673893849803395913)
          ·
            refine ⟨2993528755420387352546935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3991371673893849803395913 2993528755420387352546935)
            ·
              refine ⟨4490293133130581028820403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993528755420387352546935 4490293133130581028820403)
              ·
                refine ⟨6735439699695871543230605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490293133130581028820403 6735439699695871543230605)
                ·
                  refine ⟨2525789887385951828711477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6735439699695871543230605 2525789887385951828711477)
                  ·
                    refine ⟨236792801942432983941701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2525789887385951828711477 236792801942432983941701)
                    ·
                      rfl

theorem cell23_1383457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1383457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383457 prefixEnd_1383457 := by exact prefixLift 1383457
  have htrace : WordTrace (prefixWord ++ tailWord_1383457) baseStart_1383457 baseEnd_1383457 := by
    simpa [prefixWord, tailWord_1383457, baseEnd_1383457] using wordTrace_append hprefix tailTrace_1383457
  have hstable : (prefixWord ++ tailWord_1383457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383457).length < 2 ^ (prefixWord ++ tailWord_1383457).sum := by decide
  have hdescent : baseEnd_1383457 < baseStart_1383457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383474 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_1383474 : Nat := 118140960795 + 1383474 * 2 ^ 59
def prefixEnd_1383474 : Nat := 4983230072969 + 3 ^ 40 * 1383474 * 2
def baseEnd_1383474 : Nat := 236795711666141795104175

theorem tailTrace_1383474 : CollatzResearch.WordTrace tailWord_1383474 prefixEnd_1383474 236795711666141795104175 := by
  unfold tailWord_1383474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614860547479362848303369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33639628126611634262142317 12614860547479362848303369)
  ·
    refine ⟨9461145410609522136227527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12614860547479362848303369 9461145410609522136227527)
    ·
      refine ⟨14191718115914283204341291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9461145410609522136227527 14191718115914283204341291)
      ·
        refine ⟨21287577173871424806511937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191718115914283204341291 21287577173871424806511937)
        ·
          refine ⟨15965682880403568604883953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21287577173871424806511937 15965682880403568604883953)
          ·
            refine ⟨11974262160302676453662965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15965682880403568604883953 11974262160302676453662965)
            ·
              refine ⟨1122587077528375917530903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11974262160302676453662965 1122587077528375917530903)
              ·
                refine ⟨1683880616292563876296355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122587077528375917530903 1683880616292563876296355)
                ·
                  refine ⟨2525820924438845814444533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683880616292563876296355 2525820924438845814444533)
                  ·
                    refine ⟨236795711666141795104175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2525820924438845814444533 236795711666141795104175)
                    ·
                      rfl

theorem cell23_1383474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_1383474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383474 prefixEnd_1383474 := by exact prefixLift 1383474
  have htrace : WordTrace (prefixWord ++ tailWord_1383474) baseStart_1383474 baseEnd_1383474 := by
    simpa [prefixWord, tailWord_1383474, baseEnd_1383474] using wordTrace_append hprefix tailTrace_1383474
  have hstable : (prefixWord ++ tailWord_1383474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383474).length < 2 ^ (prefixWord ++ tailWord_1383474).sum := by decide
  have hdescent : baseEnd_1383474 < baseStart_1383474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383584 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 3, 4, 2]
def baseStart_1383584 : Nat := 118140960795 + 1383584 * 2 ^ 59
def prefixEnd_1383584 : Nat := 4983230072969 + 3 ^ 40 * 1383584 * 2
def baseEnd_1383584 : Nat := 710443617870419954937019

theorem tailTrace_1383584 : CollatzResearch.WordTrace tailWord_1383584 prefixEnd_1383584 710443617870419954937019 := by
  unfold tailWord_1383584
  simp only [CollatzResearch.WordTrace]
  refine ⟨25231727109759470089858903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33642302813012626786478537 25231727109759470089858903)
  ·
    refine ⟨37847590664639205134788355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25231727109759470089858903 37847590664639205134788355)
    ·
      refine ⟨56771385996958807702182533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37847590664639205134788355 56771385996958807702182533)
      ·
        refine ⟨10644634874429776444159225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56771385996958807702182533 10644634874429776444159225)
        ·
          refine ⟨7983476155822332333119419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10644634874429776444159225 7983476155822332333119419)
          ·
            refine ⟨11975214233733498499679129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7983476155822332333119419 11975214233733498499679129)
            ·
              refine ⟨8981410675300123874759347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11975214233733498499679129 8981410675300123874759347)
              ·
                refine ⟨13472116012950185812139021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8981410675300123874759347 13472116012950185812139021)
                ·
                  refine ⟨5052043504856319679552133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13472116012950185812139021 5052043504856319679552133)
                  ·
                    refine ⟨947258157160559939916025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5052043504856319679552133 947258157160559939916025)
                    ·
                      refine ⟨710443617870419954937019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947258157160559939916025 710443617870419954937019)
                      ·
                        rfl

theorem cell23_1383584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_1383584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383584 prefixEnd_1383584 := by exact prefixLift 1383584
  have htrace : WordTrace (prefixWord ++ tailWord_1383584) baseStart_1383584 baseEnd_1383584 := by
    simpa [prefixWord, tailWord_1383584, baseEnd_1383584] using wordTrace_append hprefix tailTrace_1383584
  have hstable : (prefixWord ++ tailWord_1383584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383584).length < 2 ^ (prefixWord ++ tailWord_1383584).sum := by decide
  have hdescent : baseEnd_1383584 < baseStart_1383584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383622 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1383622 : Nat := 118140960795 + 1383622 * 2 ^ 59
def prefixEnd_1383622 : Nat := 4983230072969 + 3 ^ 40 * 1383622 * 2
def baseEnd_1383622 : Nat := 710463130135290806261845

theorem tailTrace_1383622 : CollatzResearch.WordTrace tailWord_1383622 prefixEnd_1383622 710463130135290806261845 := by
  unfold tailWord_1383622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577026256043164770925035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33643226795587515113067413 1577026256043164770925035)
  ·
    refine ⟨2365539384064747156387553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1577026256043164770925035 2365539384064747156387553)
    ·
      refine ⟨1774154538048560367290665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2365539384064747156387553 1774154538048560367290665)
      ·
        refine ⟨1330615903536420275467999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1774154538048560367290665 1330615903536420275467999)
        ·
          refine ⟨1995923855304630413201999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330615903536420275467999 1995923855304630413201999)
          ·
            refine ⟨2993885782956945619802999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995923855304630413201999 2993885782956945619802999)
            ·
              refine ⟨4490828674435418429704499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993885782956945619802999 4490828674435418429704499)
              ·
                refine ⟨6736243011653127644556749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490828674435418429704499 6736243011653127644556749)
                ·
                  refine ⟨2526091129369922866708781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6736243011653127644556749 2526091129369922866708781)
                  ·
                    refine ⟨947284173513721075015793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526091129369922866708781 947284173513721075015793)
                    ·
                      refine ⟨710463130135290806261845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947284173513721075015793 710463130135290806261845)
                      ·
                        rfl

theorem cell23_1383622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1383622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383622 prefixEnd_1383622 := by exact prefixLift 1383622
  have htrace : WordTrace (prefixWord ++ tailWord_1383622) baseStart_1383622 baseEnd_1383622 := by
    simpa [prefixWord, tailWord_1383622, baseEnd_1383622] using wordTrace_append hprefix tailTrace_1383622
  have hstable : (prefixWord ++ tailWord_1383622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383622).length < 2 ^ (prefixWord ++ tailWord_1383622).sum := by decide
  have hdescent : baseEnd_1383622 < baseStart_1383622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383647 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1383647 : Nat := 118140960795 + 1383647 * 2 ^ 59
def prefixEnd_1383647 : Nat := 4983230072969 + 3 ^ 40 * 1383647 * 2
def baseEnd_1383647 : Nat := 710475967151653208449229

theorem tailTrace_1383647 : CollatzResearch.WordTrace tailWord_1383647 prefixEnd_1383647 710475967151653208449229 := by
  unfold tailWord_1383647
  simp only [CollatzResearch.WordTrace]
  refine ⟨50465752018290701939261195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33643834678860467959507463 50465752018290701939261195)
  ·
    refine ⟨75698628027436052908891793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50465752018290701939261195 75698628027436052908891793)
    ·
      refine ⟨56773971020577039681668845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75698628027436052908891793 56773971020577039681668845)
      ·
        refine ⟨21290239132716389880625817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56773971020577039681668845 21290239132716389880625817)
        ·
          refine ⟨15967679349537292410469363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21290239132716389880625817 15967679349537292410469363)
          ·
            refine ⟨23951519024305938615704045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15967679349537292410469363 23951519024305938615704045)
            ·
              refine ⟨8981819634114726980889017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23951519024305938615704045 8981819634114726980889017)
              ·
                refine ⟨6736364725586045235666763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8981819634114726980889017 6736364725586045235666763)
                ·
                  refine ⟨10104547088379067853500145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736364725586045235666763 10104547088379067853500145)
                  ·
                    refine ⟨7578410316284300890125109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10104547088379067853500145 7578410316284300890125109)
                    ·
                      refine ⟨710475967151653208449229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7578410316284300890125109 710475967151653208449229)
                      ·
                        rfl

theorem cell23_1383647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1383647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383647 prefixEnd_1383647 := by exact prefixLift 1383647
  have htrace : WordTrace (prefixWord ++ tailWord_1383647) baseStart_1383647 baseEnd_1383647 := by
    simpa [prefixWord, tailWord_1383647, baseEnd_1383647] using wordTrace_append hprefix tailTrace_1383647
  have hstable : (prefixWord ++ tailWord_1383647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383647).length < 2 ^ (prefixWord ++ tailWord_1383647).sum := by decide
  have hdescent : baseEnd_1383647 < baseStart_1383647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383658 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_1383658 : Nat := 118140960795 + 1383658 * 2 ^ 59
def prefixEnd_1383658 : Nat := 4983230072969 + 3 ^ 40 * 1383658 * 2
def baseEnd_1383658 : Nat := 78942401715428073934631

theorem tailTrace_1383658 : CollatzResearch.WordTrace tailWord_1383658 prefixEnd_1383658 78942401715428073934631 := by
  unfold tailWord_1383658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616538305312712704477907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33644102147500567211941085 12616538305312712704477907)
  ·
    refine ⟨18924807457969069056716861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12616538305312712704477907 18924807457969069056716861)
    ·
      refine ⟨7096802796738400896268823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18924807457969069056716861 7096802796738400896268823)
      ·
        refine ⟨10645204195107601344403235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7096802796738400896268823 10645204195107601344403235)
        ·
          refine ⟨15967806292661402016604853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645204195107601344403235 15967806292661402016604853)
          ·
            refine ⟨1496981839937006439056705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15967806292661402016604853 1496981839937006439056705)
            ·
              refine ⟨1122736379952754829292529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496981839937006439056705 1122736379952754829292529)
              ·
                refine ⟨842052284964566121969397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122736379952754829292529 842052284964566121969397)
                ·
                  refine ⟨78942401715428073934631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 842052284964566121969397 78942401715428073934631)
                  ·
                    rfl

theorem cell23_1383658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_1383658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383658 prefixEnd_1383658 := by exact prefixLift 1383658
  have htrace : WordTrace (prefixWord ++ tailWord_1383658) baseStart_1383658 baseEnd_1383658 := by
    simpa [prefixWord, tailWord_1383658, baseEnd_1383658] using wordTrace_append hprefix tailTrace_1383658
  have hstable : (prefixWord ++ tailWord_1383658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383658).length < 2 ^ (prefixWord ++ tailWord_1383658).sum := by decide
  have hdescent : baseEnd_1383658 < baseStart_1383658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383661 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1383661 : Nat := 118140960795 + 1383661 * 2 ^ 59
def prefixEnd_1383661 : Nat := 4983230072969 + 3 ^ 40 * 1383661 * 2
def baseEnd_1383661 : Nat := 710483155880816153674165

theorem tailTrace_1383661 : CollatzResearch.WordTrace tailWord_1383661 prefixEnd_1383661 710483155880816153674165 := by
  unfold tailWord_1383661
  simp only [CollatzResearch.WordTrace]
  refine ⟨50466262640239982330270837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33644175093493321553513891 50466262640239982330270837)
  ·
    refine ⟨4731212122522498343462891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50466262640239982330270837 4731212122522498343462891)
    ·
      refine ⟨7096818183783747515194337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4731212122522498343462891 7096818183783747515194337)
      ·
        refine ⟨5322613637837810636395753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7096818183783747515194337 5322613637837810636395753)
        ·
          refine ⟨3991960228378357977296815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5322613637837810636395753 3991960228378357977296815)
          ·
            refine ⟨5987940342567536965945223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991960228378357977296815 5987940342567536965945223)
            ·
              refine ⟨8981910513851305448917835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5987940342567536965945223 8981910513851305448917835)
              ·
                refine ⟨13472865770776958173376753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8981910513851305448917835 13472865770776958173376753)
                ·
                  refine ⟨10104649328082718630032565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13472865770776958173376753 10104649328082718630032565)
                  ·
                    refine ⟨947310874507754871565553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10104649328082718630032565 947310874507754871565553)
                    ·
                      refine ⟨710483155880816153674165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947310874507754871565553 710483155880816153674165)
                      ·
                        rfl

theorem cell23_1383661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1383661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383661 prefixEnd_1383661 := by exact prefixLift 1383661
  have htrace : WordTrace (prefixWord ++ tailWord_1383661) baseStart_1383661 baseEnd_1383661 := by
    simpa [prefixWord, tailWord_1383661, baseEnd_1383661] using wordTrace_append hprefix tailTrace_1383661
  have hstable : (prefixWord ++ tailWord_1383661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383661).length < 2 ^ (prefixWord ++ tailWord_1383661).sum := by decide
  have hdescent : baseEnd_1383661 < baseStart_1383661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383688 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1383688 : Nat := 118140960795 + 1383688 * 2 ^ 59
def prefixEnd_1383688 : Nat := 4983230072969 + 3 ^ 40 * 1383688 * 2
def baseEnd_1383688 : Nat := 236832339952829182678847

theorem tailTrace_1383688 : CollatzResearch.WordTrace tailWord_1383688 prefixEnd_1383688 236832339952829182678847 := by
  unfold tailWord_1383688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25233623705571082970751859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33644831607428110627669145 25233623705571082970751859)
  ·
    refine ⟨37850435558356624456127789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25233623705571082970751859 37850435558356624456127789)
    ·
      refine ⟨14193913334383734171047921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37850435558356624456127789 14193913334383734171047921)
      ·
        refine ⟨10645435000787800628285941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14193913334383734171047921 10645435000787800628285941)
        ·
          refine ⟨998009531323856308901807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10645435000787800628285941 998009531323856308901807)
          ·
            refine ⟨1497014296985784463352711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998009531323856308901807 1497014296985784463352711)
            ·
              refine ⟨2245521445478676695029067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497014296985784463352711 2245521445478676695029067)
              ·
                refine ⟨3368282168218015042543601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245521445478676695029067 3368282168218015042543601)
                ·
                  refine ⟨2526211626163511281907701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368282168218015042543601 2526211626163511281907701)
                  ·
                    refine ⟨236832339952829182678847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2526211626163511281907701 236832339952829182678847)
                    ·
                      rfl

theorem cell23_1383688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1383688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383688 prefixEnd_1383688 := by exact prefixLift 1383688
  have htrace : WordTrace (prefixWord ++ tailWord_1383688) baseStart_1383688 baseEnd_1383688 := by
    simpa [prefixWord, tailWord_1383688, baseEnd_1383688] using wordTrace_append hprefix tailTrace_1383688
  have hstable : (prefixWord ++ tailWord_1383688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383688).length < 2 ^ (prefixWord ++ tailWord_1383688).sum := by decide
  have hdescent : baseEnd_1383688 < baseStart_1383688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383691 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 4]
def baseStart_1383691 : Nat := 118140960795 + 1383691 * 2 ^ 59
def prefixEnd_1383691 : Nat := 4983230072969 + 3 ^ 40 * 1383691 * 2
def baseEnd_1383691 : Nat := 710498560300451036299027

theorem tailTrace_1383691 : CollatzResearch.WordTrace tailWord_1383691 prefixEnd_1383691 710498560300451036299027 := by
  unfold tailWord_1383691
  simp only [CollatzResearch.WordTrace]
  refine ⟨50467356830131297453862927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33644904553420864969241951 50467356830131297453862927)
  ·
    refine ⟨75701035245196946180794391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50467356830131297453862927 75701035245196946180794391)
    ·
      refine ⟨113551552867795419271191587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75701035245196946180794391 113551552867795419271191587)
      ·
        refine ⟨170327329301693128906787381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113551552867795419271191587 170327329301693128906787381)
        ·
          refine ⟨15968187122033730835011317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170327329301693128906787381 15968187122033730835011317)
          ·
            refine ⟨1497017542690662265782311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15968187122033730835011317 1497017542690662265782311)
            ·
              refine ⟨2245526314035993398673467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497017542690662265782311 2245526314035993398673467)
              ·
                refine ⟨3368289471053990098010201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245526314035993398673467 3368289471053990098010201)
                ·
                  refine ⟨2526217103290492573507651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368289471053990098010201 2526217103290492573507651)
                  ·
                    refine ⟨3789325654935738860261477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526217103290492573507651 3789325654935738860261477)
                    ·
                      refine ⟨710498560300451036299027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3789325654935738860261477 710498560300451036299027)
                      ·
                        rfl

theorem cell23_1383691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 4].length) (baseStart_1383691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383691 prefixEnd_1383691 := by exact prefixLift 1383691
  have htrace : WordTrace (prefixWord ++ tailWord_1383691) baseStart_1383691 baseEnd_1383691 := by
    simpa [prefixWord, tailWord_1383691, baseEnd_1383691] using wordTrace_append hprefix tailTrace_1383691
  have hstable : (prefixWord ++ tailWord_1383691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383691).length < 2 ^ (prefixWord ++ tailWord_1383691).sum := by decide
  have hdescent : baseEnd_1383691 < baseStart_1383691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383697 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 8]
def baseStart_1383697 : Nat := 118140960795 + 1383697 * 2 ^ 59
def prefixEnd_1383697 : Nat := 4983230072969 + 3 ^ 40 * 1383697 * 2
def baseEnd_1383697 : Nat := 78944626798264223647111

theorem tailTrace_1383697 : CollatzResearch.WordTrace tailWord_1383697 prefixEnd_1383697 78944626798264223647111 := by
  unfold tailWord_1383697
  simp only [CollatzResearch.WordTrace]
  refine ⟨50467575668109560478581345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33645050445406373652387563 50467575668109560478581345)
  ·
    refine ⟨37850681751082170358936009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50467575668109560478581345 37850681751082170358936009)
    ·
      refine ⟨28388011313311627769202007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37850681751082170358936009 28388011313311627769202007)
      ·
        refine ⟨42582016969967441653803011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28388011313311627769202007 42582016969967441653803011)
        ·
          refine ⟨63873025454951162480704517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42582016969967441653803011 63873025454951162480704517)
          ·
            refine ⟨11976192272803342965132097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63873025454951162480704517 11976192272803342965132097)
            ·
              refine ⟨8982144204602507223849073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11976192272803342965132097 8982144204602507223849073)
              ·
                refine ⟨6736608153451880417886805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8982144204602507223849073 6736608153451880417886805)
                ·
                  refine ⟨78944626798264223647111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6736608153451880417886805 78944626798264223647111)
                  ·
                    rfl

theorem cell23_1383697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_1383697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383697 prefixEnd_1383697 := by exact prefixLift 1383697
  have htrace : WordTrace (prefixWord ++ tailWord_1383697) baseStart_1383697 baseEnd_1383697 := by
    simpa [prefixWord, tailWord_1383697, baseEnd_1383697] using wordTrace_append hprefix tailTrace_1383697
  have hstable : (prefixWord ++ tailWord_1383697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383697).length < 2 ^ (prefixWord ++ tailWord_1383697).sum := by decide
  have hdescent : baseEnd_1383697 < baseStart_1383697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383731 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 6]
def baseStart_1383731 : Nat := 118140960795 + 1383731 * 2 ^ 59
def prefixEnd_1383731 : Nat := 4983230072969 + 3 ^ 40 * 1383731 * 2
def baseEnd_1383731 : Nat := 78946566614070097755427

theorem tailTrace_1383731 : CollatzResearch.WordTrace tailWord_1383731 prefixEnd_1383731 78946566614070097755427 := by
  unfold tailWord_1383731
  simp only [CollatzResearch.WordTrace]
  refine ⟨50468815749986384285319047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33645877166657589523546031 50468815749986384285319047)
  ·
    refine ⟨75703223624979576427978571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50468815749986384285319047 75703223624979576427978571)
    ·
      refine ⟨113554835437469364641967857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75703223624979576427978571 113554835437469364641967857)
      ·
        refine ⟨85166126578102023481475893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113554835437469364641967857 85166126578102023481475893)
        ·
          refine ⟨7984324366697064701388365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85166126578102023481475893 7984324366697064701388365)
          ·
            refine ⟨2994121637511399263020637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7984324366697064701388365 2994121637511399263020637)
            ·
              refine ⟨1122795614066774723632739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2994121637511399263020637 1122795614066774723632739)
              ·
                refine ⟨1684193421100162085449109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122795614066774723632739 1684193421100162085449109)
                ·
                  refine ⟨78946566614070097755427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1684193421100162085449109 78946566614070097755427)
                  ·
                    rfl

theorem cell23_1383731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 6].length) (baseStart_1383731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383731 prefixEnd_1383731 := by exact prefixLift 1383731
  have htrace : WordTrace (prefixWord ++ tailWord_1383731) baseStart_1383731 baseEnd_1383731 := by
    simpa [prefixWord, tailWord_1383731, baseEnd_1383731] using wordTrace_append hprefix tailTrace_1383731
  have hstable : (prefixWord ++ tailWord_1383731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383731).length < 2 ^ (prefixWord ++ tailWord_1383731).sum := by decide
  have hdescent : baseEnd_1383731 < baseStart_1383731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383751 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_1383751 : Nat := 118140960795 + 1383751 * 2 ^ 59
def prefixEnd_1383751 : Nat := 4983230072969 + 3 ^ 40 * 1383751 * 2
def baseEnd_1383751 : Nat := 710529369139720801548751

theorem tailTrace_1383751 : CollatzResearch.WordTrace tailWord_1383751 prefixEnd_1383751 710529369139720801548751 := by
  unfold tailWord_1383751
  simp only [CollatzResearch.WordTrace]
  refine ⟨50469545209913927701047107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33646363473275951800698071 50469545209913927701047107)
  ·
    refine ⟨75704317814870891551570661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50469545209913927701047107 75704317814870891551570661)
    ·
      refine ⟨14194559590288292165919499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75704317814870891551570661 14194559590288292165919499)
      ·
        refine ⟨21291839385432438248879249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14194559590288292165919499 21291839385432438248879249)
        ·
          refine ⟨15968879539074328686659437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21291839385432438248879249 15968879539074328686659437)
          ·
            refine ⟨5988329827152873257497289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15968879539074328686659437 5988329827152873257497289)
            ·
              refine ⟨4491247370364654943122967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5988329827152873257497289 4491247370364654943122967)
              ·
                refine ⟨6736871055546982414684451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491247370364654943122967 6736871055546982414684451)
                ·
                  refine ⟨10105306583320473622026677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6736871055546982414684451 10105306583320473622026677)
                  ·
                    refine ⟨947372492186294402065001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10105306583320473622026677 947372492186294402065001)
                    ·
                      refine ⟨710529369139720801548751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947372492186294402065001 710529369139720801548751)
                      ·
                        rfl

theorem cell23_1383751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_1383751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383751 prefixEnd_1383751 := by exact prefixLift 1383751
  have htrace : WordTrace (prefixWord ++ tailWord_1383751) baseStart_1383751 baseEnd_1383751 := by
    simpa [prefixWord, tailWord_1383751, baseEnd_1383751] using wordTrace_append hprefix tailTrace_1383751
  have hstable : (prefixWord ++ tailWord_1383751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383751).length < 2 ^ (prefixWord ++ tailWord_1383751).sum := by decide
  have hdescent : baseEnd_1383751 < baseStart_1383751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383791 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 2, 4]
def baseStart_1383791 : Nat := 118140960795 + 1383791 * 2 ^ 59
def prefixEnd_1383791 : Nat := 4983230072969 + 3 ^ 40 * 1383791 * 2
def baseEnd_1383791 : Nat := 236849969455300215016189

theorem tailTrace_1383791 : CollatzResearch.WordTrace tailWord_1383791 prefixEnd_1383791 236849969455300215016189 := by
  unfold tailWord_1383791
  simp only [CollatzResearch.WordTrace]
  refine ⟨50471004129769014532503227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33647336086512676355002151 50471004129769014532503227)
  ·
    refine ⟨75706506194653521798754841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50471004129769014532503227 75706506194653521798754841)
    ·
      refine ⟨56779879645990141349066131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75706506194653521798754841 56779879645990141349066131)
      ·
        refine ⟨85169819468985212023599197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56779879645990141349066131 85169819468985212023599197)
        ·
          refine ⟨31938682300869454508849699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85169819468985212023599197 31938682300869454508849699)
          ·
            refine ⟨47908023451304181763274549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31938682300869454508849699 47908023451304181763274549)
            ·
              refine ⟨4491377198559767040306989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47908023451304181763274549 4491377198559767040306989)
              ·
                refine ⟨1684266449459912640115121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4491377198559767040306989 1684266449459912640115121)
                ·
                  refine ⟨1263199837094934480086341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1684266449459912640115121 1263199837094934480086341)
                  ·
                    refine ⟨236849969455300215016189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263199837094934480086341 236849969455300215016189)
                    ·
                      rfl

theorem cell23_1383791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_1383791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383791 prefixEnd_1383791 := by exact prefixLift 1383791
  have htrace : WordTrace (prefixWord ++ tailWord_1383791) baseStart_1383791 baseEnd_1383791 := by
    simpa [prefixWord, tailWord_1383791, baseEnd_1383791] using wordTrace_append hprefix tailTrace_1383791
  have hstable : (prefixWord ++ tailWord_1383791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383791).length < 2 ^ (prefixWord ++ tailWord_1383791).sum := by decide
  have hdescent : baseEnd_1383791 < baseStart_1383791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383794 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1383794 : Nat := 118140960795 + 1383794 * 2 ^ 59
def prefixEnd_1383794 : Nat := 4983230072969 + 3 ^ 40 * 1383794 * 2
def baseEnd_1383794 : Nat := 710551448807864133311053

theorem tailTrace_1383794 : CollatzResearch.WordTrace tailWord_1383794 prefixEnd_1383794 710551448807864133311053 := by
  unfold tailWord_1383794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12617778387189536511215609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33647409032505430696574957 12617778387189536511215609)
  ·
    refine ⟨9463333790392152383411707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12617778387189536511215609 9463333790392152383411707)
    ·
      refine ⟨14195000685588228575117561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9463333790392152383411707 14195000685588228575117561)
      ·
        refine ⟨10646250514191171431338171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14195000685588228575117561 10646250514191171431338171)
        ·
          refine ⟨15969375771286757147007257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10646250514191171431338171 15969375771286757147007257)
          ·
            refine ⟨11977031828465067860255443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15969375771286757147007257 11977031828465067860255443)
            ·
              refine ⟨17965547742697601790383165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11977031828465067860255443 17965547742697601790383165)
              ·
                refine ⟨6737080403511600671393687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17965547742697601790383165 6737080403511600671393687)
                ·
                  refine ⟨10105620605267401007090531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6737080403511600671393687 10105620605267401007090531)
                  ·
                    refine ⟨15158430907901101510635797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10105620605267401007090531 15158430907901101510635797)
                    ·
                      refine ⟨710551448807864133311053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15158430907901101510635797 710551448807864133311053)
                      ·
                        rfl

theorem cell23_1383794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1383794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383794 prefixEnd_1383794 := by exact prefixLift 1383794
  have htrace : WordTrace (prefixWord ++ tailWord_1383794) baseStart_1383794 baseEnd_1383794 := by
    simpa [prefixWord, tailWord_1383794, baseEnd_1383794] using wordTrace_append hprefix tailTrace_1383794
  have hstable : (prefixWord ++ tailWord_1383794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383794).length < 2 ^ (prefixWord ++ tailWord_1383794).sum := by decide
  have hdescent : baseEnd_1383794 < baseStart_1383794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383811 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4]
def baseStart_1383811 : Nat := 118140960795 + 1383811 * 2 ^ 59
def prefixEnd_1383811 : Nat := 4983230072969 + 3 ^ 40 * 1383811 * 2
def baseEnd_1383811 : Nat := 710560177978990566798475

theorem tailTrace_1383811 : CollatzResearch.WordTrace tailWord_1383811 prefixEnd_1383811 710560177978990566798475 := by
  unfold tailWord_1383811
  simp only [CollatzResearch.WordTrace]
  refine ⟨50471733589696557948231287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33647822393131038632154191 50471733589696557948231287)
  ·
    refine ⟨75707600384544836922346931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50471733589696557948231287 75707600384544836922346931)
    ·
      refine ⟨113561400576817255383520397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75707600384544836922346931 113561400576817255383520397)
      ·
        refine ⟨42585525216306470768820149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113561400576817255383520397 42585525216306470768820149)
        ·
          refine ⟨3992392989028731634576889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42585525216306470768820149 3992392989028731634576889)
          ·
            refine ⟨2994294741771548725932667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3992392989028731634576889 2994294741771548725932667)
            ·
              refine ⟨4491442112657323088899001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994294741771548725932667 4491442112657323088899001)
              ·
                refine ⟨3368581584492992316674251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4491442112657323088899001 3368581584492992316674251)
                ·
                  refine ⟨5052872376739488475011377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368581584492992316674251 5052872376739488475011377)
                  ·
                    refine ⟨3789654282554616356258533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5052872376739488475011377 3789654282554616356258533)
                    ·
                      refine ⟨710560177978990566798475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3789654282554616356258533 710560177978990566798475)
                      ·
                        rfl

theorem cell23_1383811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_1383811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383811 prefixEnd_1383811 := by exact prefixLift 1383811
  have htrace : WordTrace (prefixWord ++ tailWord_1383811) baseStart_1383811 baseEnd_1383811 := by
    simpa [prefixWord, tailWord_1383811, baseEnd_1383811] using wordTrace_append hprefix tailTrace_1383811
  have hstable : (prefixWord ++ tailWord_1383811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383811).length < 2 ^ (prefixWord ++ tailWord_1383811).sum := by decide
  have hdescent : baseEnd_1383811 < baseStart_1383811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383826 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1383826 : Nat := 118140960795 + 1383826 * 2 ^ 59
def prefixEnd_1383826 : Nat := 4983230072969 + 3 ^ 40 * 1383826 * 2
def baseEnd_1383826 : Nat := 710567880188808008110907

theorem tailTrace_1383826 : CollatzResearch.WordTrace tailWord_1383826 prefixEnd_1383826 710567880188808008110907 := by
  unfold tailWord_1383826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618070171160553877506833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33648187123094810340018221 12618070171160553877506833)
  ·
    refine ⟨9463552628370415408130125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12618070171160553877506833 9463552628370415408130125)
    ·
      refine ⟨3548832235638905778048797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9463552628370415408130125 3548832235638905778048797)
      ·
        refine ⟨1330812088364589666768299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3548832235638905778048797 1330812088364589666768299)
        ·
          refine ⟨1996218132546884500152449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330812088364589666768299 1996218132546884500152449)
          ·
            refine ⟨1497163599410163375114337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996218132546884500152449 1497163599410163375114337)
            ·
              refine ⟨1122872699557622531335753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497163599410163375114337 1122872699557622531335753)
              ·
                refine ⟨842154524668216898501815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122872699557622531335753 842154524668216898501815)
                ·
                  refine ⟨1263231787002325347752723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842154524668216898501815 1263231787002325347752723)
                  ·
                    refine ⟨1894847680503488021629085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1263231787002325347752723 1894847680503488021629085)
                    ·
                      refine ⟨710567880188808008110907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1894847680503488021629085 710567880188808008110907)
                      ·
                        rfl

theorem cell23_1383826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1383826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383826 prefixEnd_1383826 := by exact prefixLift 1383826
  have htrace : WordTrace (prefixWord ++ tailWord_1383826) baseStart_1383826 baseEnd_1383826 := by
    simpa [prefixWord, tailWord_1383826, baseEnd_1383826] using wordTrace_append hprefix tailTrace_1383826
  have hstable : (prefixWord ++ tailWord_1383826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383826).length < 2 ^ (prefixWord ++ tailWord_1383826).sum := by decide
  have hdescent : baseEnd_1383826 < baseStart_1383826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383834 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_1383834 : Nat := 118140960795 + 1383834 * 2 ^ 59
def prefixEnd_1383834 : Nat := 4983230072969 + 3 ^ 40 * 1383834 * 2
def baseEnd_1383834 : Nat := 236857329344681325603623

theorem tailTrace_1383834 : CollatzResearch.WordTrace tailWord_1383834 prefixEnd_1383834 236857329344681325603623 := by
  unfold tailWord_1383834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618143117153308219079639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33648381645742155250879037 12618143117153308219079639)
  ·
    refine ⟨18927214675729962328619459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12618143117153308219079639 18927214675729962328619459)
    ·
      refine ⟨28390822013594943492929189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18927214675729962328619459 28390822013594943492929189)
      ·
        refine ⟨5323279127549051904924223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28390822013594943492929189 5323279127549051904924223)
        ·
          refine ⟨7984918691323577857386335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323279127549051904924223 7984918691323577857386335)
          ·
            refine ⟨11977378036985366786079503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7984918691323577857386335 11977378036985366786079503)
            ·
              refine ⟨17966067055478050179119255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11977378036985366786079503 17966067055478050179119255)
              ·
                refine ⟨26949100583217075268678883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17966067055478050179119255 26949100583217075268678883)
                ·
                  refine ⟨40423650874825612903018325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26949100583217075268678883 40423650874825612903018325)
                  ·
                    refine ⟨236857329344681325603623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 40423650874825612903018325 236857329344681325603623)
                    ·
                      rfl

theorem cell23_1383834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_1383834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383834 prefixEnd_1383834 := by exact prefixLift 1383834
  have htrace : WordTrace (prefixWord ++ tailWord_1383834) baseStart_1383834 baseEnd_1383834 := by
    simpa [prefixWord, tailWord_1383834, baseEnd_1383834] using wordTrace_append hprefix tailTrace_1383834
  have hstable : (prefixWord ++ tailWord_1383834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383834).length < 2 ^ (prefixWord ++ tailWord_1383834).sum := by decide
  have hdescent : baseEnd_1383834 < baseStart_1383834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383844 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1383844 : Nat := 118140960795 + 1383844 * 2 ^ 59
def prefixEnd_1383844 : Nat := 4983230072969 + 3 ^ 40 * 1383844 * 2
def baseEnd_1383844 : Nat := 710577122840588937685823

theorem tailTrace_1383844 : CollatzResearch.WordTrace tailWord_1383844 prefixEnd_1383844 710577122840588937685823 := by
  unfold tailWord_1383844
  simp only [CollatzResearch.WordTrace]
  refine ⟨25236468599288502292091293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33648624799051336389455057 25236468599288502292091293)
  ·
    refine ⟨9463675724733188359534235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25236468599288502292091293 9463675724733188359534235)
    ·
      refine ⟨14195513587099782539301353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9463675724733188359534235 14195513587099782539301353)
      ·
        refine ⟨10646635190324836904476015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14195513587099782539301353 10646635190324836904476015)
        ·
          refine ⟨15969952785487255356714023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10646635190324836904476015 15969952785487255356714023)
          ·
            refine ⟨23954929178230883035071035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15969952785487255356714023 23954929178230883035071035)
            ·
              refine ⟨35932393767346324552606553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23954929178230883035071035 35932393767346324552606553)
              ·
                refine ⟨26949295325509743414454915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35932393767346324552606553 26949295325509743414454915)
                ·
                  refine ⟨40423942988264615121682373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26949295325509743414454915 40423942988264615121682373)
                  ·
                    refine ⟨7579489310299615335315445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40423942988264615121682373 7579489310299615335315445)
                    ·
                      refine ⟨710577122840588937685823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7579489310299615335315445 710577122840588937685823)
                      ·
                        rfl

theorem cell23_1383844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1383844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383844 prefixEnd_1383844 := by exact prefixLift 1383844
  have htrace : WordTrace (prefixWord ++ tailWord_1383844) baseStart_1383844 baseEnd_1383844 := by
    simpa [prefixWord, tailWord_1383844, baseEnd_1383844] using wordTrace_append hprefix tailTrace_1383844
  have hstable : (prefixWord ++ tailWord_1383844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383844).length < 2 ^ (prefixWord ++ tailWord_1383844).sum := by decide
  have hdescent : baseEnd_1383844 < baseStart_1383844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383875 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 1, 3, 2]
def baseStart_1383875 : Nat := 118140960795 + 1383875 * 2 ^ 59
def prefixEnd_1383875 : Nat := 4983230072969 + 3 ^ 40 * 1383875 * 2
def baseEnd_1383875 : Nat := 710593040740878316398181

theorem tailTrace_1383875 : CollatzResearch.WordTrace tailWord_1383875 prefixEnd_1383875 710593040740878316398181 := by
  unfold tailWord_1383875
  simp only [CollatzResearch.WordTrace]
  refine ⟨50474067861464696878561079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33649378574309797919040719 50474067861464696878561079)
  ·
    refine ⟨75711101792197045317841619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50474067861464696878561079 75711101792197045317841619)
    ·
      refine ⟨113566652688295567976762429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75711101792197045317841619 113566652688295567976762429)
      ·
        refine ⟨42587494758110837991285911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113566652688295567976762429 42587494758110837991285911)
        ·
          refine ⟨63881242137166256986928867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42587494758110837991285911 63881242137166256986928867)
          ·
            refine ⟨95821863205749385480393301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63881242137166256986928867 95821863205749385480393301)
            ·
              refine ⟨1122912459442375611098359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 95821863205749385480393301 1122912459442375611098359)
              ·
                refine ⟨1684368689163563416647539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122912459442375611098359 1684368689163563416647539)
                ·
                  refine ⟨2526553033745345124971309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684368689163563416647539 2526553033745345124971309)
                  ·
                    refine ⟨947457387654504421864241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526553033745345124971309 947457387654504421864241)
                    ·
                      refine ⟨710593040740878316398181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947457387654504421864241 710593040740878316398181)
                      ·
                        rfl

theorem cell23_1383875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_1383875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383875 prefixEnd_1383875 := by exact prefixLift 1383875
  have htrace : WordTrace (prefixWord ++ tailWord_1383875) baseStart_1383875 baseEnd_1383875 := by
    simpa [prefixWord, tailWord_1383875, baseEnd_1383875] using wordTrace_append hprefix tailTrace_1383875
  have hstable : (prefixWord ++ tailWord_1383875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383875).length < 2 ^ (prefixWord ++ tailWord_1383875).sum := by decide
  have hdescent : baseEnd_1383875 < baseStart_1383875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383888 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 4, 2, 2]
def baseStart_1383888 : Nat := 118140960795 + 1383888 * 2 ^ 59
def prefixEnd_1383888 : Nat := 4983230072969 + 3 ^ 40 * 1383888 * 2
def baseEnd_1383888 : Nat := 710599715989386765535621

theorem tailTrace_1383888 : CollatzResearch.WordTrace tailWord_1383888 prefixEnd_1383888 710599715989386765535621 := by
  unfold tailWord_1383888
  simp only [CollatzResearch.WordTrace]
  refine ⟨25237271005208800049392159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33649694673611733399189545 25237271005208800049392159)
  ·
    refine ⟨37855906507813200074088239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25237271005208800049392159 37855906507813200074088239)
    ·
      refine ⟨56783859761719800111132359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37855906507813200074088239 56783859761719800111132359)
      ·
        refine ⟨85175789642579700166698539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56783859761719800111132359 85175789642579700166698539)
        ·
          refine ⟨127763684463869550250047809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85175789642579700166698539 127763684463869550250047809)
          ·
            refine ⟨95822763347902162687535857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127763684463869550250047809 95822763347902162687535857)
            ·
              refine ⟨71867072510926622015651893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95822763347902162687535857 71867072510926622015651893)
              ·
                refine ⟨6737538047899370813967365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71867072510926622015651893 6737538047899370813967365)
                ·
                  refine ⟨1263288383981132027618881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6737538047899370813967365 1263288383981132027618881)
                  ·
                    refine ⟨947466287985849020714161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1263288383981132027618881 947466287985849020714161)
                    ·
                      refine ⟨710599715989386765535621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947466287985849020714161 710599715989386765535621)
                      ·
                        rfl

theorem cell23_1383888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 2, 2].length) (baseStart_1383888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383888 prefixEnd_1383888 := by exact prefixLift 1383888
  have htrace : WordTrace (prefixWord ++ tailWord_1383888) baseStart_1383888 baseEnd_1383888 := by
    simpa [prefixWord, tailWord_1383888, baseEnd_1383888] using wordTrace_append hprefix tailTrace_1383888
  have hstable : (prefixWord ++ tailWord_1383888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383888).length < 2 ^ (prefixWord ++ tailWord_1383888).sum := by decide
  have hdescent : baseEnd_1383888 < baseStart_1383888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383905 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_1383905 : Nat := 118140960795 + 1383905 * 2 ^ 59
def prefixEnd_1383905 : Nat := 4983230072969 + 3 ^ 40 * 1383905 * 2
def baseEnd_1383905 : Nat := 710608445160513199023043

theorem tailTrace_1383905 : CollatzResearch.WordTrace tailWord_1383905 prefixEnd_1383905 710608445160513199023043 := by
  unfold tailWord_1383905
  simp only [CollatzResearch.WordTrace]
  refine ⟨50475162051356012002153169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33650108034237341334768779 50475162051356012002153169)
  ·
    refine ⟨37856371538517009001614877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50475162051356012002153169 37856371538517009001614877)
    ·
      refine ⟨14196139326943878375605579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37856371538517009001614877 14196139326943878375605579)
      ·
        refine ⟨21294208990415817563408369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14196139326943878375605579 21294208990415817563408369)
        ·
          refine ⟨15970656742811863172556277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21294208990415817563408369 15970656742811863172556277)
          ·
            refine ⟨1497249069638612172427151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15970656742811863172556277 1497249069638612172427151)
            ·
              refine ⟨2245873604457918258640727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497249069638612172427151 2245873604457918258640727)
              ·
                refine ⟨3368810406686877387961091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245873604457918258640727 3368810406686877387961091)
                ·
                  refine ⟨5053215610030316081941637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368810406686877387961091 5053215610030316081941637)
                  ·
                    refine ⟨947477926880684265364057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5053215610030316081941637 947477926880684265364057)
                    ·
                      refine ⟨710608445160513199023043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947477926880684265364057 710608445160513199023043)
                      ·
                        rfl

theorem cell23_1383905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_1383905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383905 prefixEnd_1383905 := by exact prefixLift 1383905
  have htrace : WordTrace (prefixWord ++ tailWord_1383905) baseStart_1383905 baseEnd_1383905 := by
    simpa [prefixWord, tailWord_1383905, baseEnd_1383905] using wordTrace_append hprefix tailTrace_1383905
  have hstable : (prefixWord ++ tailWord_1383905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383905).length < 2 ^ (prefixWord ++ tailWord_1383905).sum := by decide
  have hdescent : baseEnd_1383905 < baseStart_1383905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383911 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 7]
def baseStart_1383911 : Nat := 118140960795 + 1383911 * 2 ^ 59
def prefixEnd_1383911 : Nat := 4983230072969 + 3 ^ 40 * 1383911 * 2
def baseEnd_1383911 : Nat := 78956836227160019505335

theorem tailTrace_1383911 : CollatzResearch.WordTrace tailWord_1383911 prefixEnd_1383911 78956836227160019505335 := by
  unfold tailWord_1383911
  simp only [CollatzResearch.WordTrace]
  refine ⟨50475380889334275026871587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33650253926222850017914391 50475380889334275026871587)
  ·
    refine ⟨75713071334001412540307381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50475380889334275026871587 75713071334001412540307381)
    ·
      refine ⟨7098100437562632425653817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75713071334001412540307381 7098100437562632425653817)
      ·
        refine ⟨5323575328171974319240363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7098100437562632425653817 5323575328171974319240363)
        ·
          refine ⟨7985362992257961478860545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323575328171974319240363 7985362992257961478860545)
          ·
            refine ⟨5989022244193471109145409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7985362992257961478860545 5989022244193471109145409)
            ·
              refine ⟨4491766683145103331859057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5989022244193471109145409 4491766683145103331859057)
              ·
                refine ⟨3368825012358827498894293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4491766683145103331859057 3368825012358827498894293)
                ·
                  refine ⟨78956836227160019505335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3368825012358827498894293 78956836227160019505335)
                  ·
                    rfl

theorem cell23_1383911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 7].length) (baseStart_1383911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383911 prefixEnd_1383911 := by exact prefixLift 1383911
  have htrace : WordTrace (prefixWord ++ tailWord_1383911) baseStart_1383911 baseEnd_1383911 := by
    simpa [prefixWord, tailWord_1383911, baseEnd_1383911] using wordTrace_append hprefix tailTrace_1383911
  have hstable : (prefixWord ++ tailWord_1383911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383911).length < 2 ^ (prefixWord ++ tailWord_1383911).sum := by decide
  have hdescent : baseEnd_1383911 < baseStart_1383911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1383928 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 5]
def baseStart_1383928 : Nat := 118140960795 + 1383928 * 2 ^ 59
def prefixEnd_1383928 : Nat := 4983230072969 + 3 ^ 40 * 1383928 * 2
def baseEnd_1383928 : Nat := 78957806135062956559493

theorem tailTrace_1383928 : CollatzResearch.WordTrace tailWord_1383928 prefixEnd_1383928 78957806135062956559493 := by
  unfold tailWord_1383928
  simp only [CollatzResearch.WordTrace]
  refine ⟨25238000465136343465120219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33650667286848457953493625 25238000465136343465120219)
  ·
    refine ⟨37857000697704515197680329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25238000465136343465120219 37857000697704515197680329)
    ·
      refine ⟨28392750523278386398260247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37857000697704515197680329 28392750523278386398260247)
      ·
        refine ⟨42589125784917579597390371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28392750523278386398260247 42589125784917579597390371)
        ·
          refine ⟨63883688677376369396085557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42589125784917579597390371 63883688677376369396085557)
          ·
            refine ⟨5989095813504034630883021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63883688677376369396085557 5989095813504034630883021)
            ·
              refine ⟨2245910930064012986581133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5989095813504034630883021 2245910930064012986581133)
              ·
                refine ⟨842216598774004869967925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2245910930064012986581133 842216598774004869967925)
                ·
                  refine ⟨78957806135062956559493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 842216598774004869967925 78957806135062956559493)
                  ·
                    rfl

theorem cell23_1383928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 5].length) (baseStart_1383928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1383928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1383928 prefixEnd_1383928 := by exact prefixLift 1383928
  have htrace : WordTrace (prefixWord ++ tailWord_1383928) baseStart_1383928 baseEnd_1383928 := by
    simpa [prefixWord, tailWord_1383928, baseEnd_1383928] using wordTrace_append hprefix tailTrace_1383928
  have hstable : (prefixWord ++ tailWord_1383928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1383928).length < 2 ^ (prefixWord ++ tailWord_1383928).sum := by decide
  have hdescent : baseEnd_1383928 < baseStart_1383928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1383928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384005 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_1384005 : Nat := 118140960795 + 1384005 * 2 ^ 59
def prefixEnd_1384005 : Nat := 4983230072969 + 3 ^ 40 * 1384005 * 2
def baseEnd_1384005 : Nat := 236886597741987602590861

theorem tailTrace_1384005 : CollatzResearch.WordTrace tailWord_1384005 prefixEnd_1384005 236886597741987602590861 := by
  unfold tailWord_1384005
  simp only [CollatzResearch.WordTrace]
  refine ⟨50478809350993729080793469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33652539567329152720528979 50478809350993729080793469)
  ·
    refine ⟨18929553506622648405297551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50478809350993729080793469 18929553506622648405297551)
    ·
      refine ⟨28394330259933972607946327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18929553506622648405297551 28394330259933972607946327)
      ·
        refine ⟨42591495389900958911919491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28394330259933972607946327 42591495389900958911919491)
        ·
          refine ⟨63887243084851438367879237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42591495389900958911919491 63887243084851438367879237)
          ·
            refine ⟨11978858078409644693977357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63887243084851438367879237 11978858078409644693977357)
            ·
              refine ⟨4492071779403616760241509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11978858078409644693977357 4492071779403616760241509)
              ·
                refine ⟨842263458638178142545283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4492071779403616760241509 842263458638178142545283)
                ·
                  refine ⟨1263395187957267213817925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842263458638178142545283 1263395187957267213817925)
                  ·
                    refine ⟨236886597741987602590861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263395187957267213817925 236886597741987602590861)
                    ·
                      rfl

theorem cell23_1384005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_1384005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384005 prefixEnd_1384005 := by exact prefixLift 1384005
  have htrace : WordTrace (prefixWord ++ tailWord_1384005) baseStart_1384005 baseEnd_1384005 := by
    simpa [prefixWord, tailWord_1384005, baseEnd_1384005] using wordTrace_append hprefix tailTrace_1384005
  have hstable : (prefixWord ++ tailWord_1384005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384005).length < 2 ^ (prefixWord ++ tailWord_1384005).sum := by decide
  have hdescent : baseEnd_1384005 < baseStart_1384005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384011 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3]
def baseStart_1384011 : Nat := 118140960795 + 1384011 * 2 ^ 59
def prefixEnd_1384011 : Nat := 4983230072969 + 3 ^ 40 * 1384011 * 2
def baseEnd_1384011 : Nat := 710662874109889784297555

theorem tailTrace_1384011 : CollatzResearch.WordTrace tailWord_1384011 prefixEnd_1384011 710662874109889784297555 := by
  unfold tailWord_1384011
  simp only [CollatzResearch.WordTrace]
  refine ⟨50479028188971992105511887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33652685459314661403674591 50479028188971992105511887)
  ·
    refine ⟨75718542283457988158267831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50479028188971992105511887 75718542283457988158267831)
    ·
      refine ⟨113577813425186982237401747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75718542283457988158267831 113577813425186982237401747)
      ·
        refine ⟨170366720137780473356102621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113577813425186982237401747 170366720137780473356102621)
        ·
          refine ⟨63887520051667677508538483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170366720137780473356102621 63887520051667677508538483)
          ·
            refine ⟨95831280077501516262807725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63887520051667677508538483 95831280077501516262807725)
            ·
              refine ⟨35936730029063068598552897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95831280077501516262807725 35936730029063068598552897)
              ·
                refine ⟨26952547521797301448914673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35936730029063068598552897 26952547521797301448914673)
                ·
                  refine ⟨20214410641347976086686005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26952547521797301448914673 20214410641347976086686005)
                  ·
                    refine ⟨1895100997626372758126813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20214410641347976086686005 1895100997626372758126813)
                    ·
                      refine ⟨710662874109889784297555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1895100997626372758126813 710662874109889784297555)
                      ·
                        rfl

theorem cell23_1384011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3].length) (baseStart_1384011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384011 prefixEnd_1384011 := by exact prefixLift 1384011
  have htrace : WordTrace (prefixWord ++ tailWord_1384011) baseStart_1384011 baseEnd_1384011 := by
    simpa [prefixWord, tailWord_1384011, baseEnd_1384011] using wordTrace_append hprefix tailTrace_1384011
  have hstable : (prefixWord ++ tailWord_1384011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384011).length < 2 ^ (prefixWord ++ tailWord_1384011).sum := by decide
  have hdescent : baseEnd_1384011 < baseStart_1384011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384018 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_1384018 : Nat := 118140960795 + 1384018 * 2 ^ 59
def prefixEnd_1384018 : Nat := 4983230072969 + 3 ^ 40 * 1384018 * 2
def baseEnd_1384018 : Nat := 78962940941607917434447

theorem tailTrace_1384018 : CollatzResearch.WordTrace tailWord_1384018 prefixEnd_1384018 78962940941607917434447 := by
  unfold tailWord_1384018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12619820874986658075254177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33652855666631088200677805 12619820874986658075254177)
  ·
    refine ⟨9464865656239993556440633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12619820874986658075254177 9464865656239993556440633)
    ·
      refine ⟨7098649242179995167330475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9464865656239993556440633 7098649242179995167330475)
      ·
        refine ⟨10647973863269992750995713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098649242179995167330475 10647973863269992750995713)
        ·
          refine ⟨7985980397452494563246785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10647973863269992750995713 7985980397452494563246785)
          ·
            refine ⟨5989485298089370922435089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7985980397452494563246785 5989485298089370922435089)
            ·
              refine ⟨4492113973567028191826317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5989485298089370922435089 4492113973567028191826317)
              ·
                refine ⟨1684542740087635571934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4492113973567028191826317 1684542740087635571934869)
                ·
                  refine ⟨78962940941607917434447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1684542740087635571934869 78962940941607917434447)
                  ·
                    rfl

theorem cell23_1384018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_1384018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384018 prefixEnd_1384018 := by exact prefixLift 1384018
  have htrace : WordTrace (prefixWord ++ tailWord_1384018) baseStart_1384018 baseEnd_1384018 := by
    simpa [prefixWord, tailWord_1384018, baseEnd_1384018] using wordTrace_append hprefix tailTrace_1384018
  have hstable : (prefixWord ++ tailWord_1384018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384018).length < 2 ^ (prefixWord ++ tailWord_1384018).sum := by decide
  have hdescent : baseEnd_1384018 < baseStart_1384018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384029 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1384029 : Nat := 118140960795 + 1384029 * 2 ^ 59
def prefixEnd_1384029 : Nat := 4983230072969 + 3 ^ 40 * 1384029 * 2
def baseEnd_1384029 : Nat := 710672116761670713872473

theorem tailTrace_1384029 : CollatzResearch.WordTrace tailWord_1384029 prefixEnd_1384029 710672116761670713872473 := by
  unfold tailWord_1384029
  simp only [CollatzResearch.WordTrace]
  refine ⟨50479684702906781179667141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33653123135271187453111427 50479684702906781179667141)
  ·
    refine ⟨9464940881795021471187589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50479684702906781179667141 9464940881795021471187589)
    ·
      refine ⟨1774676415336566525847673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9464940881795021471187589 1774676415336566525847673)
      ·
        refine ⟨1331007311502424894385755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1774676415336566525847673 1331007311502424894385755)
        ·
          refine ⟨1996510967253637341578633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331007311502424894385755 1996510967253637341578633)
          ·
            refine ⟨1497383225440228006183975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996510967253637341578633 1497383225440228006183975)
            ·
              refine ⟨2246074838160342009275963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497383225440228006183975 2246074838160342009275963)
              ·
                refine ⟨3369112257240513013913945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246074838160342009275963 3369112257240513013913945)
                ·
                  refine ⟨2526834192930384760435459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3369112257240513013913945 2526834192930384760435459)
                  ·
                    refine ⟨3790251289395577140653189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526834192930384760435459 3790251289395577140653189)
                    ·
                      refine ⟨710672116761670713872473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3790251289395577140653189 710672116761670713872473)
                      ·
                        rfl

theorem cell23_1384029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1384029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384029 prefixEnd_1384029 := by exact prefixLift 1384029
  have htrace : WordTrace (prefixWord ++ tailWord_1384029) baseStart_1384029 baseEnd_1384029 := by
    simpa [prefixWord, tailWord_1384029, baseEnd_1384029] using wordTrace_append hprefix tailTrace_1384029
  have hstable : (prefixWord ++ tailWord_1384029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384029).length < 2 ^ (prefixWord ++ tailWord_1384029).sum := by decide
  have hdescent : baseEnd_1384029 < baseStart_1384029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384082 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1384082 : Nat := 118140960795 + 1384082 * 2 ^ 59
def prefixEnd_1384082 : Nat := 4983230072969 + 3 ^ 40 * 1384082 * 2
def baseEnd_1384082 : Nat := 236899777078786335503243

theorem tailTrace_1384082 : CollatzResearch.WordTrace tailWord_1384082 prefixEnd_1384082 236899777078786335503243 := by
  unfold tailWord_1384082
  simp only [CollatzResearch.WordTrace]
  refine ⟨12620404442928692807836625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33654411847809847487564333 12620404442928692807836625)
  ·
    refine ⟨9465303332196519605877469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12620404442928692807836625 9465303332196519605877469)
    ·
      refine ⟨3549488749573694852204051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9465303332196519605877469 3549488749573694852204051)
      ·
        refine ⟨5324233124360542278306077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549488749573694852204051 5324233124360542278306077)
        ·
          refine ⟨1996587421635203354364779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5324233124360542278306077 1996587421635203354364779)
          ·
            refine ⟨2994881132452805031547169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996587421635203354364779 2994881132452805031547169)
            ·
              refine ⟨2246160849339603773660377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2994881132452805031547169 2246160849339603773660377)
              ·
                refine ⟨1684620637004702830245283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246160849339603773660377 1684620637004702830245283)
                ·
                  refine ⟨2526930955507054245367925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684620637004702830245283 2526930955507054245367925)
                  ·
                    refine ⟨236899777078786335503243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2526930955507054245367925 236899777078786335503243)
                    ·
                      rfl

theorem cell23_1384082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1384082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384082 prefixEnd_1384082 := by exact prefixLift 1384082
  have htrace : WordTrace (prefixWord ++ tailWord_1384082) baseStart_1384082 baseEnd_1384082 := by
    simpa [prefixWord, tailWord_1384082, baseEnd_1384082] using wordTrace_append hprefix tailTrace_1384082
  have hstable : (prefixWord ++ tailWord_1384082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384082).length < 2 ^ (prefixWord ++ tailWord_1384082).sum := by decide
  have hdescent : baseEnd_1384082 < baseStart_1384082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384119 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 3, 2, 2]
def baseStart_1384119 : Nat := 118140960795 + 1384119 * 2 ^ 59
def prefixEnd_1384119 : Nat := 4983230072969 + 3 ^ 40 * 1384119 * 2
def baseEnd_1384119 : Nat := 710718330020575361747059

theorem tailTrace_1384119 : CollatzResearch.WordTrace tailWord_1384119 prefixEnd_1384119 710718330020575361747059 := by
  unfold tailWord_1384119
  simp only [CollatzResearch.WordTrace]
  refine ⟨50482967272580726550443411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33655311515053817700295607 50482967272580726550443411)
  ·
    refine ⟨75724450908871089825665117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50482967272580726550443411 75724450908871089825665117)
    ·
      refine ⟨28396669090826658684624419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75724450908871089825665117 28396669090826658684624419)
      ·
        refine ⟨42595003636239988026936629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28396669090826658684624419 42595003636239988026936629)
        ·
          refine ⟨3993281590897498877525309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42595003636239988026936629 3993281590897498877525309)
          ·
            refine ⟨1497480596586562079071991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3993281590897498877525309 1497480596586562079071991)
            ·
              refine ⟨2246220894879843118607987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497480596586562079071991 2246220894879843118607987)
              ·
                refine ⟨3369331342319764677911981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246220894879843118607987 3369331342319764677911981)
                ·
                  refine ⟨1263499253369911754216993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3369331342319764677911981 1263499253369911754216993)
                  ·
                    refine ⟨947624440027433815662745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1263499253369911754216993 947624440027433815662745)
                    ·
                      refine ⟨710718330020575361747059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947624440027433815662745 710718330020575361747059)
                      ·
                        rfl

theorem cell23_1384119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_1384119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384119 prefixEnd_1384119 := by exact prefixLift 1384119
  have htrace : WordTrace (prefixWord ++ tailWord_1384119) baseStart_1384119 baseEnd_1384119 := by
    simpa [prefixWord, tailWord_1384119, baseEnd_1384119] using wordTrace_append hprefix tailTrace_1384119
  have hstable : (prefixWord ++ tailWord_1384119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384119).length < 2 ^ (prefixWord ++ tailWord_1384119).sum := by decide
  have hdescent : baseEnd_1384119 < baseStart_1384119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384156 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1384156 : Nat := 118140960795 + 1384156 * 2 ^ 59
def prefixEnd_1384156 : Nat := 4983230072969 + 3 ^ 40 * 1384156 * 2
def baseEnd_1384156 : Nat := 710737328804791716984389

theorem tailTrace_1384156 : CollatzResearch.WordTrace tailWord_1384156 prefixEnd_1384156 710737328804791716984389 := by
  unfold tailWord_1384156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25242158386723340934770161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33656211182297787913026881 25242158386723340934770161)
  ·
    refine ⟨18931618790042505701077621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25242158386723340934770161 18931618790042505701077621)
    ·
      refine ⟨1774839261566484909476027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18931618790042505701077621 1774839261566484909476027)
      ·
        refine ⟨2662258892349727364214041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774839261566484909476027 2662258892349727364214041)
        ·
          refine ⟨1996694169262295523160531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662258892349727364214041 1996694169262295523160531)
          ·
            refine ⟨2995041253893443284740797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996694169262295523160531 2995041253893443284740797)
            ·
              refine ⟨1123140470210041231777799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2995041253893443284740797 1123140470210041231777799)
              ·
                refine ⟨1684710705315061847666699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123140470210041231777799 1684710705315061847666699)
                ·
                  refine ⟨2527066057972592771500049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684710705315061847666699 2527066057972592771500049)
                  ·
                    refine ⟨1895299543479444578625037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2527066057972592771500049 1895299543479444578625037)
                    ·
                      refine ⟨710737328804791716984389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1895299543479444578625037 710737328804791716984389)
                      ·
                        rfl

theorem cell23_1384156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1384156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384156 prefixEnd_1384156 := by exact prefixLift 1384156
  have htrace : WordTrace (prefixWord ++ tailWord_1384156) baseStart_1384156 baseEnd_1384156 := by
    simpa [prefixWord, tailWord_1384156, baseEnd_1384156] using wordTrace_append hprefix tailTrace_1384156
  have hstable : (prefixWord ++ tailWord_1384156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384156).length < 2 ^ (prefixWord ++ tailWord_1384156).sum := by decide
  have hdescent : baseEnd_1384156 < baseStart_1384156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384175 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 3, 4, 2]
def baseStart_1384175 : Nat := 118140960795 + 1384175 * 2 ^ 59
def prefixEnd_1384175 : Nat := 4983230072969 + 3 ^ 40 * 1384175 * 2
def baseEnd_1384175 : Nat := 710747084937227142646801

theorem tailTrace_1384175 : CollatzResearch.WordTrace tailWord_1384175 prefixEnd_1384175 710747084937227142646801 := by
  unfold tailWord_1384175
  simp only [CollatzResearch.WordTrace]
  refine ⟨50485009760377848114481979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33656673173585232076321319 50485009760377848114481979)
  ·
    refine ⟨75727514640566772171722969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50485009760377848114481979 75727514640566772171722969)
    ·
      refine ⟨56795635980425079128792227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75727514640566772171722969 56795635980425079128792227)
      ·
        refine ⟨85193453970637618693188341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56795635980425079128792227 85193453970637618693188341)
        ·
          refine ⟨7986886309747276752486407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85193453970637618693188341 7986886309747276752486407)
          ·
            refine ⟨11980329464620915128729611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986886309747276752486407 11980329464620915128729611)
            ·
              refine ⟨17970494196931372693094417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11980329464620915128729611 17970494196931372693094417)
              ·
                refine ⟨13477870647698529519820813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17970494196931372693094417 13477870647698529519820813)
                ·
                  refine ⟨5054201492886948569932805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13477870647698529519820813 5054201492886948569932805)
                  ·
                    refine ⟨947662779916302856862401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5054201492886948569932805 947662779916302856862401)
                    ·
                      refine ⟨710747084937227142646801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947662779916302856862401 710747084937227142646801)
                      ·
                        rfl

theorem cell23_1384175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4, 2].length) (baseStart_1384175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384175 prefixEnd_1384175 := by exact prefixLift 1384175
  have htrace : WordTrace (prefixWord ++ tailWord_1384175) baseStart_1384175 baseEnd_1384175 := by
    simpa [prefixWord, tailWord_1384175, baseEnd_1384175] using wordTrace_append hprefix tailTrace_1384175
  have hstable : (prefixWord ++ tailWord_1384175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384175).length < 2 ^ (prefixWord ++ tailWord_1384175).sum := by decide
  have hdescent : baseEnd_1384175 < baseStart_1384175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384225 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1384225 : Nat := 118140960795 + 1384225 * 2 ^ 59
def prefixEnd_1384225 : Nat := 4983230072969 + 3 ^ 40 * 1384225 * 2
def baseEnd_1384225 : Nat := 710772758969951947021571

theorem tailTrace_1384225 : CollatzResearch.WordTrace tailWord_1384225 prefixEnd_1384225 710772758969951947021571 := by
  unfold tailWord_1384225
  simp only [CollatzResearch.WordTrace]
  refine ⟨50486833410196706653802129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33657888940131137769201419 50486833410196706653802129)
  ·
    refine ⟨37865125057647529990351597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50486833410196706653802129 37865125057647529990351597)
    ·
      refine ⟨14199421896617823746381849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37865125057647529990351597 14199421896617823746381849)
      ·
        refine ⟨10649566422463367809786387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14199421896617823746381849 10649566422463367809786387)
        ·
          refine ⟨15974349633695051714679581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10649566422463367809786387 15974349633695051714679581)
          ·
            refine ⟨5990381112635644393004843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15974349633695051714679581 5990381112635644393004843)
            ·
              refine ⟨8985571668953466589507265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990381112635644393004843 8985571668953466589507265)
              ·
                refine ⟨6739178751715099942130449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8985571668953466589507265 6739178751715099942130449)
                ·
                  refine ⟨5054384063786324956597837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6739178751715099942130449 5054384063786324956597837)
                  ·
                    refine ⟨1895394023919871858724189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5054384063786324956597837 1895394023919871858724189)
                    ·
                      refine ⟨710772758969951947021571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1895394023919871858724189 710772758969951947021571)
                      ·
                        rfl

theorem cell23_1384225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1384225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384225 prefixEnd_1384225 := by exact prefixLift 1384225
  have htrace : WordTrace (prefixWord ++ tailWord_1384225) baseStart_1384225 baseEnd_1384225 := by
    simpa [prefixWord, tailWord_1384225, baseEnd_1384225] using wordTrace_append hprefix tailTrace_1384225
  have hstable : (prefixWord ++ tailWord_1384225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384225).length < 2 ^ (prefixWord ++ tailWord_1384225).sum := by decide
  have hdescent : baseEnd_1384225 < baseStart_1384225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384232 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 5]
def baseStart_1384232 : Nat := 118140960795 + 1384232 * 2 ^ 59
def prefixEnd_1384232 : Nat := 4983230072969 + 3 ^ 40 * 1384232 * 2
def baseEnd_1384232 : Nat := 78975150370503713292671

theorem tailTrace_1384232 : CollatzResearch.WordTrace tailWord_1384232 prefixEnd_1384232 78975150370503713292671 := by
  unfold tailWord_1384232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25243544360585673424653475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33658059147447564566204633 25243544360585673424653475)
  ·
    refine ⟨37865316540878510136980213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25243544360585673424653475 37865316540878510136980213)
    ·
      refine ⟨3549873425707360325341895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37865316540878510136980213 3549873425707360325341895)
      ·
        refine ⟨5324810138561040488012843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549873425707360325341895 5324810138561040488012843)
        ·
          refine ⟨7987215207841560732019265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324810138561040488012843 7987215207841560732019265)
          ·
            refine ⟨5990411405881170549014449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7987215207841560732019265 5990411405881170549014449)
            ·
              refine ⟨4492808554410877911760837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5990411405881170549014449 4492808554410877911760837)
              ·
                refine ⟨842401603952039608455157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4492808554410877911760837 842401603952039608455157)
                ·
                  refine ⟨78975150370503713292671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 842401603952039608455157 78975150370503713292671)
                  ·
                    rfl

theorem cell23_1384232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 5].length) (baseStart_1384232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384232 prefixEnd_1384232 := by exact prefixLift 1384232
  have htrace : WordTrace (prefixWord ++ tailWord_1384232) baseStart_1384232 baseEnd_1384232 := by
    simpa [prefixWord, tailWord_1384232, baseEnd_1384232] using wordTrace_append hprefix tailTrace_1384232
  have hstable : (prefixWord ++ tailWord_1384232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384232).length < 2 ^ (prefixWord ++ tailWord_1384232).sum := by decide
  have hdescent : baseEnd_1384232 < baseStart_1384232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384265 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_1384265 : Nat := 118140960795 + 1384265 * 2 ^ 59
def prefixEnd_1384265 : Nat := 4983230072969 + 3 ^ 40 * 1384265 * 2
def baseEnd_1384265 : Nat := 710793298196131790521387

theorem tailTrace_1384265 : CollatzResearch.WordTrace tailWord_1384265 prefixEnd_1384265 710793298196131790521387 := by
  unfold tailWord_1384265
  simp only [CollatzResearch.WordTrace]
  refine ⟨50488292330051793485258249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33658861553367862323505499 50488292330051793485258249)
  ·
    refine ⟨37866219247538845113943687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50488292330051793485258249 37866219247538845113943687)
    ·
      refine ⟨56799328871308267670915531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37866219247538845113943687 56799328871308267670915531)
      ·
        refine ⟨85198993306962401506373297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56799328871308267670915531 85198993306962401506373297)
        ·
          refine ⟨63899244980221801129779973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85198993306962401506373297 63899244980221801129779973)
          ·
            refine ⟨11981108433791587711833745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63899244980221801129779973 11981108433791587711833745)
            ·
              refine ⟨8985831325343690783875309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11981108433791587711833745 8985831325343690783875309)
              ·
                refine ⟨3369686747003884043953241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8985831325343690783875309 3369686747003884043953241)
                ·
                  refine ⟨2527265060252913032964931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3369686747003884043953241 2527265060252913032964931)
                  ·
                    refine ⟨3790897590379369549447397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2527265060252913032964931 3790897590379369549447397)
                    ·
                      refine ⟨710793298196131790521387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3790897590379369549447397 710793298196131790521387)
                      ·
                        rfl

theorem cell23_1384265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_1384265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384265 prefixEnd_1384265 := by exact prefixLift 1384265
  have htrace : WordTrace (prefixWord ++ tailWord_1384265) baseStart_1384265 baseEnd_1384265 := by
    simpa [prefixWord, tailWord_1384265, baseEnd_1384265] using wordTrace_append hprefix tailTrace_1384265
  have hstable : (prefixWord ++ tailWord_1384265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384265).length < 2 ^ (prefixWord ++ tailWord_1384265).sum := by decide
  have hdescent : baseEnd_1384265 < baseStart_1384265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384305 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 6]
def baseStart_1384305 : Nat := 118140960795 + 1384305 * 2 ^ 59
def prefixEnd_1384305 : Nat := 4983230072969 + 3 ^ 40 * 1384305 * 2
def baseEnd_1384305 : Nat := 78979315269145737113467

theorem tailTrace_1384305 : CollatzResearch.WordTrace tailWord_1384305 prefixEnd_1384305 78979315269145737113467 := by
  unfold tailWord_1384305
  simp only [CollatzResearch.WordTrace]
  refine ⟨50489751249906880316714369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33659834166604586877809579 50489751249906880316714369)
  ·
    refine ⟨37867313437430160237535777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50489751249906880316714369 37867313437430160237535777)
    ·
      refine ⟨28400485078072620178151833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37867313437430160237535777 28400485078072620178151833)
      ·
        refine ⟨21300363808554465133613875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28400485078072620178151833 21300363808554465133613875)
        ·
          refine ⟨31950545712831697700420813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21300363808554465133613875 31950545712831697700420813)
          ·
            refine ⟨11981454642311886637657805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31950545712831697700420813 11981454642311886637657805)
            ·
              refine ⟨4493045490866957489121677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11981454642311886637657805 4493045490866957489121677)
              ·
                refine ⟨1684892059075109058420629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4493045490866957489121677 1684892059075109058420629)
                ·
                  refine ⟨78979315269145737113467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1684892059075109058420629 78979315269145737113467)
                  ·
                    rfl

theorem cell23_1384305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 6].length) (baseStart_1384305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384305 prefixEnd_1384305 := by exact prefixLift 1384305
  have htrace : WordTrace (prefixWord ++ tailWord_1384305) baseStart_1384305 baseEnd_1384305 := by
    simpa [prefixWord, tailWord_1384305, baseEnd_1384305] using wordTrace_append hprefix tailTrace_1384305
  have hstable : (prefixWord ++ tailWord_1384305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384305).length < 2 ^ (prefixWord ++ tailWord_1384305).sum := by decide
  have hdescent : baseEnd_1384305 < baseStart_1384305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384382 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1384382 : Nat := 118140960795 + 1384382 * 2 ^ 59
def prefixEnd_1384382 : Nat := 4983230072969 + 3 ^ 40 * 1384382 * 2
def baseEnd_1384382 : Nat := 236951125144235944252783

theorem tailTrace_1384382 : CollatzResearch.WordTrace tailWord_1384382 prefixEnd_1384382 236951125144235944252783 := by
  unfold tailWord_1384382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6311569958828490308408425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33661706447085281644844933 6311569958828490308408425)
  ·
    refine ⟨4733677469121367731306319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6311569958828490308408425 4733677469121367731306319)
    ·
      refine ⟨7100516203682051596959479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4733677469121367731306319 7100516203682051596959479)
      ·
        refine ⟨10650774305523077395439219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100516203682051596959479 10650774305523077395439219)
        ·
          refine ⟨15976161458284616093158829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10650774305523077395439219 15976161458284616093158829)
          ·
            refine ⟨5991060546856731034934561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15976161458284616093158829 5991060546856731034934561)
            ·
              refine ⟨4493295410142548276200921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991060546856731034934561 4493295410142548276200921)
              ·
                refine ⟨3369971557606911207150691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493295410142548276200921 3369971557606911207150691)
                ·
                  refine ⟨5054957336410366810726037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369971557606911207150691 5054957336410366810726037)
                  ·
                    refine ⟨236951125144235944252783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5054957336410366810726037 236951125144235944252783)
                    ·
                      rfl

theorem cell23_1384382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1384382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384382 prefixEnd_1384382 := by exact prefixLift 1384382
  have htrace : WordTrace (prefixWord ++ tailWord_1384382) baseStart_1384382 baseEnd_1384382 := by
    simpa [prefixWord, tailWord_1384382, baseEnd_1384382] using wordTrace_append hprefix tailTrace_1384382
  have hstable : (prefixWord ++ tailWord_1384382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384382).length < 2 ^ (prefixWord ++ tailWord_1384382).sum := by decide
  have hdescent : baseEnd_1384382 < baseStart_1384382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384419 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1384419 : Nat := 118140960795 + 1384419 * 2 ^ 59
def prefixEnd_1384419 : Nat := 4983230072969 + 3 ^ 40 * 1384419 * 2
def baseEnd_1384419 : Nat := 710872374216924187995679

theorem tailTrace_1384419 : CollatzResearch.WordTrace tailWord_1384419 prefixEnd_1384419 710872374216924187995679 := by
  unfold tailWord_1384419
  simp only [CollatzResearch.WordTrace]
  refine ⟨50493909171493877786364311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33662606114329251857576207 50493909171493877786364311)
  ·
    refine ⟨75740863757240816679546467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50493909171493877786364311 75740863757240816679546467)
    ·
      refine ⟨113611295635861225019319701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75740863757240816679546467 113611295635861225019319701)
      ·
        refine ⟨5325529482930994922780611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113611295635861225019319701 5325529482930994922780611)
        ·
          refine ⟨7988294224396492384170917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325529482930994922780611 7988294224396492384170917)
          ·
            refine ⟨1497805167074342322032047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7988294224396492384170917 1497805167074342322032047)
            ·
              refine ⟨2246707750611513483048071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497805167074342322032047 2246707750611513483048071)
              ·
                refine ⟨3370061625917270224572107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246707750611513483048071 3370061625917270224572107)
                ·
                  refine ⟨5055092438875905336858161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370061625917270224572107 5055092438875905336858161)
                  ·
                    refine ⟨3791319329156929002643621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5055092438875905336858161 3791319329156929002643621)
                    ·
                      refine ⟨710872374216924187995679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3791319329156929002643621 710872374216924187995679)
                      ·
                        rfl

theorem cell23_1384419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1384419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384419 prefixEnd_1384419 := by exact prefixLift 1384419
  have htrace : WordTrace (prefixWord ++ tailWord_1384419) baseStart_1384419 baseEnd_1384419 := by
    simpa [prefixWord, tailWord_1384419, baseEnd_1384419] using wordTrace_append hprefix tailTrace_1384419
  have hstable : (prefixWord ++ tailWord_1384419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384419).length < 2 ^ (prefixWord ++ tailWord_1384419).sum := by decide
  have hdescent : baseEnd_1384419 < baseStart_1384419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384429 : List Nat := [1, 5, 1, 4, 1, 1, 1, 9]
def baseStart_1384429 : Nat := 118140960795 + 1384429 * 2 ^ 59
def prefixEnd_1384429 : Nat := 4983230072969 + 3 ^ 40 * 1384429 * 2
def baseEnd_1384429 : Nat := 26328796630498857365579

theorem tailTrace_1384429 : CollatzResearch.WordTrace tailWord_1384429 prefixEnd_1384429 26328796630498857365579 := by
  unfold tailWord_1384429
  simp only [CollatzResearch.WordTrace]
  refine ⟨50494273901457649494228341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33662849267638432996152227 50494273901457649494228341)
  ·
    refine ⟨4733838178261654640083907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50494273901457649494228341 4733838178261654640083907)
    ·
      refine ⟨7100757267392481960125861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4733838178261654640083907 7100757267392481960125861)
      ·
        refine ⟨1331391987636090367523599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7100757267392481960125861 1331391987636090367523599)
        ·
          refine ⟨1997087981454135551285399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331391987636090367523599 1997087981454135551285399)
          ·
            refine ⟨2995631972181203326928099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997087981454135551285399 2995631972181203326928099)
            ·
              refine ⟨4493447958271804990392149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995631972181203326928099 4493447958271804990392149)
              ·
                refine ⟨26328796630498857365579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4493447958271804990392149 26328796630498857365579)
                ·
                  rfl

theorem cell23_1384429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 9].length) (baseStart_1384429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384429 prefixEnd_1384429 := by exact prefixLift 1384429
  have htrace : WordTrace (prefixWord ++ tailWord_1384429) baseStart_1384429 baseEnd_1384429 := by
    simpa [prefixWord, tailWord_1384429, baseEnd_1384429] using wordTrace_append hprefix tailTrace_1384429
  have hstable : (prefixWord ++ tailWord_1384429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384429).length < 2 ^ (prefixWord ++ tailWord_1384429).sum := by decide
  have hdescent : baseEnd_1384429 < baseStart_1384429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384462 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1384462 : Nat := 118140960795 + 1384462 * 2 ^ 59
def prefixEnd_1384462 : Nat := 4983230072969 + 3 ^ 40 * 1384462 * 2
def baseEnd_1384462 : Nat := 710894453885067519757981

theorem tailTrace_1384462 : CollatzResearch.WordTrace tailWord_1384462 prefixEnd_1384462 710894453885067519757981 := by
  unfold tailWord_1384462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6311934688792262016272455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33663651673558730753453093 6311934688792262016272455)
  ·
    refine ⟨9467902033188393024408683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6311934688792262016272455 9467902033188393024408683)
    ·
      refine ⟨14201853049782589536613025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9467902033188393024408683 14201853049782589536613025)
      ·
        refine ⟨10651389787336942152459769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14201853049782589536613025 10651389787336942152459769)
        ·
          refine ⟨7988542340502706614344827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10651389787336942152459769 7988542340502706614344827)
          ·
            refine ⟨11982813510754059921517241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988542340502706614344827 11982813510754059921517241)
            ·
              refine ⟨8987110133065544941137931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11982813510754059921517241 8987110133065544941137931)
              ·
                refine ⟨13480665199598317411706897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8987110133065544941137931 13480665199598317411706897)
                ·
                  refine ⟨10110498899698738058780173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13480665199598317411706897 10110498899698738058780173)
                  ·
                    refine ⟨3791437087387026772042565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10110498899698738058780173 3791437087387026772042565)
                    ·
                      refine ⟨710894453885067519757981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3791437087387026772042565 710894453885067519757981)
                      ·
                        rfl

theorem cell23_1384462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1384462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384462 prefixEnd_1384462 := by exact prefixLift 1384462
  have htrace : WordTrace (prefixWord ++ tailWord_1384462) baseStart_1384462 baseEnd_1384462 := by
    simpa [prefixWord, tailWord_1384462, baseEnd_1384462] using wordTrace_append hprefix tailTrace_1384462
  have hstable : (prefixWord ++ tailWord_1384462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384462).length < 2 ^ (prefixWord ++ tailWord_1384462).sum := by decide
  have hdescent : baseEnd_1384462 < baseStart_1384462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384479 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 1, 4, 2]
def baseStart_1384479 : Nat := 118140960795 + 1384479 * 2 ^ 59
def prefixEnd_1384479 : Nat := 4983230072969 + 3 ^ 40 * 1384479 * 2
def baseEnd_1384479 : Nat := 710903183056193953245403

theorem tailTrace_1384479 : CollatzResearch.WordTrace tailWord_1384479 prefixEnd_1384479 710903183056193953245403 := by
  unfold tailWord_1384479
  simp only [CollatzResearch.WordTrace]
  refine ⟨50496097551276508033548491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33664065034184338689032327 50496097551276508033548491)
  ·
    refine ⟨75744146326914762050322737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50496097551276508033548491 75744146326914762050322737)
    ·
      refine ⟨56808109745186071537742053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75744146326914762050322737 56808109745186071537742053)
      ·
        refine ⟨10651520577222388413326635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56808109745186071537742053 10651520577222388413326635)
        ·
          refine ⟨15977280865833582619989953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651520577222388413326635 15977280865833582619989953)
          ·
            refine ⟨11982960649375186964992465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15977280865833582619989953 11982960649375186964992465)
            ·
              refine ⟨8987220487031390223744349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11982960649375186964992465 8987220487031390223744349)
              ·
                refine ⟨3370207682636771333904131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8987220487031390223744349 3370207682636771333904131)
                ·
                  refine ⟨5055311523955157000856197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370207682636771333904131 5055311523955157000856197)
                  ·
                    refine ⟨947870910741591937660537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055311523955157000856197 947870910741591937660537)
                    ·
                      refine ⟨710903183056193953245403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947870910741591937660537 710903183056193953245403)
                      ·
                        rfl

theorem cell23_1384479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_1384479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384479 prefixEnd_1384479 := by exact prefixLift 1384479
  have htrace : WordTrace (prefixWord ++ tailWord_1384479) baseStart_1384479 baseEnd_1384479 := by
    simpa [prefixWord, tailWord_1384479, baseEnd_1384479] using wordTrace_append hprefix tailTrace_1384479
  have hstable : (prefixWord ++ tailWord_1384479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384479).length < 2 ^ (prefixWord ++ tailWord_1384479).sum := by decide
  have hdescent : baseEnd_1384479 < baseStart_1384479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384482 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1384482 : Nat := 118140960795 + 1384482 * 2 ^ 59
def prefixEnd_1384482 : Nat := 4983230072969 + 3 ^ 40 * 1384482 * 2
def baseEnd_1384482 : Nat := 710904723498157441507889

theorem tailTrace_1384482 : CollatzResearch.WordTrace tailWord_1384482 prefixEnd_1384482 710904723498157441507889 := by
  unfold tailWord_1384482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624051742566409886476925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33664137980177093030605133 12624051742566409886476925)
  ·
    refine ⟨4734019403462403707428847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12624051742566409886476925 4734019403462403707428847)
    ·
      refine ⟨7101029105193605561143271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4734019403462403707428847 7101029105193605561143271)
      ·
        refine ⟨10651543657790408341714907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7101029105193605561143271 10651543657790408341714907)
        ·
          refine ⟨15977315486685612512572361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651543657790408341714907 15977315486685612512572361)
          ·
            refine ⟨11982986615014209384429271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15977315486685612512572361 11982986615014209384429271)
            ·
              refine ⟨17974479922521314076643907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11982986615014209384429271 17974479922521314076643907)
              ·
                refine ⟨26961719883781971114965861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17974479922521314076643907 26961719883781971114965861)
                ·
                  refine ⟨5055322478209119584056099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26961719883781971114965861 5055322478209119584056099)
                  ·
                    refine ⟨7582983717313679376084149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5055322478209119584056099 7582983717313679376084149)
                    ·
                      refine ⟨710904723498157441507889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7582983717313679376084149 710904723498157441507889)
                      ·
                        rfl

theorem cell23_1384482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1384482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384482 prefixEnd_1384482 := by exact prefixLift 1384482
  have htrace : WordTrace (prefixWord ++ tailWord_1384482) baseStart_1384482 baseEnd_1384482 := by
    simpa [prefixWord, tailWord_1384482, baseEnd_1384482] using wordTrace_append hprefix tailTrace_1384482
  have hstable : (prefixWord ++ tailWord_1384482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384482).length < 2 ^ (prefixWord ++ tailWord_1384482).sum := by decide
  have hdescent : baseEnd_1384482 < baseStart_1384482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384495 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_1384495 : Nat := 118140960795 + 1384495 * 2 ^ 59
def prefixEnd_1384495 : Nat := 4983230072969 + 3 ^ 40 * 1384495 * 2
def baseEnd_1384495 : Nat := 710911398746665890645329

theorem tailTrace_1384495 : CollatzResearch.WordTrace tailWord_1384495 prefixEnd_1384495 710911398746665890645329 := by
  unfold tailWord_1384495
  simp only [CollatzResearch.WordTrace]
  refine ⟨50496681119218542766130939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33664454079479028510753959 50496681119218542766130939)
  ·
    refine ⟨75745021678827814149196409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50496681119218542766130939 75745021678827814149196409)
    ·
      refine ⟨56808766259120860611897307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75745021678827814149196409 56808766259120860611897307)
      ·
        refine ⟨85213149388681290917845961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56808766259120860611897307 85213149388681290917845961)
        ·
          refine ⟨63909862041510968188384471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85213149388681290917845961 63909862041510968188384471)
          ·
            refine ⟨95864793062266452282576707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63909862041510968188384471 95864793062266452282576707)
            ·
              refine ⟨143797189593399678423865061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95864793062266452282576707 143797189593399678423865061)
              ·
                refine ⟨26961973048762439704474699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143797189593399678423865061 26961973048762439704474699)
                ·
                  refine ⟨40442959573143659556712049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26961973048762439704474699 40442959573143659556712049)
                  ·
                    refine ⟨30332219679857744667534037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40442959573143659556712049 30332219679857744667534037)
                    ·
                      refine ⟨710911398746665890645329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30332219679857744667534037 710911398746665890645329)
                      ·
                        rfl

theorem cell23_1384495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_1384495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384495 prefixEnd_1384495 := by exact prefixLift 1384495
  have htrace : WordTrace (prefixWord ++ tailWord_1384495) baseStart_1384495 baseEnd_1384495 := by
    simpa [prefixWord, tailWord_1384495, baseEnd_1384495] using wordTrace_append hprefix tailTrace_1384495
  have hstable : (prefixWord ++ tailWord_1384495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384495).length < 2 ^ (prefixWord ++ tailWord_1384495).sum := by decide
  have hdescent : baseEnd_1384495 < baseStart_1384495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384513 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1384513 : Nat := 118140960795 + 1384513 * 2 ^ 59
def prefixEnd_1384513 : Nat := 4983230072969 + 3 ^ 40 * 1384513 * 2
def baseEnd_1384513 : Nat := 710920641398446820220247

theorem tailTrace_1384513 : CollatzResearch.WordTrace tailWord_1384513 prefixEnd_1384513 710920641398446820220247 := by
  unfold tailWord_1384513
  simp only [CollatzResearch.WordTrace]
  refine ⟨50497337633153331840286193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33664891755435554560190795 50497337633153331840286193)
  ·
    refine ⟨37873003224864998880214645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50497337633153331840286193 37873003224864998880214645)
    ·
      refine ⟨3550594052331093645020123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37873003224864998880214645 3550594052331093645020123)
      ·
        refine ⟨5325891078496640467530185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550594052331093645020123 5325891078496640467530185)
        ·
          refine ⟨3994418308872480350647639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5325891078496640467530185 3994418308872480350647639)
          ·
            refine ⟨5991627463308720525971459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994418308872480350647639 5991627463308720525971459)
            ·
              refine ⟨8987441194963080788957189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5991627463308720525971459 8987441194963080788957189)
              ·
                refine ⟨1685145224055577647929473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8987441194963080788957189 1685145224055577647929473)
                ·
                  refine ⟨1263858918041683235947105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1685145224055577647929473 1263858918041683235947105)
                  ·
                    refine ⟨947894188531262426960329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1263858918041683235947105 947894188531262426960329)
                    ·
                      refine ⟨710920641398446820220247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947894188531262426960329 710920641398446820220247)
                      ·
                        rfl

theorem cell23_1384513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1384513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384513 prefixEnd_1384513 := by exact prefixLift 1384513
  have htrace : WordTrace (prefixWord ++ tailWord_1384513) baseStart_1384513 baseEnd_1384513 := by
    simpa [prefixWord, tailWord_1384513, baseEnd_1384513] using wordTrace_append hprefix tailTrace_1384513
  have hstable : (prefixWord ++ tailWord_1384513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384513).length < 2 ^ (prefixWord ++ tailWord_1384513).sum := by decide
  have hdescent : baseEnd_1384513 < baseStart_1384513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384519 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 5]
def baseStart_1384519 : Nat := 118140960795 + 1384519 * 2 ^ 59
def prefixEnd_1384519 : Nat := 4983230072969 + 3 ^ 40 * 1384519 * 2
def baseEnd_1384519 : Nat := 78991524698041532971691

theorem tailTrace_1384519 : CollatzResearch.WordTrace tailWord_1384519 prefixEnd_1384519 78991524698041532971691 := by
  unfold tailWord_1384519
  simp only [CollatzResearch.WordTrace]
  refine ⟨50497556471131594865004611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33665037647421063243336407 50497556471131594865004611)
  ·
    refine ⟨75746334706697392297506917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50497556471131594865004611 75746334706697392297506917)
    ·
      refine ⟨14202437757505761055782547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75746334706697392297506917 14202437757505761055782547)
      ·
        refine ⟨21303656636258641583673821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14202437757505761055782547 21303656636258641583673821)
        ·
          refine ⟨7988871238596990593877683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21303656636258641583673821 7988871238596990593877683)
          ·
            refine ⟨11983306857895485890816525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988871238596990593877683 11983306857895485890816525)
            ·
              refine ⟨4493740071710807209056197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11983306857895485890816525 4493740071710807209056197)
              ·
                refine ⟨842576263445776351698037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4493740071710807209056197 842576263445776351698037)
                ·
                  refine ⟨78991524698041532971691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 842576263445776351698037 78991524698041532971691)
                  ·
                    rfl

theorem cell23_1384519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 5].length) (baseStart_1384519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384519 prefixEnd_1384519 := by exact prefixLift 1384519
  have htrace : WordTrace (prefixWord ++ tailWord_1384519) baseStart_1384519 baseEnd_1384519 := by
    simpa [prefixWord, tailWord_1384519, baseEnd_1384519] using wordTrace_append hprefix tailTrace_1384519
  have hstable : (prefixWord ++ tailWord_1384519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384519).length < 2 ^ (prefixWord ++ tailWord_1384519).sum := by decide
  have hdescent : baseEnd_1384519 < baseStart_1384519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384532 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1384532 : Nat := 118140960795 + 1384532 * 2 ^ 59
def prefixEnd_1384532 : Nat := 4983230072969 + 3 ^ 40 * 1384532 * 2
def baseEnd_1384532 : Nat := 236976799176960748627553

theorem tailTrace_1384532 : CollatzResearch.WordTrace tailWord_1384532 prefixEnd_1384532 236976799176960748627553 := by
  unfold tailWord_1384532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25249015310042249042613925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33665353746722998723485233 25249015310042249042613925)
  ·
    refine ⟨4734190370632921695490111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25249015310042249042613925 4734190370632921695490111)
    ·
      refine ⟨7101285555949382543235167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4734190370632921695490111 7101285555949382543235167)
      ·
        refine ⟨10651928333924073814852751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7101285555949382543235167 10651928333924073814852751)
        ·
          refine ⟨15977892500886110722279127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651928333924073814852751 15977892500886110722279127)
          ·
            refine ⟨23966838751329166083418691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15977892500886110722279127 23966838751329166083418691)
            ·
              refine ⟨35950258126993749125128037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23966838751329166083418691 35950258126993749125128037)
              ·
                refine ⟨6740673398811327960961507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35950258126993749125128037 6740673398811327960961507)
                ·
                  refine ⟨10111010098216991941442261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740673398811327960961507 10111010098216991941442261)
                  ·
                    refine ⟨236976799176960748627553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10111010098216991941442261 236976799176960748627553)
                    ·
                      rfl

theorem cell23_1384532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1384532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384532 prefixEnd_1384532 := by exact prefixLift 1384532
  have htrace : WordTrace (prefixWord ++ tailWord_1384532) baseStart_1384532 baseEnd_1384532 := by
    simpa [prefixWord, tailWord_1384532, baseEnd_1384532] using wordTrace_append hprefix tailTrace_1384532
  have hstable : (prefixWord ++ tailWord_1384532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384532).length < 2 ^ (prefixWord ++ tailWord_1384532).sum := by decide
  have hdescent : baseEnd_1384532 < baseStart_1384532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384549 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_1384549 : Nat := 118140960795 + 1384549 * 2 ^ 59
def prefixEnd_1384549 : Nat := 4983230072969 + 3 ^ 40 * 1384549 * 2
def baseEnd_1384549 : Nat := 236979708900669559790027

theorem tailTrace_1384549 : CollatzResearch.WordTrace tailWord_1384549 prefixEnd_1384549 236979708900669559790027 := by
  unfold tailWord_1384549
  simp only [CollatzResearch.WordTrace]
  refine ⟨50498650661022909988596701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33665767107348606659064467 50498650661022909988596701)
  ·
    refine ⟨18936993997883591245723763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50498650661022909988596701 18936993997883591245723763)
    ·
      refine ⟨28405490996825386868585645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18936993997883591245723763 28405490996825386868585645)
      ·
        refine ⟨10652059123809520075719617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28405490996825386868585645 10652059123809520075719617)
        ·
          refine ⟨7989044342857140056789713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10652059123809520075719617 7989044342857140056789713)
          ·
            refine ⟨5991783257142855042592285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7989044342857140056789713 5991783257142855042592285)
            ·
              refine ⟨2246918721428570640972107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5991783257142855042592285 2246918721428570640972107)
              ·
                refine ⟨3370378082142855961458161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246918721428570640972107 3370378082142855961458161)
                ·
                  refine ⟨2527783561607141971093621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370378082142855961458161 2527783561607141971093621)
                  ·
                    refine ⟨236979708900669559790027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2527783561607141971093621 236979708900669559790027)
                    ·
                      rfl

theorem cell23_1384549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_1384549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384549 prefixEnd_1384549 := by exact prefixLift 1384549
  have htrace : WordTrace (prefixWord ++ tailWord_1384549) baseStart_1384549 baseEnd_1384549 := by
    simpa [prefixWord, tailWord_1384549, baseEnd_1384549] using wordTrace_append hprefix tailTrace_1384549
  have hstable : (prefixWord ++ tailWord_1384549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384549).length < 2 ^ (prefixWord ++ tailWord_1384549).sum := by decide
  have hdescent : baseEnd_1384549 < baseStart_1384549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384579 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 3, 4]
def baseStart_1384579 : Nat := 118140960795 + 1384579 * 2 ^ 59
def prefixEnd_1384579 : Nat := 4983230072969 + 3 ^ 40 * 1384579 * 2
def baseEnd_1384579 : Nat := 236984843707214520664981

theorem tailTrace_1384579 : CollatzResearch.WordTrace tailWord_1384579 prefixEnd_1384579 236984843707214520664981 := by
  unfold tailWord_1384579
  simp only [CollatzResearch.WordTrace]
  refine ⟨50499744850914225112188791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33666496567276150074792527 50499744850914225112188791)
  ·
    refine ⟨75749617276371337668283187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50499744850914225112188791 75749617276371337668283187)
    ·
      refine ⟨113624425914557006502424781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75749617276371337668283187 113624425914557006502424781)
      ·
        refine ⟨42609159717958877438409293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113624425914557006502424781 42609159717958877438409293)
        ·
          refine ⟨15978434894234579039403485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42609159717958877438409293 15978434894234579039403485)
          ·
            refine ⟨5991913085337967139776307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15978434894234579039403485 5991913085337967139776307)
            ·
              refine ⟨8987869628006950709664461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5991913085337967139776307 8987869628006950709664461)
              ·
                refine ⟨3370451110502606516124173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8987869628006950709664461 3370451110502606516124173)
                ·
                  refine ⟨1263919166438477443546565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3370451110502606516124173 1263919166438477443546565)
                  ·
                    refine ⟨236984843707214520664981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263919166438477443546565 236984843707214520664981)
                    ·
                      rfl

theorem cell23_1384579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 4].length) (baseStart_1384579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384579 prefixEnd_1384579 := by exact prefixLift 1384579
  have htrace : WordTrace (prefixWord ++ tailWord_1384579) baseStart_1384579 baseEnd_1384579 := by
    simpa [prefixWord, tailWord_1384579, baseEnd_1384579] using wordTrace_append hprefix tailTrace_1384579
  have hstable : (prefixWord ++ tailWord_1384579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384579).length < 2 ^ (prefixWord ++ tailWord_1384579).sum := by decide
  have hdescent : baseEnd_1384579 < baseStart_1384579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384586 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_1384586 : Nat := 118140960795 + 1384586 * 2 ^ 59
def prefixEnd_1384586 : Nat := 4983230072969 + 3 ^ 40 * 1384586 * 2
def baseEnd_1384586 : Nat := 710958125486225034607411

theorem tailTrace_1384586 : CollatzResearch.WordTrace tailWord_1384586 prefixEnd_1384586 710958125486225034607411 := by
  unfold tailWord_1384586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625000040472216326923403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33666666774592576871795741 12625000040472216326923403)
  ·
    refine ⟨18937500060708324490385105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12625000040472216326923403 18937500060708324490385105)
    ·
      refine ⟨14203125045531243367788829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18937500060708324490385105 14203125045531243367788829)
      ·
        refine ⟨5326171892074216262920811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14203125045531243367788829 5326171892074216262920811)
        ·
          refine ⟨7989257838111324394381217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326171892074216262920811 7989257838111324394381217)
          ·
            refine ⟨5991943378583493295785913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7989257838111324394381217 5991943378583493295785913)
            ·
              refine ⟨4493957533937619971839435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991943378583493295785913 4493957533937619971839435)
              ·
                refine ⟨6740936300906429957759153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493957533937619971839435 6740936300906429957759153)
                ·
                  refine ⟨5055702225679822468319365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6740936300906429957759153 5055702225679822468319365)
                  ·
                    refine ⟨947944167314966712809881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055702225679822468319365 947944167314966712809881)
                    ·
                      refine ⟨710958125486225034607411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 947944167314966712809881 710958125486225034607411)
                      ·
                        rfl

theorem cell23_1384586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_1384586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384586 prefixEnd_1384586 := by exact prefixLift 1384586
  have htrace : WordTrace (prefixWord ++ tailWord_1384586) baseStart_1384586 baseEnd_1384586 := by
    simpa [prefixWord, tailWord_1384586, baseEnd_1384586] using wordTrace_append hprefix tailTrace_1384586
  have hstable : (prefixWord ++ tailWord_1384586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384586).length < 2 ^ (prefixWord ++ tailWord_1384586).sum := by decide
  have hdescent : baseEnd_1384586 < baseStart_1384586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384687 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 1, 1, 3]
def baseStart_1384687 : Nat := 118140960795 + 1384687 * 2 ^ 59
def prefixEnd_1384687 : Nat := 4983230072969 + 3 ^ 40 * 1384687 * 2
def baseEnd_1384687 : Nat := 711009987032329139444447

theorem tailTrace_1384687 : CollatzResearch.WordTrace tailWord_1384687 prefixEnd_1384687 711009987032329139444447 := by
  unfold tailWord_1384687
  simp only [CollatzResearch.WordTrace]
  refine ⟨50503683934522959557120315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33669122623015306371413543 50503683934522959557120315)
  ·
    refine ⟨75755525901784439335680473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50503683934522959557120315 75755525901784439335680473)
    ·
      refine ⟨56816644426338329501760355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75755525901784439335680473 56816644426338329501760355)
      ·
        refine ⟨85224966639507494252640533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56816644426338329501760355 85224966639507494252640533)
        ·
          refine ⟨3994920311226913793092525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85224966639507494252640533 3994920311226913793092525)
          ·
            refine ⟨1498095116710092672409697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3994920311226913793092525 1498095116710092672409697)
            ·
              refine ⟨1123571337532569504307273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498095116710092672409697 1123571337532569504307273)
              ·
                refine ⟨842678503149427128230455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123571337532569504307273 842678503149427128230455)
                ·
                  refine ⟨1264017754724140692345683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842678503149427128230455 1264017754724140692345683)
                  ·
                    refine ⟨1896026632086211038518525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1264017754724140692345683 1896026632086211038518525)
                    ·
                      refine ⟨711009987032329139444447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1896026632086211038518525 711009987032329139444447)
                      ·
                        rfl

theorem cell23_1384687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 1, 3].length) (baseStart_1384687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384687 prefixEnd_1384687 := by exact prefixLift 1384687
  have htrace : WordTrace (prefixWord ++ tailWord_1384687) baseStart_1384687 baseEnd_1384687 := by
    simpa [prefixWord, tailWord_1384687, baseEnd_1384687] using wordTrace_append hprefix tailTrace_1384687
  have hstable : (prefixWord ++ tailWord_1384687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384687).length < 2 ^ (prefixWord ++ tailWord_1384687).sum := by decide
  have hdescent : baseEnd_1384687 < baseStart_1384687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
