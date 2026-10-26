import V185TrunkScan22Chunk103

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_934065 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 6]
def baseStart_934065 : Nat := 118140960795 + 934065 * 2 ^ 59
def prefixEnd_934065 : Nat := 4983230072969 + 3 ^ 40 * 934065 * 2
def baseEnd_934065 : Nat := 106583179453776266687071

theorem tailTrace_934065 : CollatzResearch.WordTrace tailWord_934065 prefixEnd_934065 106583179453776266687071 := by
  unfold tailWord_934065
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068149361049505446627649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22712099574033003631085099 34068149361049505446627649)
  ·
    refine ⟨25551112020787129084970737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34068149361049505446627649 25551112020787129084970737)
    ·
      refine ⟨19163334015590346813728053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25551112020787129084970737 19163334015590346813728053)
      ·
        refine ⟨1796562563961595013787005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19163334015590346813728053 1796562563961595013787005)
        ·
          refine ⟨673710961485598130170127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1796562563961595013787005 673710961485598130170127)
          ·
            refine ⟨1010566442228397195255191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673710961485598130170127 1010566442228397195255191)
            ·
              refine ⟨1515849663342595792882787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010566442228397195255191 1515849663342595792882787)
              ·
                refine ⟨2273774495013893689324181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515849663342595792882787 2273774495013893689324181)
                ·
                  refine ⟨106583179453776266687071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2273774495013893689324181 106583179453776266687071)
                  ·
                    rfl

theorem cell22_934065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_934065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934065 prefixEnd_934065 := by exact prefixLift 934065
  have htrace : WordTrace (prefixWord ++ tailWord_934065) baseStart_934065 baseEnd_934065 := by
    simpa [prefixWord, tailWord_934065, baseEnd_934065] using wordTrace_append hprefix tailTrace_934065
  have hstable : (prefixWord ++ tailWord_934065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934065).length < 2 ^ (prefixWord ++ tailWord_934065).sum := by decide
  have hdescent : baseEnd_934065 < baseStart_934065 := by decide
  rcases family_descends (prefixWord ++ tailWord_934065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934080 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 2, 3]
def baseStart_934080 : Nat := 118140960795 + 934080 * 2 ^ 59
def prefixEnd_934080 : Nat := 4983230072969 + 3 ^ 40 * 934080 * 2
def baseEnd_934080 : Nat := 319754673167873760936167

theorem tailTrace_934080 : CollatzResearch.WordTrace tailWord_934080 prefixEnd_934080 319754673167873760936167 := by
  unfold tailWord_934080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17034348227997581504211847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22712464303996775338949129 17034348227997581504211847)
  ·
    refine ⟨25551522341996372256317771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17034348227997581504211847 25551522341996372256317771)
    ·
      refine ⟨38327283512994558384476657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25551522341996372256317771 38327283512994558384476657)
      ·
        refine ⟨28745462634745918788357493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38327283512994558384476657 28745462634745918788357493)
        ·
          refine ⟨2694887122007429886408515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28745462634745918788357493 2694887122007429886408515)
          ·
            refine ⟨4042330683011144829612773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694887122007429886408515 4042330683011144829612773)
            ·
              refine ⟨757937003064589655552395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4042330683011144829612773 757937003064589655552395)
              ·
                refine ⟨1136905504596884483328593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757937003064589655552395 1136905504596884483328593)
                ·
                  refine ⟨852679128447663362496445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1136905504596884483328593 852679128447663362496445)
                  ·
                    refine ⟨319754673167873760936167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 852679128447663362496445 319754673167873760936167)
                    ·
                      rfl

theorem cell22_934080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_934080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934080 prefixEnd_934080 := by exact prefixLift 934080
  have htrace : WordTrace (prefixWord ++ tailWord_934080) baseStart_934080 baseEnd_934080 := by
    simpa [prefixWord, tailWord_934080, baseEnd_934080] using wordTrace_append hprefix tailTrace_934080
  have hstable : (prefixWord ++ tailWord_934080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934080).length < 2 ^ (prefixWord ++ tailWord_934080).sum := by decide
  have hdescent : baseEnd_934080 < baseStart_934080 := by decide
  rcases family_descends (prefixWord ++ tailWord_934080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934089 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_934089 : Nat := 118140960795 + 934089 * 2 ^ 59
def prefixEnd_934089 : Nat := 4983230072969 + 3 ^ 40 * 934089 * 2
def baseEnd_934089 : Nat := 319757754051800737461139

theorem tailTrace_934089 : CollatzResearch.WordTrace tailWord_934089 prefixEnd_934089 319757754051800737461139 := by
  unfold tailWord_934089
  simp only [CollatzResearch.WordTrace]
  refine ⟨34069024712962557545501321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22712683141975038363667547 34069024712962557545501321)
  ·
    refine ⟨25551768534721918159125991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34069024712962557545501321 25551768534721918159125991)
    ·
      refine ⟨38327652802082877238688987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25551768534721918159125991 38327652802082877238688987)
      ·
        refine ⟨57491479203124315858033481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38327652802082877238688987 57491479203124315858033481)
        ·
          refine ⟨43118609402343236893525111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57491479203124315858033481 43118609402343236893525111)
          ·
            refine ⟨64677914103514855340287667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43118609402343236893525111 64677914103514855340287667)
            ·
              refine ⟨97016871155272283010431501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64677914103514855340287667 97016871155272283010431501)
              ·
                refine ⟨36381326683227106128911813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97016871155272283010431501 36381326683227106128911813)
                ·
                  refine ⟨6821498753105082399170965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36381326683227106128911813 6821498753105082399170965)
                  ·
                    refine ⟨319757754051800737461139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6821498753105082399170965 319757754051800737461139)
                    ·
                      rfl

theorem cell22_934089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_934089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934089 prefixEnd_934089 := by exact prefixLift 934089
  have htrace : WordTrace (prefixWord ++ tailWord_934089) baseStart_934089 baseEnd_934089 := by
    simpa [prefixWord, tailWord_934089, baseEnd_934089] using wordTrace_append hprefix tailTrace_934089
  have hstable : (prefixWord ++ tailWord_934089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934089).length < 2 ^ (prefixWord ++ tailWord_934089).sum := by decide
  have hdescent : baseEnd_934089 < baseStart_934089 := by decide
  rcases family_descends (prefixWord ++ tailWord_934089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934091 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 5, 3]
def baseStart_934091 : Nat := 118140960795 + 934091 * 2 ^ 59
def prefixEnd_934091 : Nat := 4983230072969 + 3 ^ 40 * 934091 * 2
def baseEnd_934091 : Nat := 319758438692673398911133

theorem tailTrace_934091 : CollatzResearch.WordTrace tailWord_934091 prefixEnd_934091 319758438692673398911133 := by
  unfold tailWord_934091
  simp only [CollatzResearch.WordTrace]
  refine ⟨34069097658955311887074127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22712731772636874591382751 34069097658955311887074127)
  ·
    refine ⟨51103646488432967830611191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34069097658955311887074127 51103646488432967830611191)
    ·
      refine ⟨76655469732649451745916787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51103646488432967830611191 76655469732649451745916787)
      ·
        refine ⟨114983204598974177618875181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76655469732649451745916787 114983204598974177618875181)
        ·
          refine ⟨43118701724615316607078193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114983204598974177618875181 43118701724615316607078193)
          ·
            refine ⟨32339026293461487455308645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43118701724615316607078193 32339026293461487455308645)
            ·
              refine ⟨6063567430024028897870371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32339026293461487455308645 6063567430024028897870371)
              ·
                refine ⟨9095351145036043346805557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063567430024028897870371 9095351145036043346805557)
                ·
                  refine ⟨852689169847129063763021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9095351145036043346805557 852689169847129063763021)
                  ·
                    refine ⟨319758438692673398911133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 852689169847129063763021 319758438692673398911133)
                    ·
                      rfl

theorem cell22_934091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 3].length) (baseStart_934091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934091 prefixEnd_934091 := by exact prefixLift 934091
  have htrace : WordTrace (prefixWord ++ tailWord_934091) baseStart_934091 baseEnd_934091 := by
    simpa [prefixWord, tailWord_934091, baseEnd_934091] using wordTrace_append hprefix tailTrace_934091
  have hstable : (prefixWord ++ tailWord_934091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934091).length < 2 ^ (prefixWord ++ tailWord_934091).sum := by decide
  have hdescent : baseEnd_934091 < baseStart_934091 := by decide
  rcases family_descends (prefixWord ++ tailWord_934091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934168 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_934168 : Nat := 118140960795 + 934168 * 2 ^ 59
def prefixEnd_934168 : Nat := 4983230072969 + 3 ^ 40 * 934168 * 2
def baseEnd_934168 : Nat := 319784797366270864735897

theorem tailTrace_934168 : CollatzResearch.WordTrace tailWord_934168 prefixEnd_934168 319784797366270864735897 := by
  unfold tailWord_934168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17035953039838177018813579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22714604053117569358418105 17035953039838177018813579)
  ·
    refine ⟨25553929559757265528220369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17035953039838177018813579 25553929559757265528220369)
    ·
      refine ⟨19165447169817949146165277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25553929559757265528220369 19165447169817949146165277)
      ·
        refine ⟨7187042688681730929811979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19165447169817949146165277 7187042688681730929811979)
        ·
          refine ⟨10780564033022596394717969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7187042688681730929811979 10780564033022596394717969)
          ·
            refine ⟨8085423024766947296038477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10780564033022596394717969 8085423024766947296038477)
            ·
              refine ⟨3032033634287605236014429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8085423024766947296038477 3032033634287605236014429)
              ·
                refine ⟨1137012612857851963505411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3032033634287605236014429 1137012612857851963505411)
                ·
                  refine ⟨1705518919286777945258117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137012612857851963505411 1705518919286777945258117)
                  ·
                    refine ⟨319784797366270864735897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1705518919286777945258117 319784797366270864735897)
                    ·
                      rfl

theorem cell22_934168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_934168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934168 prefixEnd_934168 := by exact prefixLift 934168
  have htrace : WordTrace (prefixWord ++ tailWord_934168) baseStart_934168 baseEnd_934168 := by
    simpa [prefixWord, tailWord_934168, baseEnd_934168] using wordTrace_append hprefix tailTrace_934168
  have hstable : (prefixWord ++ tailWord_934168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934168).length < 2 ^ (prefixWord ++ tailWord_934168).sum := by decide
  have hdescent : baseEnd_934168 < baseStart_934168 := by decide
  rcases family_descends (prefixWord ++ tailWord_934168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934228 : List Nat := [2, 4, 1, 1, 2, 4, 8]
def baseStart_934228 : Nat := 118140960795 + 934228 * 2 ^ 59
def prefixEnd_934228 : Nat := 4983230072969 + 3 ^ 40 * 934228 * 2
def baseEnd_934228 : Nat := 11844642096016692897619

theorem tailTrace_934228 : CollatzResearch.WordTrace tailWord_934228 prefixEnd_934228 11844642096016692897619 := by
  unfold tailWord_934228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037047229729492142405669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22716062972972656189874225 17037047229729492142405669)
  ·
    refine ⟨3194446355574279776701063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17037047229729492142405669 3194446355574279776701063)
    ·
      refine ⟨4791669533361419665051595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194446355574279776701063 4791669533361419665051595)
      ·
        refine ⟨7187504300042129497577393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791669533361419665051595 7187504300042129497577393)
        ·
          refine ⟨5390628225031597123183045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7187504300042129497577393 5390628225031597123183045)
          ·
            refine ⟨1010742792193424460596821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5390628225031597123183045 1010742792193424460596821)
            ·
              refine ⟨11844642096016692897619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1010742792193424460596821 11844642096016692897619)
              ·
                rfl

theorem cell22_934228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 8].length) (baseStart_934228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934228 prefixEnd_934228 := by exact prefixLift 934228
  have htrace : WordTrace (prefixWord ++ tailWord_934228) baseStart_934228 baseEnd_934228 := by
    simpa [prefixWord, tailWord_934228, baseEnd_934228] using wordTrace_append hprefix tailTrace_934228
  have hstable : (prefixWord ++ tailWord_934228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934228).length < 2 ^ (prefixWord ++ tailWord_934228).sum := by decide
  have hdescent : baseEnd_934228 < baseStart_934228 := by decide
  rcases family_descends (prefixWord ++ tailWord_934228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934271 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_934271 : Nat := 118140960795 + 934271 * 2 ^ 59
def prefixEnd_934271 : Nat := 4983230072969 + 3 ^ 40 * 934271 * 2
def baseEnd_934271 : Nat := 319820056371212929410581

theorem tailTrace_934271 : CollatzResearch.WordTrace tailWord_934271 prefixEnd_934271 319820056371212929410581 := by
  unfold tailWord_934271
  simp only [CollatzResearch.WordTrace]
  refine ⟨34075662798303202628626667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22717108532202135085751111 34075662798303202628626667)
  ·
    refine ⟨51113494197454803942940001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34075662798303202628626667 51113494197454803942940001)
    ·
      refine ⟨38335120648091102957205001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51113494197454803942940001 38335120648091102957205001)
      ·
        refine ⟨28751340486068327217903751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38335120648091102957205001 28751340486068327217903751)
        ·
          refine ⟨43127010729102490826855627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28751340486068327217903751 43127010729102490826855627)
          ·
            refine ⟨64690516093653736240283441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43127010729102490826855627 64690516093653736240283441)
            ·
              refine ⟨48517887070240302180212581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64690516093653736240283441 48517887070240302180212581)
              ·
                refine ⟨9097103825670056658789859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48517887070240302180212581 9097103825670056658789859)
                ·
                  refine ⟨13645655738505084988184789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097103825670056658789859 13645655738505084988184789)
                  ·
                    refine ⟨319820056371212929410581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13645655738505084988184789 319820056371212929410581)
                    ·
                      rfl

theorem cell22_934271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_934271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934271 prefixEnd_934271 := by exact prefixLift 934271
  have htrace : WordTrace (prefixWord ++ tailWord_934271) baseStart_934271 baseEnd_934271 := by
    simpa [prefixWord, tailWord_934271, baseEnd_934271] using wordTrace_append hprefix tailTrace_934271
  have hstable : (prefixWord ++ tailWord_934271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934271).length < 2 ^ (prefixWord ++ tailWord_934271).sum := by decide
  have hdescent : baseEnd_934271 < baseStart_934271 := by decide
  rcases family_descends (prefixWord ++ tailWord_934271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934303 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 5, 4]
def baseStart_934303 : Nat := 118140960795 + 934303 * 2 ^ 59
def prefixEnd_934303 : Nat := 4983230072969 + 3 ^ 40 * 934303 * 2
def baseEnd_934303 : Nat := 319831010625175512610483

theorem tailTrace_934303 : CollatzResearch.WordTrace tailWord_934303 prefixEnd_934303 319831010625175512610483 := by
  unfold tailWord_934303
  simp only [CollatzResearch.WordTrace]
  refine ⟨34076829934187272093791563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22717886622791514729194375 34076829934187272093791563)
  ·
    refine ⟨51115244901280908140687345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34076829934187272093791563 51115244901280908140687345)
    ·
      refine ⟨38336433675960681105515509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51115244901280908140687345 38336433675960681105515509)
      ·
        refine ⟨3594040657121313853642079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38336433675960681105515509 3594040657121313853642079)
        ·
          refine ⟨5391060985681970780463119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594040657121313853642079 5391060985681970780463119)
          ·
            refine ⟨8086591478522956170694679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391060985681970780463119 8086591478522956170694679)
            ·
              refine ⟨12129887217784434256042019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086591478522956170694679 12129887217784434256042019)
              ·
                refine ⟨18194830826676651384063029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12129887217784434256042019 18194830826676651384063029)
                ·
                  refine ⟨1705765390000936067255909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18194830826676651384063029 1705765390000936067255909)
                  ·
                    refine ⟨319831010625175512610483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1705765390000936067255909 319831010625175512610483)
                    ·
                      rfl

theorem cell22_934303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_934303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934303 prefixEnd_934303 := by exact prefixLift 934303
  have htrace : WordTrace (prefixWord ++ tailWord_934303) baseStart_934303 baseEnd_934303 := by
    simpa [prefixWord, tailWord_934303, baseEnd_934303] using wordTrace_append hprefix tailTrace_934303
  have hstable : (prefixWord ++ tailWord_934303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934303).length < 2 ^ (prefixWord ++ tailWord_934303).sum := by decide
  have hdescent : baseEnd_934303 < baseStart_934303 := by decide
  rcases family_descends (prefixWord ++ tailWord_934303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934386 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_934386 : Nat := 118140960795 + 934386 * 2 ^ 59
def prefixEnd_934386 : Nat := 4983230072969 + 3 ^ 40 * 934386 * 2
def baseEnd_934386 : Nat := 106619807740463654261743

theorem tailTrace_934386 : CollatzResearch.WordTrace tailWord_934386 prefixEnd_934386 106619807740463654261743 := by
  unfold tailWord_934386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8519964298221644317265753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22719904795257718179375341 8519964298221644317265753)
  ·
    refine ⟨6389973223666233237949315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8519964298221644317265753 6389973223666233237949315)
    ·
      refine ⟨9584959835499349856923973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389973223666233237949315 9584959835499349856923973)
      ·
        refine ⟨1797179969156128098173245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9584959835499349856923973 1797179969156128098173245)
        ·
          refine ⟨673942488433548036814967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1797179969156128098173245 673942488433548036814967)
          ·
            refine ⟨1010913732650322055222451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673942488433548036814967 1010913732650322055222451)
            ·
              refine ⟨1516370598975483082833677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010913732650322055222451 1516370598975483082833677)
              ·
                refine ⟨568638974615806156062629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1516370598975483082833677 568638974615806156062629)
                ·
                  refine ⟨106619807740463654261743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568638974615806156062629 106619807740463654261743)
                  ·
                    rfl

theorem cell22_934386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_934386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934386 prefixEnd_934386 := by exact prefixLift 934386
  have htrace : WordTrace (prefixWord ++ tailWord_934386) baseStart_934386 baseEnd_934386 := by
    simpa [prefixWord, tailWord_934386, baseEnd_934386] using wordTrace_append hprefix tailTrace_934386
  have hstable : (prefixWord ++ tailWord_934386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934386).length < 2 ^ (prefixWord ++ tailWord_934386).sum := by decide
  have hdescent : baseEnd_934386 < baseStart_934386 := by decide
  rcases family_descends (prefixWord ++ tailWord_934386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934412 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_934412 : Nat := 118140960795 + 934412 * 2 ^ 59
def prefixEnd_934412 : Nat := 4983230072969 + 3 ^ 40 * 934412 * 2
def baseEnd_934412 : Nat := 319868323552735561635149

theorem tailTrace_934412 : CollatzResearch.WordTrace tailWord_934412 prefixEnd_934412 319868323552735561635149 := by
  unfold tailWord_934412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17040402745396191854754745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22720536993861589139672993 17040402745396191854754745)
  ·
    refine ⟨12780302059047143891066059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17040402745396191854754745 12780302059047143891066059)
    ·
      refine ⟨19170453088570715836599089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12780302059047143891066059 19170453088570715836599089)
      ·
        refine ⟨14377839816428036877449317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19170453088570715836599089 14377839816428036877449317)
        ·
          refine ⟨2695844965580256914521747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14377839816428036877449317 2695844965580256914521747)
          ·
            refine ⟨4043767448370385371782621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695844965580256914521747 4043767448370385371782621)
            ·
              refine ⟨1516412793138894514418483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4043767448370385371782621 1516412793138894514418483)
              ·
                refine ⟨2274619189708341771627725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516412793138894514418483 2274619189708341771627725)
                ·
                  refine ⟨852982196140628164360397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2274619189708341771627725 852982196140628164360397)
                  ·
                    refine ⟨319868323552735561635149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 852982196140628164360397 319868323552735561635149)
                    ·
                      rfl

theorem cell22_934412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_934412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934412 prefixEnd_934412 := by exact prefixLift 934412
  have htrace : WordTrace (prefixWord ++ tailWord_934412) baseStart_934412 baseEnd_934412 := by
    simpa [prefixWord, tailWord_934412, baseEnd_934412] using wordTrace_append hprefix tailTrace_934412
  have hstable : (prefixWord ++ tailWord_934412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934412).length < 2 ^ (prefixWord ++ tailWord_934412).sum := by decide
  have hdescent : baseEnd_934412 < baseStart_934412 := by decide
  rcases family_descends (prefixWord ++ tailWord_934412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934485 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_934485 : Nat := 118140960795 + 934485 * 2 ^ 59
def prefixEnd_934485 : Nat := 4983230072969 + 3 ^ 40 * 934485 * 2
def baseEnd_934485 : Nat := 319893312944587704559925

theorem tailTrace_934485 : CollatzResearch.WordTrace tailWord_934485 prefixEnd_934485 319893312944587704559925 := by
  unfold tailWord_934485
  simp only [CollatzResearch.WordTrace]
  refine ⟨34083468019527917176916909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22722312013018611451277939 34083468019527917176916909)
  ·
    refine ⟨12781300507322968941343841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34083468019527917176916909 12781300507322968941343841)
    ·
      refine ⟨9585975380492226706007881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12781300507322968941343841 9585975380492226706007881)
      ·
        refine ⟨7189481535369170029505911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9585975380492226706007881 7189481535369170029505911)
        ·
          refine ⟨10784222303053755044258867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189481535369170029505911 10784222303053755044258867)
          ·
            refine ⟨16176333454580632566388301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784222303053755044258867 16176333454580632566388301)
            ·
              refine ⟨6066125045467737212395613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16176333454580632566388301 6066125045467737212395613)
              ·
                refine ⟨2274796892050401454648355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6066125045467737212395613 2274796892050401454648355)
                ·
                  refine ⟨3412195338075602181972533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274796892050401454648355 3412195338075602181972533)
                  ·
                    refine ⟨319893312944587704559925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3412195338075602181972533 319893312944587704559925)
                    ·
                      rfl

theorem cell22_934485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_934485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934485 prefixEnd_934485 := by exact prefixLift 934485
  have htrace : WordTrace (prefixWord ++ tailWord_934485) baseStart_934485 baseEnd_934485 := by
    simpa [prefixWord, tailWord_934485, baseEnd_934485] using wordTrace_append hprefix tailTrace_934485
  have hstable : (prefixWord ++ tailWord_934485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934485).length < 2 ^ (prefixWord ++ tailWord_934485).sum := by decide
  have hdescent : baseEnd_934485 < baseStart_934485 := by decide
  rcases family_descends (prefixWord ++ tailWord_934485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934500 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_934500 : Nat := 118140960795 + 934500 * 2 ^ 59
def prefixEnd_934500 : Nat := 4983230072969 + 3 ^ 40 * 934500 * 2
def baseEnd_934500 : Nat := 319898447751132665434879

theorem tailTrace_934500 : CollatzResearch.WordTrace tailWord_934500 prefixEnd_934500 319898447751132665434879 := by
  unfold tailWord_934500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042007557236787369356477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22722676742982383159141969 17042007557236787369356477)
  ·
    refine ⟨6390752833963795263508679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17042007557236787369356477 6390752833963795263508679)
    ·
      refine ⟨9586129250945692895263019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390752833963795263508679 9586129250945692895263019)
      ·
        refine ⟨14379193876418539342894529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586129250945692895263019 14379193876418539342894529)
        ·
          refine ⟨10784395407313904507170897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14379193876418539342894529 10784395407313904507170897)
          ·
            refine ⟨8088296555485428380378173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10784395407313904507170897 8088296555485428380378173)
            ·
              refine ⟨3033111208307035642641815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8088296555485428380378173 3033111208307035642641815)
              ·
                refine ⟨4549666812460553463962723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033111208307035642641815 4549666812460553463962723)
                ·
                  refine ⟨6824500218690830195944085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549666812460553463962723 6824500218690830195944085)
                  ·
                    refine ⟨319898447751132665434879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6824500218690830195944085 319898447751132665434879)
                    ·
                      rfl

theorem cell22_934500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_934500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934500 prefixEnd_934500 := by exact prefixLift 934500
  have htrace : WordTrace (prefixWord ++ tailWord_934500) baseStart_934500 baseEnd_934500 := by
    simpa [prefixWord, tailWord_934500, baseEnd_934500] using wordTrace_append hprefix tailTrace_934500
  have hstable : (prefixWord ++ tailWord_934500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934500).length < 2 ^ (prefixWord ++ tailWord_934500).sum := by decide
  have hdescent : baseEnd_934500 < baseStart_934500 := by decide
  rcases family_descends (prefixWord ++ tailWord_934500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934581 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_934581 : Nat := 118140960795 + 934581 * 2 ^ 59
def prefixEnd_934581 : Nat := 4983230072969 + 3 ^ 40 * 934581 * 2
def baseEnd_934581 : Nat := 319926175706475454159631

theorem tailTrace_934581 : CollatzResearch.WordTrace tailWord_934581 prefixEnd_934581 319926175706475454159631 := by
  unfold tailWord_934581
  simp only [CollatzResearch.WordTrace]
  refine ⟨34086969427180125572411597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22724646284786750381607731 34086969427180125572411597)
  ·
    refine ⟨12782613535192547089654349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34086969427180125572411597 12782613535192547089654349)
    ·
      refine ⟨4793480075697205158620381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12782613535192547089654349 4793480075697205158620381)
      ·
        refine ⟨1797555028386451934482643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4793480075697205158620381 1797555028386451934482643)
        ·
          refine ⟨2696332542579677901723965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797555028386451934482643 2696332542579677901723965)
          ·
            refine ⟨1011124703467379213146487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2696332542579677901723965 1011124703467379213146487)
            ·
              refine ⟨1516687055201068819719731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011124703467379213146487 1516687055201068819719731)
              ·
                refine ⟨2275030582801603229579597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516687055201068819719731 2275030582801603229579597)
                ·
                  refine ⟨853136468550601211092349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2275030582801603229579597 853136468550601211092349)
                  ·
                    refine ⟨319926175706475454159631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853136468550601211092349 319926175706475454159631)
                    ·
                      rfl

theorem cell22_934581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_934581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934581 prefixEnd_934581 := by exact prefixLift 934581
  have htrace : WordTrace (prefixWord ++ tailWord_934581) baseStart_934581 baseEnd_934581 := by
    simpa [prefixWord, tailWord_934581, baseEnd_934581] using wordTrace_append hprefix tailTrace_934581
  have hstable : (prefixWord ++ tailWord_934581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934581).length < 2 ^ (prefixWord ++ tailWord_934581).sum := by decide
  have hdescent : baseEnd_934581 < baseStart_934581 := by decide
  rcases family_descends (prefixWord ++ tailWord_934581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934635 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_934635 : Nat := 118140960795 + 934635 * 2 ^ 59
def prefixEnd_934635 : Nat := 4983230072969 + 3 ^ 40 * 934635 * 2
def baseEnd_934635 : Nat := 319944661010037313309465

theorem tailTrace_934635 : CollatzResearch.WordTrace tailWord_934635 prefixEnd_934635 319944661010037313309465 := by
  unfold tailWord_934635
  simp only [CollatzResearch.WordTrace]
  refine ⟨34088938968984492794877359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22725959312656328529918239 34088938968984492794877359)
  ·
    refine ⟨51133408453476739192316039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34088938968984492794877359 51133408453476739192316039)
    ·
      refine ⟨76700112680215108788474059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51133408453476739192316039 76700112680215108788474059)
      ·
        refine ⟨115050169020322663182711089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76700112680215108788474059 115050169020322663182711089)
        ·
          refine ⟨86287626765241997387033317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115050169020322663182711089 86287626765241997387033317)
          ·
            refine ⟨16178930018482874510068747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86287626765241997387033317 16178930018482874510068747)
            ·
              refine ⟨24268395027724311765103121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16178930018482874510068747 24268395027724311765103121)
              ·
                refine ⟨18201296270793233823827341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24268395027724311765103121 18201296270793233823827341)
                ·
                  refine ⟨6825486101547462683935253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18201296270793233823827341 6825486101547462683935253)
                  ·
                    refine ⟨319944661010037313309465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6825486101547462683935253 319944661010037313309465)
                    ·
                      rfl

theorem cell22_934635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_934635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934635 prefixEnd_934635 := by exact prefixLift 934635
  have htrace : WordTrace (prefixWord ++ tailWord_934635) baseStart_934635 baseEnd_934635 := by
    simpa [prefixWord, tailWord_934635, baseEnd_934635] using wordTrace_append hprefix tailTrace_934635
  have hstable : (prefixWord ++ tailWord_934635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934635).length < 2 ^ (prefixWord ++ tailWord_934635).sum := by decide
  have hdescent : baseEnd_934635 < baseStart_934635 := by decide
  rcases family_descends (prefixWord ++ tailWord_934635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934637 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_934637 : Nat := 118140960795 + 934637 * 2 ^ 59
def prefixEnd_934637 : Nat := 4983230072969 + 3 ^ 40 * 934637 * 2
def baseEnd_934637 : Nat := 319945345650909974759459

theorem tailTrace_934637 : CollatzResearch.WordTrace tailWord_934637 prefixEnd_934637 319945345650909974759459 := by
  unfold tailWord_934637
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089011914977247136450165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22726007943318164757633443 34089011914977247136450165)
  ·
    refine ⟨3195844867029116919042203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34089011914977247136450165 3195844867029116919042203)
    ·
      refine ⟨4793767300543675378563305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3195844867029116919042203 4793767300543675378563305)
      ·
        refine ⟨3595325475407756533922479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4793767300543675378563305 3595325475407756533922479)
        ·
          refine ⟨5392988213111634800883719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595325475407756533922479 5392988213111634800883719)
          ·
            refine ⟨8089482319667452201325579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392988213111634800883719 8089482319667452201325579)
            ·
              refine ⟨12134223479501178301988369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089482319667452201325579 12134223479501178301988369)
              ·
                refine ⟨9100667609625883726491277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12134223479501178301988369 9100667609625883726491277)
                ·
                  refine ⟨3412750353609706397434229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9100667609625883726491277 3412750353609706397434229)
                  ·
                    refine ⟨319945345650909974759459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3412750353609706397434229 319945345650909974759459)
                    ·
                      rfl

theorem cell22_934637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_934637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934637 prefixEnd_934637 := by exact prefixLift 934637
  have htrace : WordTrace (prefixWord ++ tailWord_934637) baseStart_934637 baseEnd_934637 := by
    simpa [prefixWord, tailWord_934637, baseEnd_934637] using wordTrace_append hprefix tailTrace_934637
  have hstable : (prefixWord ++ tailWord_934637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934637).length < 2 ^ (prefixWord ++ tailWord_934637).sum := by decide
  have hdescent : baseEnd_934637 < baseStart_934637 := by decide
  rcases family_descends (prefixWord ++ tailWord_934637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934639 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 4]
def baseStart_934639 : Nat := 118140960795 + 934639 * 2 ^ 59
def prefixEnd_934639 : Nat := 4983230072969 + 3 ^ 40 * 934639 * 2
def baseEnd_934639 : Nat := 106648676763927545403151

theorem tailTrace_934639 : CollatzResearch.WordTrace tailWord_934639 prefixEnd_934639 106648676763927545403151 := by
  unfold tailWord_934639
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089084860970001478022971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22726056573980000985348647 34089084860970001478022971)
  ·
    refine ⟨51133627291455002217034457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34089084860970001478022971 51133627291455002217034457)
    ·
      refine ⟨38350220468591251662775843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51133627291455002217034457 38350220468591251662775843)
      ·
        refine ⟨57525330702886877494163765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38350220468591251662775843 57525330702886877494163765)
        ·
          refine ⟨5392999753395644765077853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57525330702886877494163765 5392999753395644765077853)
          ·
            refine ⟨2022374907523366786904195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5392999753395644765077853 2022374907523366786904195)
            ·
              refine ⟨3033562361285050180356293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022374907523366786904195 3033562361285050180356293)
              ·
                refine ⟨568792942740946908816805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3033562361285050180356293 568792942740946908816805)
                ·
                  refine ⟨106648676763927545403151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568792942740946908816805 106648676763927545403151)
                  ·
                    rfl

theorem cell22_934639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 4].length) (baseStart_934639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934639 prefixEnd_934639 := by exact prefixLift 934639
  have htrace : WordTrace (prefixWord ++ tailWord_934639) baseStart_934639 baseEnd_934639 := by
    simpa [prefixWord, tailWord_934639, baseEnd_934639] using wordTrace_append hprefix tailTrace_934639
  have hstable : (prefixWord ++ tailWord_934639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934639).length < 2 ^ (prefixWord ++ tailWord_934639).sum := by decide
  have hdescent : baseEnd_934639 < baseStart_934639 := by decide
  rcases family_descends (prefixWord ++ tailWord_934639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934654 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_934654 : Nat := 118140960795 + 934654 * 2 ^ 59
def prefixEnd_934654 : Nat := 4983230072969 + 3 ^ 40 * 934654 * 2
def baseEnd_934654 : Nat := 319951165098327597084407

theorem tailTrace_934654 : CollatzResearch.WordTrace tailWord_934654 prefixEnd_934654 319951165098327597084407 := by
  unfold tailWord_934654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261203994489457379977377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22726421303943772693212677 4261203994489457379977377)
  ·
    refine ⟨3195902995867093034983033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4261203994489457379977377 3195902995867093034983033)
    ·
      refine ⟨2396927246900319776237275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3195902995867093034983033 2396927246900319776237275)
      ·
        refine ⟨3595390870350479664355913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396927246900319776237275 3595390870350479664355913)
        ·
          refine ⟨2696543152762859748266935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3595390870350479664355913 2696543152762859748266935)
          ·
            refine ⟨4044814729144289622400403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696543152762859748266935 4044814729144289622400403)
            ·
              refine ⟨6067222093716434433600605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044814729144289622400403 6067222093716434433600605)
              ·
                refine ⟨2275208285143662912600227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6067222093716434433600605 2275208285143662912600227)
                ·
                  refine ⟨3412812427715494368900341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275208285143662912600227 3412812427715494368900341)
                  ·
                    refine ⟨319951165098327597084407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3412812427715494368900341 319951165098327597084407)
                    ·
                      rfl

theorem cell22_934654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_934654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934654 prefixEnd_934654 := by exact prefixLift 934654
  have htrace : WordTrace (prefixWord ++ tailWord_934654) baseStart_934654 baseEnd_934654 := by
    simpa [prefixWord, tailWord_934654, baseEnd_934654] using wordTrace_append hprefix tailTrace_934654
  have hstable : (prefixWord ++ tailWord_934654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934654).length < 2 ^ (prefixWord ++ tailWord_934654).sum := by decide
  have hdescent : baseEnd_934654 < baseStart_934654 := by decide
  rcases family_descends (prefixWord ++ tailWord_934654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934718 : List Nat := [4, 2, 1, 2, 4, 1, 2, 6]
def baseStart_934718 : Nat := 118140960795 + 934718 * 2 ^ 59
def prefixEnd_934718 : Nat := 4983230072969 + 3 ^ 40 * 934718 * 2
def baseEnd_934718 : Nat := 35552563734028084831579

theorem tailTrace_934718 : CollatzResearch.WordTrace tailWord_934718 prefixEnd_934718 35552563734028084831579 := by
  unfold tailWord_934718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261495778460474746268601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22727977485122531980099205 4261495778460474746268601)
  ·
    refine ⟨3196121833845356059701451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4261495778460474746268601 3196121833845356059701451)
    ·
      refine ⟨4794182750768034089552177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196121833845356059701451 4794182750768034089552177)
      ·
        refine ⟨3595637063076025567164133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4794182750768034089552177 3595637063076025567164133)
        ·
          refine ⟨674181949326754793843275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3595637063076025567164133 674181949326754793843275)
          ·
            refine ⟨1011272923990132190764913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674181949326754793843275 1011272923990132190764913)
            ·
              refine ⟨758454692992599143073685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011272923990132190764913 758454692992599143073685)
              ·
                refine ⟨35552563734028084831579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 758454692992599143073685 35552563734028084831579)
                ·
                  rfl

theorem cell22_934718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_934718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934718 prefixEnd_934718 := by exact prefixLift 934718
  have htrace : WordTrace (prefixWord ++ tailWord_934718) baseStart_934718 baseEnd_934718 := by
    simpa [prefixWord, tailWord_934718, baseEnd_934718] using wordTrace_append hprefix tailTrace_934718
  have hstable : (prefixWord ++ tailWord_934718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934718).length < 2 ^ (prefixWord ++ tailWord_934718).sum := by decide
  have hdescent : baseEnd_934718 < baseStart_934718 := by decide
  rcases family_descends (prefixWord ++ tailWord_934718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934789 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_934789 : Nat := 118140960795 + 934789 * 2 ^ 59
def prefixEnd_934789 : Nat := 4983230072969 + 3 ^ 40 * 934789 * 2
def baseEnd_934789 : Nat := 319997378357232244958993

theorem tailTrace_934789 : CollatzResearch.WordTrace tailWord_934789 prefixEnd_934789 319997378357232244958993 := by
  unfold tailWord_934789
  simp only [CollatzResearch.WordTrace]
  refine ⟨34094555810426577095983421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22729703873617718063988947 34094555810426577095983421)
  ·
    refine ⟨12785458428909966410993783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34094555810426577095983421 12785458428909966410993783)
    ·
      refine ⟨19178187643364949616490675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12785458428909966410993783 19178187643364949616490675)
      ·
        refine ⟨28767281465047424424736013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19178187643364949616490675 28767281465047424424736013)
        ·
          refine ⟨10787730549392784159276005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28767281465047424424736013 10787730549392784159276005)
          ·
            refine ⟨2022699478011147029864251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10787730549392784159276005 2022699478011147029864251)
            ·
              refine ⟨3034049217016720544796377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022699478011147029864251 3034049217016720544796377)
              ·
                refine ⟨2275536912762540408597283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034049217016720544796377 2275536912762540408597283)
                ·
                  refine ⟨3413305369143810612895925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275536912762540408597283 3413305369143810612895925)
                  ·
                    refine ⟨319997378357232244958993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3413305369143810612895925 319997378357232244958993)
                    ·
                      rfl

theorem cell22_934789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_934789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934789 prefixEnd_934789 := by exact prefixLift 934789
  have htrace : WordTrace (prefixWord ++ tailWord_934789) baseStart_934789 baseEnd_934789 := by
    simpa [prefixWord, tailWord_934789, baseEnd_934789] using wordTrace_append hprefix tailTrace_934789
  have hstable : (prefixWord ++ tailWord_934789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934789).length < 2 ^ (prefixWord ++ tailWord_934789).sum := by decide
  have hdescent : baseEnd_934789 < baseStart_934789 := by decide
  rcases family_descends (prefixWord ++ tailWord_934789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934868 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_934868 : Nat := 118140960795 + 934868 * 2 ^ 59
def prefixEnd_934868 : Nat := 4983230072969 + 3 ^ 40 * 934868 * 2
def baseEnd_934868 : Nat := 320024421671702372233751

theorem tailTrace_934868 : CollatzResearch.WordTrace tailWord_934868 prefixEnd_934868 320024421671702372233751 := by
  unfold tailWord_934868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048718588570186794054629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22731624784760249058739505 17048718588570186794054629)
  ·
    refine ⟨3196634735356910023885243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17048718588570186794054629 3196634735356910023885243)
    ·
      refine ⟨4794952103035365035827865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196634735356910023885243 4794952103035365035827865)
      ·
        refine ⟨3596214077276523776870899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4794952103035365035827865 3596214077276523776870899)
        ·
          refine ⟨5394321115914785665306349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596214077276523776870899 5394321115914785665306349)
          ·
            refine ⟨2022870418468044624489881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5394321115914785665306349 2022870418468044624489881)
            ·
              refine ⟨1517152813851033468367411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022870418468044624489881 1517152813851033468367411)
              ·
                refine ⟨2275729220776550202551117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517152813851033468367411 2275729220776550202551117)
                ·
                  refine ⟨853398457791206325956669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2275729220776550202551117 853398457791206325956669)
                  ·
                    refine ⟨320024421671702372233751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853398457791206325956669 320024421671702372233751)
                    ·
                      rfl

theorem cell22_934868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_934868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934868 prefixEnd_934868 := by exact prefixLift 934868
  have htrace : WordTrace (prefixWord ++ tailWord_934868) baseStart_934868 baseEnd_934868 := by
    simpa [prefixWord, tailWord_934868, baseEnd_934868] using wordTrace_append hprefix tailTrace_934868
  have hstable : (prefixWord ++ tailWord_934868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934868).length < 2 ^ (prefixWord ++ tailWord_934868).sum := by decide
  have hdescent : baseEnd_934868 < baseStart_934868 := by decide
  rcases family_descends (prefixWord ++ tailWord_934868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934902 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_934902 : Nat := 118140960795 + 934902 * 2 ^ 59
def prefixEnd_934902 : Nat := 4983230072969 + 3 ^ 40 * 934902 * 2
def baseEnd_934902 : Nat := 320036060566537616883647

theorem tailTrace_934902 : CollatzResearch.WordTrace tailWord_934902 prefixEnd_934902 320036060566537616883647 := by
  unfold tailWord_934902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131167328688574837177935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22732451506011464929897973 2131167328688574837177935)
  ·
    refine ⟨3196750993032862255766903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2131167328688574837177935 3196750993032862255766903)
    ·
      refine ⟨4795126489549293383650355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196750993032862255766903 4795126489549293383650355)
      ·
        refine ⟨7192689734323940075475533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795126489549293383650355 7192689734323940075475533)
        ·
          refine ⟨2697258650371477528303325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7192689734323940075475533 2697258650371477528303325)
          ·
            refine ⟨1011471993889304073113747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2697258650371477528303325 1011471993889304073113747)
            ·
              refine ⟨1517207990833956109670621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011471993889304073113747 1517207990833956109670621)
              ·
                refine ⟨568952996562733541126483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517207990833956109670621 568952996562733541126483)
                ·
                  refine ⟨853429494844100311689725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568952996562733541126483 853429494844100311689725)
                  ·
                    refine ⟨320036060566537616883647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853429494844100311689725 320036060566537616883647)
                    ·
                      rfl

theorem cell22_934902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_934902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934902 prefixEnd_934902 := by exact prefixLift 934902
  have htrace : WordTrace (prefixWord ++ tailWord_934902) baseStart_934902 baseEnd_934902 := by
    simpa [prefixWord, tailWord_934902, baseEnd_934902] using wordTrace_append hprefix tailTrace_934902
  have hstable : (prefixWord ++ tailWord_934902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934902).length < 2 ^ (prefixWord ++ tailWord_934902).sum := by decide
  have hdescent : baseEnd_934902 < baseStart_934902 := by decide
  rcases family_descends (prefixWord ++ tailWord_934902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934926 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_934926 : Nat := 118140960795 + 934926 * 2 ^ 59
def prefixEnd_934926 : Nat := 4983230072969 + 3 ^ 40 * 934926 * 2
def baseEnd_934926 : Nat := 106681425419003184761191

theorem tailTrace_934926 : CollatzResearch.WordTrace tailWord_934926 prefixEnd_934926 106681425419003184761191 := by
  unfold tailWord_934926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262444076366281186715079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22733035073953499662480421 4262444076366281186715079)
  ·
    refine ⟨6393666114549421780072619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4262444076366281186715079 6393666114549421780072619)
    ·
      refine ⟨9590499171824132670108929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6393666114549421780072619 9590499171824132670108929)
      ·
        refine ⟨7192874378868099502581697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9590499171824132670108929 7192874378868099502581697)
        ·
          refine ⟨5394655784151074626936273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7192874378868099502581697 5394655784151074626936273)
          ·
            refine ⟨4045991838113305970202205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5394655784151074626936273 4045991838113305970202205)
            ·
              refine ⟨1517246939292489738825827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045991838113305970202205 1517246939292489738825827)
              ·
                refine ⟨2275870408938734608238741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517246939292489738825827 2275870408938734608238741)
                ·
                  refine ⟨106681425419003184761191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2275870408938734608238741 106681425419003184761191)
                  ·
                    rfl

theorem cell22_934926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_934926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934926 prefixEnd_934926 := by exact prefixLift 934926
  have htrace : WordTrace (prefixWord ++ tailWord_934926) baseStart_934926 baseEnd_934926 := by
    simpa [prefixWord, tailWord_934926, baseEnd_934926] using wordTrace_append hprefix tailTrace_934926
  have hstable : (prefixWord ++ tailWord_934926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934926).length < 2 ^ (prefixWord ++ tailWord_934926).sum := by decide
  have hdescent : baseEnd_934926 < baseStart_934926 := by decide
  rcases family_descends (prefixWord ++ tailWord_934926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934956 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_934956 : Nat := 118140960795 + 934956 * 2 ^ 59
def prefixEnd_934956 : Nat := 4983230072969 + 3 ^ 40 * 934956 * 2
def baseEnd_934956 : Nat := 320054545870099476033481

theorem tailTrace_934956 : CollatzResearch.WordTrace tailWord_934956 prefixEnd_934956 320054545870099476033481 := by
  unfold tailWord_934956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17050323400410782308656361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22733764533881043078208481 17050323400410782308656361)
  ·
    refine ⟨12787742550308086731492271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17050323400410782308656361 12787742550308086731492271)
    ·
      refine ⟨19181613825462130097238407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12787742550308086731492271 19181613825462130097238407)
      ·
        refine ⟨28772420738193195145857611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19181613825462130097238407 28772420738193195145857611)
        ·
          refine ⟨43158631107289792718786417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28772420738193195145857611 43158631107289792718786417)
          ·
            refine ⟨32368973330467344539089813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43158631107289792718786417 32368973330467344539089813)
            ·
              refine ⟨1517295624865656775269835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32368973330467344539089813 1517295624865656775269835)
              ·
                refine ⟨2275943437298485162904753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517295624865656775269835 2275943437298485162904753)
                ·
                  refine ⟨1706957577973863872178565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2275943437298485162904753 1706957577973863872178565)
                  ·
                    refine ⟨320054545870099476033481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1706957577973863872178565 320054545870099476033481)
                    ·
                      rfl

theorem cell22_934956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_934956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934956 prefixEnd_934956 := by exact prefixLift 934956
  have htrace : WordTrace (prefixWord ++ tailWord_934956) baseStart_934956 baseEnd_934956 := by
    simpa [prefixWord, tailWord_934956, baseEnd_934956] using wordTrace_append hprefix tailTrace_934956
  have hstable : (prefixWord ++ tailWord_934956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934956).length < 2 ^ (prefixWord ++ tailWord_934956).sum := by decide
  have hdescent : baseEnd_934956 < baseStart_934956 := by decide
  rcases family_descends (prefixWord ++ tailWord_934956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934977 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 4]
def baseStart_934977 : Nat := 118140960795 + 934977 * 2 ^ 59
def prefixEnd_934977 : Nat := 4983230072969 + 3 ^ 40 * 934977 * 2
def baseEnd_934977 : Nat := 106687244866420807086139

theorem tailTrace_934977 : CollatzResearch.WordTrace tailWord_934977 prefixEnd_934977 106687244866420807086139 := by
  unfold tailWord_934977
  simp only [CollatzResearch.WordTrace]
  refine ⟨34101412733745485203827185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22734275155830323469218123 34101412733745485203827185)
  ·
    refine ⟨25576059550309113902870389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34101412733745485203827185 25576059550309113902870389)
    ·
      refine ⟨2397755582841479428394099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25576059550309113902870389 2397755582841479428394099)
      ·
        refine ⟨3596633374262219142591149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397755582841479428394099 3596633374262219142591149)
        ·
          refine ⟨1348737515348332178471681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3596633374262219142591149 1348737515348332178471681)
          ·
            refine ⟨1011553136511249133853761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348737515348332178471681 1011553136511249133853761)
            ·
              refine ⟨758664852383436850390321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011553136511249133853761 758664852383436850390321)
              ·
                refine ⟨568998639287577637792741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758664852383436850390321 568998639287577637792741)
                ·
                  refine ⟨106687244866420807086139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568998639287577637792741 106687244866420807086139)
                  ·
                    rfl

theorem cell22_934977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_934977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934977 prefixEnd_934977 := by exact prefixLift 934977
  have htrace : WordTrace (prefixWord ++ tailWord_934977) baseStart_934977 baseEnd_934977 := by
    simpa [prefixWord, tailWord_934977, baseEnd_934977] using wordTrace_append hprefix tailTrace_934977
  have hstable : (prefixWord ++ tailWord_934977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934977).length < 2 ^ (prefixWord ++ tailWord_934977).sum := by decide
  have hdescent : baseEnd_934977 < baseStart_934977 := by decide
  rcases family_descends (prefixWord ++ tailWord_934977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934984 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_934984 : Nat := 118140960795 + 934984 * 2 ^ 59
def prefixEnd_934984 : Nat := 4983230072969 + 3 ^ 40 * 934984 * 2
def baseEnd_934984 : Nat := 320064130842316736333395

theorem tailTrace_934984 : CollatzResearch.WordTrace tailWord_934984 prefixEnd_934984 320064130842316736333395 := by
  unfold tailWord_934984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17050834022360062699666003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22734445363146750266221337 17050834022360062699666003)
  ·
    refine ⟨25576251033540094049499005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17050834022360062699666003 25576251033540094049499005)
    ·
      refine ⟨9591094137577535268562127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25576251033540094049499005 9591094137577535268562127)
      ·
        refine ⟨14386641206366302902843191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9591094137577535268562127 14386641206366302902843191)
        ·
          refine ⟨21579961809549454354264787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14386641206366302902843191 21579961809549454354264787)
          ·
            refine ⟨32369942714324181531397181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579961809549454354264787 32369942714324181531397181)
            ·
              refine ⟨12138728517871568074273943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32369942714324181531397181 12138728517871568074273943)
              ·
                refine ⟨18208092776807352111410915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12138728517871568074273943 18208092776807352111410915)
                ·
                  refine ⟨27312139165211028167116373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18208092776807352111410915 27312139165211028167116373)
                  ·
                    refine ⟨320064130842316736333395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27312139165211028167116373 320064130842316736333395)
                    ·
                      rfl

theorem cell22_934984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_934984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934984 prefixEnd_934984 := by exact prefixLift 934984
  have htrace : WordTrace (prefixWord ++ tailWord_934984) baseStart_934984 baseEnd_934984 := by
    simpa [prefixWord, tailWord_934984, baseEnd_934984] using wordTrace_append hprefix tailTrace_934984
  have hstable : (prefixWord ++ tailWord_934984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934984).length < 2 ^ (prefixWord ++ tailWord_934984).sum := by decide
  have hdescent : baseEnd_934984 < baseStart_934984 := by decide
  rcases family_descends (prefixWord ++ tailWord_934984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934999 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 9]
def baseStart_934999 : Nat := 118140960795 + 934999 * 2 ^ 59
def prefixEnd_934999 : Nat := 4983230072969 + 3 ^ 40 * 934999 * 2
def baseEnd_934999 : Nat := 106689755216287232402783

theorem tailTrace_934999 : CollatzResearch.WordTrace tailWord_934999 prefixEnd_934999 106689755216287232402783 := by
  unfold tailWord_934999
  simp only [CollatzResearch.WordTrace]
  refine ⟨34102215139665782961128051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22734810093110521974085367 34102215139665782961128051)
  ·
    refine ⟨51153322709498674441692077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34102215139665782961128051 51153322709498674441692077)
    ·
      refine ⟨19182496016062002915634529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51153322709498674441692077 19182496016062002915634529)
      ·
        refine ⟨14386872012046502186725897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19182496016062002915634529 14386872012046502186725897)
        ·
          refine ⟨10790154009034876640044423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14386872012046502186725897 10790154009034876640044423)
          ·
            refine ⟨16185231013552314960066635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790154009034876640044423 16185231013552314960066635)
            ·
              refine ⟨24277846520328472440099953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16185231013552314960066635 24277846520328472440099953)
              ·
                refine ⟨18208384890246354330074965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24277846520328472440099953 18208384890246354330074965)
                ·
                  refine ⟨106689755216287232402783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18208384890246354330074965 106689755216287232402783)
                  ·
                    rfl

theorem cell22_934999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_934999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934999 prefixEnd_934999 := by exact prefixLift 934999
  have htrace : WordTrace (prefixWord ++ tailWord_934999) baseStart_934999 baseEnd_934999 := by
    simpa [prefixWord, tailWord_934999, baseEnd_934999] using wordTrace_append hprefix tailTrace_934999
  have hstable : (prefixWord ++ tailWord_934999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934999).length < 2 ^ (prefixWord ++ tailWord_934999).sum := by decide
  have hdescent : baseEnd_934999 < baseStart_934999 := by decide
  rcases family_descends (prefixWord ++ tailWord_934999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935005 : List Nat := [1, 4, 4, 1, 2, 1, 3, 6]
def baseStart_935005 : Nat := 118140960795 + 935005 * 2 ^ 59
def prefixEnd_935005 : Nat := 4983230072969 + 3 ^ 40 * 935005 * 2
def baseEnd_935005 : Nat := 35563479952386631284259

theorem tailTrace_935005 : CollatzResearch.WordTrace tailWord_935005 prefixEnd_935005 35563479952386631284259 := by
  unfold tailWord_935005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34102433977644045985846469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22734955985096030657230979 34102433977644045985846469)
  ·
    refine ⟨6394206370808258622346213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34102433977644045985846469 6394206370808258622346213)
    ·
      refine ⟨1198913694526548491689915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6394206370808258622346213 1198913694526548491689915)
      ·
        refine ⟨1798370541789822737534873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198913694526548491689915 1798370541789822737534873)
        ·
          refine ⟨1348777906342367053151155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798370541789822737534873 1348777906342367053151155)
          ·
            refine ⟨2023166859513550579726733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348777906342367053151155 2023166859513550579726733)
            ·
              refine ⟨758687572317581467397525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2023166859513550579726733 758687572317581467397525)
              ·
                refine ⟨35563479952386631284259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 758687572317581467397525 35563479952386631284259)
                ·
                  rfl

theorem cell22_935005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 6].length) (baseStart_935005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935005 prefixEnd_935005 := by exact prefixLift 935005
  have htrace : WordTrace (prefixWord ++ tailWord_935005) baseStart_935005 baseEnd_935005 := by
    simpa [prefixWord, tailWord_935005, baseEnd_935005] using wordTrace_append hprefix tailTrace_935005
  have hstable : (prefixWord ++ tailWord_935005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935005).length < 2 ^ (prefixWord ++ tailWord_935005).sum := by decide
  have hdescent : baseEnd_935005 < baseStart_935005 := by decide
  rcases family_descends (prefixWord ++ tailWord_935005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935020 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_935020 : Nat := 118140960795 + 935020 * 2 ^ 59
def prefixEnd_935020 : Nat := 4983230072969 + 3 ^ 40 * 935020 * 2
def baseEnd_935020 : Nat := 320076454378024642433285

theorem tailTrace_935020 : CollatzResearch.WordTrace tailWord_935020 prefixEnd_935020 320076454378024642433285 := by
  unfold tailWord_935020
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051490536294851773821257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22735320715059802365095009 17051490536294851773821257)
  ·
    refine ⟨12788617902221138830365943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17051490536294851773821257 12788617902221138830365943)
    ·
      refine ⟨19182926853331708245548915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788617902221138830365943 19182926853331708245548915)
      ·
        refine ⟨28774390279997562368323373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19182926853331708245548915 28774390279997562368323373)
        ·
          refine ⟨10790396354999085888121265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28774390279997562368323373 10790396354999085888121265)
          ·
            refine ⟨8092797266249314416090949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10790396354999085888121265 8092797266249314416090949)
            ·
              refine ⟨1517399487421746453017053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8092797266249314416090949 1517399487421746453017053)
              ·
                refine ⟨569024807783154919881395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517399487421746453017053 569024807783154919881395)
                ·
                  refine ⟨853537211674732379822093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569024807783154919881395 853537211674732379822093)
                  ·
                    refine ⟨320076454378024642433285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853537211674732379822093 320076454378024642433285)
                    ·
                      rfl

theorem cell22_935020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_935020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935020 prefixEnd_935020 := by exact prefixLift 935020
  have htrace : WordTrace (prefixWord ++ tailWord_935020) baseStart_935020 baseEnd_935020 := by
    simpa [prefixWord, tailWord_935020, baseEnd_935020] using wordTrace_append hprefix tailTrace_935020
  have hstable : (prefixWord ++ tailWord_935020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935020).length < 2 ^ (prefixWord ++ tailWord_935020).sum := by decide
  have hdescent : baseEnd_935020 < baseStart_935020 := by decide
  rcases family_descends (prefixWord ++ tailWord_935020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935063 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 1, 4]
def baseStart_935063 : Nat := 118140960795 + 935063 * 2 ^ 59
def prefixEnd_935063 : Nat := 4983230072969 + 3 ^ 40 * 935063 * 2
def baseEnd_935063 : Nat := 320091174156786863608153

theorem tailTrace_935063 : CollatzResearch.WordTrace tailWord_935063 prefixEnd_935063 320091174156786863608153 := by
  unfold tailWord_935063
  simp only [CollatzResearch.WordTrace]
  refine ⟨34104549411433921891457843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22736366274289281260971895 34104549411433921891457843)
  ·
    refine ⟨51156824117150882837186765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34104549411433921891457843 51156824117150882837186765)
    ·
      refine ⟨19183809043931581063945037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51156824117150882837186765 19183809043931581063945037)
      ·
        refine ⟨7193928391474342898979389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19183809043931581063945037 7193928391474342898979389)
        ·
          refine ⟨2697723146802878587117271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7193928391474342898979389 2697723146802878587117271)
          ·
            refine ⟨4046584720204317880675907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697723146802878587117271 4046584720204317880675907)
            ·
              refine ⟨6069877080306476821013861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046584720204317880675907 6069877080306476821013861)
              ·
                refine ⟨1138101952557464403940099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6069877080306476821013861 1138101952557464403940099)
                ·
                  refine ⟨1707152928836196605910149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138101952557464403940099 1707152928836196605910149)
                  ·
                    refine ⟨320091174156786863608153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1707152928836196605910149 320091174156786863608153)
                    ·
                      rfl

theorem cell22_935063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_935063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935063 prefixEnd_935063 := by exact prefixLift 935063
  have htrace : WordTrace (prefixWord ++ tailWord_935063) baseStart_935063 baseEnd_935063 := by
    simpa [prefixWord, tailWord_935063, baseEnd_935063] using wordTrace_append hprefix tailTrace_935063
  have hstable : (prefixWord ++ tailWord_935063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935063).length < 2 ^ (prefixWord ++ tailWord_935063).sum := by decide
  have hdescent : baseEnd_935063 < baseStart_935063 := by decide
  rcases family_descends (prefixWord ++ tailWord_935063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935091 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 4, 4]
def baseStart_935091 : Nat := 118140960795 + 935091 * 2 ^ 59
def prefixEnd_935091 : Nat := 4983230072969 + 3 ^ 40 * 935091 * 2
def baseEnd_935091 : Nat := 320100759129004123908067

theorem tailTrace_935091 : CollatzResearch.WordTrace tailWord_935091 prefixEnd_935091 320100759129004123908067 := by
  unfold tailWord_935091
  simp only [CollatzResearch.WordTrace]
  refine ⟨34105570655332482673477127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22737047103554988448984751 34105570655332482673477127)
  ·
    refine ⟨51158355982998724010215691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34105570655332482673477127 51158355982998724010215691)
    ·
      refine ⟨76737533974498086015323537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51158355982998724010215691 76737533974498086015323537)
      ·
        refine ⟨57553150480873564511492653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76737533974498086015323537 57553150480873564511492653)
        ·
          refine ⟨21582431430327586691809745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57553150480873564511492653 21582431430327586691809745)
          ·
            refine ⟨16186823572745690018857309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21582431430327586691809745 16186823572745690018857309)
            ·
              refine ⟨6070058839779633757071491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16186823572745690018857309 6070058839779633757071491)
              ·
                refine ⟨9105088259669450635607237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6070058839779633757071491 9105088259669450635607237)
                ·
                  refine ⟨1707204048688021994176357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9105088259669450635607237 1707204048688021994176357)
                  ·
                    refine ⟨320100759129004123908067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1707204048688021994176357 320100759129004123908067)
                    ·
                      rfl

theorem cell22_935091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_935091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935091 prefixEnd_935091 := by exact prefixLift 935091
  have htrace : WordTrace (prefixWord ++ tailWord_935091) baseStart_935091 baseEnd_935091 := by
    simpa [prefixWord, tailWord_935091, baseEnd_935091] using wordTrace_append hprefix tailTrace_935091
  have hstable : (prefixWord ++ tailWord_935091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935091).length < 2 ^ (prefixWord ++ tailWord_935091).sum := by decide
  have hdescent : baseEnd_935091 < baseStart_935091 := by decide
  rcases family_descends (prefixWord ++ tailWord_935091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935095 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 4]
def baseStart_935095 : Nat := 118140960795 + 935095 * 2 ^ 59
def prefixEnd_935095 : Nat := 4983230072969 + 3 ^ 40 * 935095 * 2
def baseEnd_935095 : Nat := 106700709470249815602685

theorem tailTrace_935095 : CollatzResearch.WordTrace tailWord_935095 prefixEnd_935095 106700709470249815602685 := by
  unfold tailWord_935095
  simp only [CollatzResearch.WordTrace]
  refine ⟨34105716547317991356622739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22737144364878660904415159 34105716547317991356622739)
  ·
    refine ⟨51158574820976987034934109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34105716547317991356622739 51158574820976987034934109)
    ·
      refine ⟨19184465557866370138100291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51158574820976987034934109 19184465557866370138100291)
      ·
        refine ⟨28776698336799555207150437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19184465557866370138100291 28776698336799555207150437)
        ·
          refine ⟨5395630938149916601340707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28776698336799555207150437 5395630938149916601340707)
          ·
            refine ⟨8093446407224874902011061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395630938149916601340707 8093446407224874902011061)
            ·
              refine ⟨758760600677332022063537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8093446407224874902011061 758760600677332022063537)
              ·
                refine ⟨569070450507999016547653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758760600677332022063537 569070450507999016547653)
                ·
                  refine ⟨106700709470249815602685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569070450507999016547653 106700709470249815602685)
                  ·
                    rfl

theorem cell22_935095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 4].length) (baseStart_935095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935095 prefixEnd_935095 := by exact prefixLift 935095
  have htrace : WordTrace (prefixWord ++ tailWord_935095) baseStart_935095 baseEnd_935095 := by
    simpa [prefixWord, tailWord_935095, baseEnd_935095] using wordTrace_append hprefix tailTrace_935095
  have hstable : (prefixWord ++ tailWord_935095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935095).length < 2 ^ (prefixWord ++ tailWord_935095).sum := by decide
  have hdescent : baseEnd_935095 < baseStart_935095 := by decide
  rcases family_descends (prefixWord ++ tailWord_935095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935125 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_935125 : Nat := 118140960795 + 935125 * 2 ^ 59
def prefixEnd_935125 : Nat := 4983230072969 + 3 ^ 40 * 935125 * 2
def baseEnd_935125 : Nat := 320112398023839368557963

theorem tailTrace_935125 : CollatzResearch.WordTrace tailWord_935125 prefixEnd_935125 320112398023839368557963 := by
  unfold tailWord_935125
  simp only [CollatzResearch.WordTrace]
  refine ⟨34106810737209306480214829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22737873824806204320143219 34106810737209306480214829)
  ·
    refine ⟨12790054026453489930080561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34106810737209306480214829 12790054026453489930080561)
    ·
      refine ⟨9592540519840117447560421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12790054026453489930080561 9592540519840117447560421)
      ·
        refine ⟨1798601347470022021417579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9592540519840117447560421 1798601347470022021417579)
        ·
          refine ⟨2697902021205033032126369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798601347470022021417579 2697902021205033032126369)
          ·
            refine ⟨2023426515903774774094777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697902021205033032126369 2023426515903774774094777)
            ·
              refine ⟨1517569886927831080571083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023426515903774774094777 1517569886927831080571083)
              ·
                refine ⟨2276354830391746620856625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517569886927831080571083 2276354830391746620856625)
                ·
                  refine ⟨1707266122793809965642469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2276354830391746620856625 1707266122793809965642469)
                  ·
                    refine ⟨320112398023839368557963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1707266122793809965642469 320112398023839368557963)
                    ·
                      rfl

theorem cell22_935125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_935125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935125 prefixEnd_935125 := by exact prefixLift 935125
  have htrace : WordTrace (prefixWord ++ tailWord_935125) baseStart_935125 baseEnd_935125 := by
    simpa [prefixWord, tailWord_935125, baseEnd_935125] using wordTrace_append hprefix tailTrace_935125
  have hstable : (prefixWord ++ tailWord_935125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935125).length < 2 ^ (prefixWord ++ tailWord_935125).sum := by decide
  have hdescent : baseEnd_935125 < baseStart_935125 := by decide
  rcases family_descends (prefixWord ++ tailWord_935125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935202 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_935202 : Nat := 118140960795 + 935202 * 2 ^ 59
def prefixEnd_935202 : Nat := 4983230072969 + 3 ^ 40 * 935202 * 2
def baseEnd_935202 : Nat := 106712918899145611460909

theorem tailTrace_935202 : CollatzResearch.WordTrace tailWord_935202 prefixEnd_935202 106712918899145611460909 := by
  unfold tailWord_935202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8527404789482587157691965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22739746105286899087178573 8527404789482587157691965)
  ·
    refine ⟨3197776796055970184134487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8527404789482587157691965 3197776796055970184134487)
    ·
      refine ⟨4796665194083955276201731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197776796055970184134487 4796665194083955276201731)
      ·
        refine ⟨7194997791125932914302597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796665194083955276201731 7194997791125932914302597)
        ·
          refine ⟨1349062085836112421431737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7194997791125932914302597 1349062085836112421431737)
          ·
            refine ⟨1011796564377084316073803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1349062085836112421431737 1011796564377084316073803)
            ·
              refine ⟨1517694846565626474110705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011796564377084316073803 1517694846565626474110705)
              ·
                refine ⟨1138271134924219855583029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517694846565626474110705 1138271134924219855583029)
                ·
                  refine ⟨106712918899145611460909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138271134924219855583029 106712918899145611460909)
                  ·
                    rfl

theorem cell22_935202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_935202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935202 prefixEnd_935202 := by exact prefixLift 935202
  have htrace : WordTrace (prefixWord ++ tailWord_935202) baseStart_935202 baseEnd_935202 := by
    simpa [prefixWord, tailWord_935202, baseEnd_935202] using wordTrace_append hprefix tailTrace_935202
  have hstable : (prefixWord ++ tailWord_935202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935202).length < 2 ^ (prefixWord ++ tailWord_935202).sum := by decide
  have hdescent : baseEnd_935202 < baseStart_935202 := by decide
  rcases family_descends (prefixWord ++ tailWord_935202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935307 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 1, 3]
def baseStart_935307 : Nat := 118140960795 + 935307 * 2 ^ 59
def prefixEnd_935307 : Nat := 4983230072969 + 3 ^ 40 * 935307 * 2
def baseEnd_935307 : Nat := 320174700343251560507405

theorem tailTrace_935307 : CollatzResearch.WordTrace tailWord_935307 prefixEnd_935307 320174700343251560507405 := by
  unfold tailWord_935307
  simp only [CollatzResearch.WordTrace]
  refine ⟨34113448822549951563340175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22742299215033301042226783 34113448822549951563340175)
  ·
    refine ⟨51170173233824927345010263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34113448822549951563340175 51170173233824927345010263)
    ·
      refine ⟨76755259850737391017515395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51170173233824927345010263 76755259850737391017515395)
      ·
        refine ⟨115132889776106086526273093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76755259850737391017515395 115132889776106086526273093)
        ·
          refine ⟨21587416833019891223676205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115132889776106086526273093 21587416833019891223676205)
          ·
            refine ⟨8095281312382459208878577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21587416833019891223676205 8095281312382459208878577)
            ·
              refine ⟨6071460984286844406658933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8095281312382459208878577 6071460984286844406658933)
              ·
                refine ⟨569199467276891663124275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6071460984286844406658933 569199467276891663124275)
                ·
                  refine ⟨853799200915337494686413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569199467276891663124275 853799200915337494686413)
                  ·
                    refine ⟨320174700343251560507405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853799200915337494686413 320174700343251560507405)
                    ·
                      rfl

theorem cell22_935307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 3].length) (baseStart_935307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935307 prefixEnd_935307 := by exact prefixLift 935307
  have htrace : WordTrace (prefixWord ++ tailWord_935307) baseStart_935307 baseEnd_935307 := by
    simpa [prefixWord, tailWord_935307, baseEnd_935307] using wordTrace_append hprefix tailTrace_935307
  have hstable : (prefixWord ++ tailWord_935307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935307).length < 2 ^ (prefixWord ++ tailWord_935307).sum := by decide
  have hdescent : baseEnd_935307 < baseStart_935307 := by decide
  rcases family_descends (prefixWord ++ tailWord_935307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935335 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 2, 5]
def baseStart_935335 : Nat := 118140960795 + 935335 * 2 ^ 59
def prefixEnd_935335 : Nat := 4983230072969 + 3 ^ 40 * 935335 * 2
def baseEnd_935335 : Nat := 320184285315468820807319

theorem tailTrace_935335 : CollatzResearch.WordTrace tailWord_935335 prefixEnd_935335 320184285315468820807319 := by
  unfold tailWord_935335
  simp only [CollatzResearch.WordTrace]
  refine ⟨34114470066448512345359459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22742980044299008230239639 34114470066448512345359459)
  ·
    refine ⟨51171705099672768518039189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34114470066448512345359459 51171705099672768518039189)
    ·
      refine ⟨2398673676547161024283087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51171705099672768518039189 2398673676547161024283087)
      ·
        refine ⟨3598010514820741536424631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398673676547161024283087 3598010514820741536424631)
        ·
          refine ⟨5397015772231112304636947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598010514820741536424631 5397015772231112304636947)
          ·
            refine ⟨8095523658346668456955421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397015772231112304636947 8095523658346668456955421)
            ·
              refine ⟨3035821371880000671358283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8095523658346668456955421 3035821371880000671358283)
              ·
                refine ⟨4553732057820001007037425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035821371880000671358283 4553732057820001007037425)
                ·
                  refine ⟨3415299043365000755278069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553732057820001007037425 3415299043365000755278069)
                  ·
                    refine ⟨320184285315468820807319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3415299043365000755278069 320184285315468820807319)
                    ·
                      rfl

theorem cell22_935335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_935335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935335 prefixEnd_935335 := by exact prefixLift 935335
  have htrace : WordTrace (prefixWord ++ tailWord_935335) baseStart_935335 baseEnd_935335 := by
    simpa [prefixWord, tailWord_935335, baseEnd_935335] using wordTrace_append hprefix tailTrace_935335
  have hstable : (prefixWord ++ tailWord_935335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935335).length < 2 ^ (prefixWord ++ tailWord_935335).sum := by decide
  have hdescent : baseEnd_935335 < baseStart_935335 := by decide
  rcases family_descends (prefixWord ++ tailWord_935335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935382 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_935382 : Nat := 118140960795 + 935382 * 2 ^ 59
def prefixEnd_935382 : Nat := 4983230072969 + 3 ^ 40 * 935382 * 2
def baseEnd_935382 : Nat := 106733458125325454960725

theorem tailTrace_935382 : CollatzResearch.WordTrace tailWord_935382 prefixEnd_935382 106733458125325454960725 := by
  unfold tailWord_935382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132261518579889960770025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22744122864852159581546933 2132261518579889960770025)
  ·
    refine ⟨1599196138934917470577519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2132261518579889960770025 1599196138934917470577519)
    ·
      refine ⟨2398794208402376205866279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599196138934917470577519 2398794208402376205866279)
      ·
        refine ⟨3598191312603564308799419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398794208402376205866279 3598191312603564308799419)
        ·
          refine ⟨5397286968905346463199129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598191312603564308799419 5397286968905346463199129)
          ·
            refine ⟨4047965226679009847399347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397286968905346463199129 4047965226679009847399347)
            ·
              refine ⟨6071947840018514771099021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047965226679009847399347 6071947840018514771099021)
              ·
                refine ⟨2276980440006943039162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6071947840018514771099021 2276980440006943039162133)
                ·
                  refine ⟨106733458125325454960725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2276980440006943039162133 106733458125325454960725)
                  ·
                    rfl

theorem cell22_935382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_935382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935382 prefixEnd_935382 := by exact prefixLift 935382
  have htrace : WordTrace (prefixWord ++ tailWord_935382) baseStart_935382 baseEnd_935382 := by
    simpa [prefixWord, tailWord_935382, baseEnd_935382] using wordTrace_append hprefix tailTrace_935382
  have hstable : (prefixWord ++ tailWord_935382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935382).length < 2 ^ (prefixWord ++ tailWord_935382).sum := by decide
  have hdescent : baseEnd_935382 < baseStart_935382 := by decide
  rcases family_descends (prefixWord ++ tailWord_935382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935395 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 1, 6]
def baseStart_935395 : Nat := 118140960795 + 935395 * 2 ^ 59
def prefixEnd_935395 : Nat := 4983230072969 + 3 ^ 40 * 935395 * 2
def baseEnd_935395 : Nat := 320204824541648664307135

theorem tailTrace_935395 : CollatzResearch.WordTrace tailWord_935395 prefixEnd_935395 320204824541648664307135 := by
  unfold tailWord_935395
  simp only [CollatzResearch.WordTrace]
  refine ⟨34116658446231142592543639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22744438964154095061695759 34116658446231142592543639)
  ·
    refine ⟨51174987669346713888815459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34116658446231142592543639 51174987669346713888815459)
    ·
      refine ⟨76762481504020070833223189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51174987669346713888815459 76762481504020070833223189)
      ·
        refine ⟨3598241320500940820307337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76762481504020070833223189 3598241320500940820307337)
        ·
          refine ⟨2698680990375705615230503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598241320500940820307337 2698680990375705615230503)
          ·
            refine ⟨4048021485563558422845755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698680990375705615230503 4048021485563558422845755)
            ·
              refine ⟨6072032228345337634268633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048021485563558422845755 6072032228345337634268633)
              ·
                refine ⟨4554024171259003225701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072032228345337634268633 4554024171259003225701475)
                ·
                  refine ⟨6831036256888504838552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554024171259003225701475 6831036256888504838552213)
                  ·
                    refine ⟨320204824541648664307135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6831036256888504838552213 320204824541648664307135)
                    ·
                      rfl

theorem cell22_935395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_935395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935395 prefixEnd_935395 := by exact prefixLift 935395
  have htrace : WordTrace (prefixWord ++ tailWord_935395) baseStart_935395 baseEnd_935395 := by
    simpa [prefixWord, tailWord_935395, baseEnd_935395] using wordTrace_append hprefix tailTrace_935395
  have hstable : (prefixWord ++ tailWord_935395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935395).length < 2 ^ (prefixWord ++ tailWord_935395).sum := by decide
  have hdescent : baseEnd_935395 < baseStart_935395 := by decide
  rcases family_descends (prefixWord ++ tailWord_935395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935397 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_935397 : Nat := 118140960795 + 935397 * 2 ^ 59
def prefixEnd_935397 : Nat := 4983230072969 + 3 ^ 40 * 935397 * 2
def baseEnd_935397 : Nat := 320205509182521325757129

theorem tailTrace_935397 : CollatzResearch.WordTrace tailWord_935397 prefixEnd_935397 320205509182521325757129 := by
  unfold tailWord_935397
  simp only [CollatzResearch.WordTrace]
  refine ⟨34116731392223896934116445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22744487594815931289410963 34116731392223896934116445)
  ·
    refine ⟨12793774272083961350293667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34116731392223896934116445 12793774272083961350293667)
    ·
      refine ⟨19190661408125942025440501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12793774272083961350293667 19190661408125942025440501)
      ·
        refine ⟨1799124507011807064885047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19190661408125942025440501 1799124507011807064885047)
        ·
          refine ⟨2698686760517710597327571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799124507011807064885047 2698686760517710597327571)
          ·
            refine ⟨4048030140776565895991357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698686760517710597327571 4048030140776565895991357)
            ·
              refine ⟨1518011302791212210996759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4048030140776565895991357 1518011302791212210996759)
              ·
                refine ⟨2277016954186818316495139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518011302791212210996759 2277016954186818316495139)
                ·
                  refine ⟨3415525431280227474742709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277016954186818316495139 3415525431280227474742709)
                  ·
                    refine ⟨320205509182521325757129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3415525431280227474742709 320205509182521325757129)
                    ·
                      rfl

theorem cell22_935397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_935397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935397 prefixEnd_935397 := by exact prefixLift 935397
  have htrace : WordTrace (prefixWord ++ tailWord_935397) baseStart_935397 baseEnd_935397 := by
    simpa [prefixWord, tailWord_935397, baseEnd_935397] using wordTrace_append hprefix tailTrace_935397
  have hstable : (prefixWord ++ tailWord_935397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935397).length < 2 ^ (prefixWord ++ tailWord_935397).sum := by decide
  have hdescent : baseEnd_935397 < baseStart_935397 := by decide
  rcases family_descends (prefixWord ++ tailWord_935397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935444 : List Nat := [2, 4, 3, 1, 2, 1, 2, 7]
def baseStart_935444 : Nat := 118140960795 + 935444 * 2 ^ 59
def prefixEnd_935444 : Nat := 4983230072969 + 3 ^ 40 * 935444 * 2
def baseEnd_935444 : Nat := 35580177582558763314665

theorem tailTrace_935444 : CollatzResearch.WordTrace tailWord_935444 prefixEnd_935444 35580177582558763314665 := by
  unfold tailWord_935444
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059222811526811980538693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22745630415369082640718257 17059222811526811980538693)
  ·
    refine ⟨3198604277161277246351005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17059222811526811980538693 3198604277161277246351005)
    ·
      refine ⟨1199476603935478967381627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3198604277161277246351005 1199476603935478967381627)
      ·
        refine ⟨1799214905903218451072441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199476603935478967381627 1799214905903218451072441)
        ·
          refine ⟨1349411179427413838304331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799214905903218451072441 1349411179427413838304331)
          ·
            refine ⟨2024116769141120757456497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349411179427413838304331 2024116769141120757456497)
            ·
              refine ⟨1518087576855840568092373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024116769141120757456497 1518087576855840568092373)
              ·
                refine ⟨35580177582558763314665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1518087576855840568092373 35580177582558763314665)
                ·
                  rfl

theorem cell22_935444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_935444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935444 prefixEnd_935444 := by exact prefixLift 935444
  have htrace : WordTrace (prefixWord ++ tailWord_935444) baseStart_935444 baseEnd_935444 := by
    simpa [prefixWord, tailWord_935444, baseEnd_935444] using wordTrace_append hprefix tailTrace_935444
  have hstable : (prefixWord ++ tailWord_935444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935444).length < 2 ^ (prefixWord ++ tailWord_935444).sum := by decide
  have hdescent : baseEnd_935444 < baseStart_935444 := by decide
  rcases family_descends (prefixWord ++ tailWord_935444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935448 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 2, 3]
def baseStart_935448 : Nat := 118140960795 + 935448 * 2 ^ 59
def prefixEnd_935448 : Nat := 4983230072969 + 3 ^ 40 * 935448 * 2
def baseEnd_935448 : Nat := 320222967524774192731973

theorem tailTrace_935448 : CollatzResearch.WordTrace tailWord_935448 prefixEnd_935448 320222967524774192731973 := by
  unfold tailWord_935448
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059295757519566322111499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22745727676692755096148665 17059295757519566322111499)
  ·
    refine ⟨25588943636279349483167249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17059295757519566322111499 25588943636279349483167249)
    ·
      refine ⟨19191707727209512112375437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25588943636279349483167249 19191707727209512112375437)
      ·
        refine ⟨7196890397703567042140789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19191707727209512112375437 7196890397703567042140789)
        ·
          refine ⟨674708474784709410200699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7196890397703567042140789 674708474784709410200699)
          ·
            refine ⟨1012062712177064115301049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674708474784709410200699 1012062712177064115301049)
            ·
              refine ⟨759047034132798086475787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012062712177064115301049 759047034132798086475787)
              ·
                refine ⟨1138570551199197129713681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759047034132798086475787 1138570551199197129713681)
                ·
                  refine ⟨853927913399397847285261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1138570551199197129713681 853927913399397847285261)
                  ·
                    refine ⟨320222967524774192731973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853927913399397847285261 320222967524774192731973)
                    ·
                      rfl

theorem cell22_935448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_935448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935448 prefixEnd_935448 := by exact prefixLift 935448
  have htrace : WordTrace (prefixWord ++ tailWord_935448) baseStart_935448 baseEnd_935448 := by
    simpa [prefixWord, tailWord_935448, baseEnd_935448] using wordTrace_append hprefix tailTrace_935448
  have hstable : (prefixWord ++ tailWord_935448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935448).length < 2 ^ (prefixWord ++ tailWord_935448).sum := by decide
  have hdescent : baseEnd_935448 < baseStart_935448 := by decide
  rcases family_descends (prefixWord ++ tailWord_935448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935532 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_935532 : Nat := 118140960795 + 935532 * 2 ^ 59
def prefixEnd_935532 : Nat := 4983230072969 + 3 ^ 40 * 935532 * 2
def baseEnd_935532 : Nat := 320251722441425973631715

theorem tailTrace_935532 : CollatzResearch.WordTrace tailWord_935532 prefixEnd_935532 320251722441425973631715 := by
  unfold tailWord_935532
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060827623367407495140425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22747770164489876660187233 17060827623367407495140425)
  ·
    refine ⟨12795620717525555621355319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17060827623367407495140425 12795620717525555621355319)
    ·
      refine ⟨19193431076288333432032979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12795620717525555621355319 19193431076288333432032979)
      ·
        refine ⟨28790146614432500148049469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19193431076288333432032979 28790146614432500148049469)
        ·
          refine ⟨10796304980412187555518551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28790146614432500148049469 10796304980412187555518551)
          ·
            refine ⟨16194457470618281333277827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10796304980412187555518551 16194457470618281333277827)
            ·
              refine ⟨24291686205927421999916741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16194457470618281333277827 24291686205927421999916741)
              ·
                refine ⟨4554691163611391624984389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24291686205927421999916741 4554691163611391624984389)
                ·
                  refine ⟨854004593177135929684573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4554691163611391624984389 854004593177135929684573)
                  ·
                    refine ⟨320251722441425973631715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854004593177135929684573 320251722441425973631715)
                    ·
                      rfl

theorem cell22_935532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_935532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935532 prefixEnd_935532 := by exact prefixLift 935532
  have htrace : WordTrace (prefixWord ++ tailWord_935532) baseStart_935532 baseEnd_935532 := by
    simpa [prefixWord, tailWord_935532, baseEnd_935532] using wordTrace_append hprefix tailTrace_935532
  have hstable : (prefixWord ++ tailWord_935532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935532).length < 2 ^ (prefixWord ++ tailWord_935532).sum := by decide
  have hdescent : baseEnd_935532 < baseStart_935532 := by decide
  rcases family_descends (prefixWord ++ tailWord_935532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935536 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 1, 4]
def baseStart_935536 : Nat := 118140960795 + 935536 * 2 ^ 59
def prefixEnd_935536 : Nat := 4983230072969 + 3 ^ 40 * 935536 * 2
def baseEnd_935536 : Nat := 320253091723171296531703

theorem tailTrace_935536 : CollatzResearch.WordTrace tailWord_935536 prefixEnd_935536 320253091723171296531703 := by
  unfold tailWord_935536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17060900569360161836713231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22747867425813549115617641 17060900569360161836713231)
  ·
    refine ⟨25591350854040242755069847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17060900569360161836713231 25591350854040242755069847)
    ·
      refine ⟨38387026281060364132604771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25591350854040242755069847 38387026281060364132604771)
      ·
        refine ⟨57580539421590546198907157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38387026281060364132604771 57580539421590546198907157)
        ·
          refine ⟨2699087785387056853073773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57580539421590546198907157 2699087785387056853073773)
          ·
            refine ⟨1012157919520146319902665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2699087785387056853073773 1012157919520146319902665)
            ·
              refine ⟨759118439640109739926999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012157919520146319902665 759118439640109739926999)
              ·
                refine ⟨1138677659460164609890499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759118439640109739926999 1138677659460164609890499)
                ·
                  refine ⟨1708016489190246914835749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138677659460164609890499 1708016489190246914835749)
                  ·
                    refine ⟨320253091723171296531703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1708016489190246914835749 320253091723171296531703)
                    ·
                      rfl

theorem cell22_935536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_935536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935536 prefixEnd_935536 := by exact prefixLift 935536
  have htrace : WordTrace (prefixWord ++ tailWord_935536) baseStart_935536 baseEnd_935536 := by
    simpa [prefixWord, tailWord_935536, baseEnd_935536] using wordTrace_append hprefix tailTrace_935536
  have hstable : (prefixWord ++ tailWord_935536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935536).length < 2 ^ (prefixWord ++ tailWord_935536).sum := by decide
  have hdescent : baseEnd_935536 < baseStart_935536 := by decide
  rcases family_descends (prefixWord ++ tailWord_935536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935545 : List Nat := [1, 2, 1, 3, 3, 1, 11]
def baseStart_935545 : Nat := 118140960795 + 935545 * 2 ^ 59
def prefixEnd_935545 : Nat := 4983230072969 + 3 ^ 40 * 935545 * 2
def baseEnd_935545 : Nat := 11861339726188824928025

theorem tailTrace_935545 : CollatzResearch.WordTrace tailWord_935545 prefixEnd_935545 11861339726188824928025 := by
  unfold tailWord_935545
  simp only [CollatzResearch.WordTrace]
  refine ⟨34122129395687718210504089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22748086263791812140336059 34122129395687718210504089)
  ·
    refine ⟨25591597046765788657878067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34122129395687718210504089 25591597046765788657878067)
    ·
      refine ⟨38387395570148682986817101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25591597046765788657878067 38387395570148682986817101)
      ·
        refine ⟨14395273338805756120056413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38387395570148682986817101 14395273338805756120056413)
        ·
          refine ⟨5398227502052158545021155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14395273338805756120056413 5398227502052158545021155)
          ·
            refine ⟨8097341253078237817531733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398227502052158545021155 8097341253078237817531733)
            ·
              refine ⟨11861339726188824928025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8097341253078237817531733 11861339726188824928025)
              ·
                rfl

theorem cell22_935545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 11].length) (baseStart_935545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935545 prefixEnd_935545 := by exact prefixLift 935545
  have htrace : WordTrace (prefixWord ++ tailWord_935545) baseStart_935545 baseEnd_935545 := by
    simpa [prefixWord, tailWord_935545, baseEnd_935545] using wordTrace_append hprefix tailTrace_935545
  have hstable : (prefixWord ++ tailWord_935545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935545).length < 2 ^ (prefixWord ++ tailWord_935545).sum := by decide
  have hdescent : baseEnd_935545 < baseStart_935545 := by decide
  rcases family_descends (prefixWord ++ tailWord_935545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935549 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_935549 : Nat := 118140960795 + 935549 * 2 ^ 59
def prefixEnd_935549 : Nat := 4983230072969 + 3 ^ 40 * 935549 * 2
def baseEnd_935549 : Nat := 320257541888843595956663

theorem tailTrace_935549 : CollatzResearch.WordTrace tailWord_935549 prefixEnd_935549 320257541888843595956663 := by
  unfold tailWord_935549
  simp only [CollatzResearch.WordTrace]
  refine ⟨34122275287673226893649701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22748183525115484595766467 34122275287673226893649701)
  ·
    refine ⟨6397926616438730042559319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34122275287673226893649701 6397926616438730042559319)
    ·
      refine ⟨9596889924658095063838979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397926616438730042559319 9596889924658095063838979)
      ·
        refine ⟨14395334886987142595758469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596889924658095063838979 14395334886987142595758469)
        ·
          refine ⟨2699125291310089236704713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14395334886987142595758469 2699125291310089236704713)
          ·
            refine ⟨2024343968482566927528535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2699125291310089236704713 2024343968482566927528535)
            ·
              refine ⟨3036515952723850391292803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024343968482566927528535 3036515952723850391292803)
              ·
                refine ⟨4554773929085775586939205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036515952723850391292803 4554773929085775586939205)
                ·
                  refine ⟨854020111703582922551101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4554773929085775586939205 854020111703582922551101)
                  ·
                    refine ⟨320257541888843595956663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854020111703582922551101 320257541888843595956663)
                    ·
                      rfl

theorem cell22_935549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_935549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935549 prefixEnd_935549 := by exact prefixLift 935549
  have htrace : WordTrace (prefixWord ++ tailWord_935549) baseStart_935549 baseEnd_935549 := by
    simpa [prefixWord, tailWord_935549, baseEnd_935549] using wordTrace_append hprefix tailTrace_935549
  have hstable : (prefixWord ++ tailWord_935549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935549).length < 2 ^ (prefixWord ++ tailWord_935549).sum := by decide
  have hdescent : baseEnd_935549 < baseStart_935549 := by decide
  rcases family_descends (prefixWord ++ tailWord_935549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935577 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_935577 : Nat := 118140960795 + 935577 * 2 ^ 59
def prefixEnd_935577 : Nat := 4983230072969 + 3 ^ 40 * 935577 * 2
def baseEnd_935577 : Nat := 320267126861060856256577

theorem tailTrace_935577 : CollatzResearch.WordTrace tailWord_935577 prefixEnd_935577 320267126861060856256577 := by
  unfold tailWord_935577
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123296531571787675668985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22748864354381191783779323 34123296531571787675668985)
  ·
    refine ⟨25592472398678840756751739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34123296531571787675668985 25592472398678840756751739)
    ·
      refine ⟨38388708598018261135127609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25592472398678840756751739 38388708598018261135127609)
      ·
        refine ⟨28791531448513695851345707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38388708598018261135127609 28791531448513695851345707)
        ·
          refine ⟨43187297172770543777018561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28791531448513695851345707 43187297172770543777018561)
          ·
            refine ⟨32390472879577907832763921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43187297172770543777018561 32390472879577907832763921)
            ·
              refine ⟨24292854659683430874572941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32390472879577907832763921 24292854659683430874572941)
              ·
                refine ⟨9109820497381286577964853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24292854659683430874572941 9109820497381286577964853)
                ·
                  refine ⟨854045671629495616684205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9109820497381286577964853 854045671629495616684205)
                  ·
                    refine ⟨320267126861060856256577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854045671629495616684205 320267126861060856256577)
                    ·
                      rfl

theorem cell22_935577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_935577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935577 prefixEnd_935577 := by exact prefixLift 935577
  have htrace : WordTrace (prefixWord ++ tailWord_935577) baseStart_935577 baseEnd_935577 := by
    simpa [prefixWord, tailWord_935577, baseEnd_935577] using wordTrace_append hprefix tailTrace_935577
  have hstable : (prefixWord ++ tailWord_935577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935577).length < 2 ^ (prefixWord ++ tailWord_935577).sum := by decide
  have hdescent : baseEnd_935577 < baseStart_935577 := by decide
  rcases family_descends (prefixWord ++ tailWord_935577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935607 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 7]
def baseStart_935607 : Nat := 118140960795 + 935607 * 2 ^ 59
def prefixEnd_935607 : Nat := 4983230072969 + 3 ^ 40 * 935607 * 2
def baseEnd_935607 : Nat := 106759132158050259335495

theorem tailTrace_935607 : CollatzResearch.WordTrace tailWord_935607 prefixEnd_935607 106759132158050259335495 := by
  unfold tailWord_935607
  simp only [CollatzResearch.WordTrace]
  refine ⟨34124390721463102799261075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22749593814308735199507383 34124390721463102799261075)
  ·
    refine ⟨51186586082194654198891613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34124390721463102799261075 51186586082194654198891613)
    ·
      refine ⟨19194969780822995324584355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51186586082194654198891613 19194969780822995324584355)
      ·
        refine ⟨28792454671234492986876533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19194969780822995324584355 28792454671234492986876533)
        ·
          refine ⟨2699292625428233717519675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28792454671234492986876533 2699292625428233717519675)
          ·
            refine ⟨4048938938142350576279513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699292625428233717519675 4048938938142350576279513)
            ·
              refine ⟨3036704203606762932209635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048938938142350576279513 3036704203606762932209635)
              ·
                refine ⟨4555056305410144398314453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036704203606762932209635 4555056305410144398314453)
                ·
                  refine ⟨106759132158050259335495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4555056305410144398314453 106759132158050259335495)
                  ·
                    rfl

theorem cell22_935607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 7].length) (baseStart_935607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935607 prefixEnd_935607 := by exact prefixLift 935607
  have htrace : WordTrace (prefixWord ++ tailWord_935607) baseStart_935607 baseEnd_935607 := by
    simpa [prefixWord, tailWord_935607, baseEnd_935607] using wordTrace_append hprefix tailTrace_935607
  have hstable : (prefixWord ++ tailWord_935607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935607).length < 2 ^ (prefixWord ++ tailWord_935607).sum := by decide
  have hdescent : baseEnd_935607 < baseStart_935607 := by decide
  rcases family_descends (prefixWord ++ tailWord_935607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935684 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_935684 : Nat := 118140960795 + 935684 * 2 ^ 59
def prefixEnd_935684 : Nat := 4983230072969 + 3 ^ 40 * 935684 * 2
def baseEnd_935684 : Nat := 320303755147748243831249

theorem tailTrace_935684 : CollatzResearch.WordTrace tailWord_935684 prefixEnd_935684 320303755147748243831249 := by
  unfold tailWord_935684
  simp only [CollatzResearch.WordTrace]
  refine ⟨17063599571092072474907053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22751466094789429966542737 17063599571092072474907053)
  ·
    refine ⟨6398849839159527178090145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17063599571092072474907053 6398849839159527178090145)
    ·
      refine ⟨4799137379369645383567609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6398849839159527178090145 4799137379369645383567609)
      ·
        refine ⟨3599353034527234037675707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4799137379369645383567609 3599353034527234037675707)
        ·
          refine ⟨5399029551790851056513561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599353034527234037675707 5399029551790851056513561)
          ·
            refine ⟨4049272163843138292385171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5399029551790851056513561 4049272163843138292385171)
            ·
              refine ⟨6073908245764707438577757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049272163843138292385171 6073908245764707438577757)
              ·
                refine ⟨2277715592161765289466659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6073908245764707438577757 2277715592161765289466659)
                ·
                  refine ⟨3416573388242647934199989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277715592161765289466659 3416573388242647934199989)
                  ·
                    refine ⟨320303755147748243831249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3416573388242647934199989 320303755147748243831249)
                    ·
                      rfl

theorem cell22_935684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_935684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935684 prefixEnd_935684 := by exact prefixLift 935684
  have htrace : WordTrace (prefixWord ++ tailWord_935684) baseStart_935684 baseEnd_935684 := by
    simpa [prefixWord, tailWord_935684, baseEnd_935684] using wordTrace_append hprefix tailTrace_935684
  have hstable : (prefixWord ++ tailWord_935684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935684).length < 2 ^ (prefixWord ++ tailWord_935684).sum := by decide
  have hdescent : baseEnd_935684 < baseStart_935684 := by decide
  rcases family_descends (prefixWord ++ tailWord_935684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935780 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_935780 : Nat := 118140960795 + 935780 * 2 ^ 59
def prefixEnd_935780 : Nat := 4983230072969 + 3 ^ 40 * 935780 * 2
def baseEnd_935780 : Nat := 320336617909635993430955

theorem tailTrace_935780 : CollatzResearch.WordTrace tailWord_935780 prefixEnd_935780 320336617909635993430955 := by
  unfold tailWord_935780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065350274918176672654397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22753800366557568896872529 17065350274918176672654397)
  ·
    refine ⟨6399506353094316252245399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17065350274918176672654397 6399506353094316252245399)
    ·
      refine ⟨9599259529641474378368099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6399506353094316252245399 9599259529641474378368099)
      ·
        refine ⟨14398889294462211567552149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599259529641474378368099 14398889294462211567552149)
        ·
          refine ⟨674947935677916167229007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14398889294462211567552149 674947935677916167229007)
          ·
            refine ⟨1012421903516874250843511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674947935677916167229007 1012421903516874250843511)
            ·
              refine ⟨1518632855275311376265267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012421903516874250843511 1518632855275311376265267)
              ·
                refine ⟨2277949282912967064397901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518632855275311376265267 2277949282912967064397901)
                ·
                  refine ⟨854230981092362649149213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2277949282912967064397901 854230981092362649149213)
                  ·
                    refine ⟨320336617909635993430955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854230981092362649149213 320336617909635993430955)
                    ·
                      rfl

theorem cell22_935780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_935780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935780 prefixEnd_935780 := by exact prefixLift 935780
  have htrace : WordTrace (prefixWord ++ tailWord_935780) baseStart_935780 baseEnd_935780 := by
    simpa [prefixWord, tailWord_935780, baseEnd_935780] using wordTrace_append hprefix tailTrace_935780
  have hstable : (prefixWord ++ tailWord_935780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935780).length < 2 ^ (prefixWord ++ tailWord_935780).sum := by decide
  have hdescent : baseEnd_935780 < baseStart_935780 := by decide
  rcases family_descends (prefixWord ++ tailWord_935780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935868 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_935868 : Nat := 118140960795 + 935868 * 2 ^ 59
def prefixEnd_935868 : Nat := 4983230072969 + 3 ^ 40 * 935868 * 2
def baseEnd_935868 : Nat := 320366742108033097230685

theorem tailTrace_935868 : CollatzResearch.WordTrace tailWord_935868 prefixEnd_935868 320366742108033097230685 := by
  unfold tailWord_935868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066955086758772187256129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22755940115678362916341505 17066955086758772187256129)
  ·
    refine ⟨12800216315069079140442097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17066955086758772187256129 12800216315069079140442097)
    ·
      refine ⟨9600162236301809355331573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12800216315069079140442097 9600162236301809355331573)
      ·
        refine ⟨900015209653294627062335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9600162236301809355331573 900015209653294627062335)
        ·
          refine ⟨1350022814479941940593503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900015209653294627062335 1350022814479941940593503)
          ·
            refine ⟨2025034221719912910890255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350022814479941940593503 2025034221719912910890255)
            ·
              refine ⟨3037551332579869366335383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025034221719912910890255 3037551332579869366335383)
              ·
                refine ⟨4556326998869804049503075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037551332579869366335383 4556326998869804049503075)
                ·
                  refine ⟨6834490498304706074254613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556326998869804049503075 6834490498304706074254613)
                  ·
                    refine ⟨320366742108033097230685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6834490498304706074254613 320366742108033097230685)
                    ·
                      rfl

theorem cell22_935868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_935868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935868 prefixEnd_935868 := by exact prefixLift 935868
  have htrace : WordTrace (prefixWord ++ tailWord_935868) baseStart_935868 baseEnd_935868 := by
    simpa [prefixWord, tailWord_935868, baseEnd_935868] using wordTrace_append hprefix tailTrace_935868
  have hstable : (prefixWord ++ tailWord_935868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935868).length < 2 ^ (prefixWord ++ tailWord_935868).sum := by decide
  have hdescent : baseEnd_935868 < baseStart_935868 := by decide
  rcases family_descends (prefixWord ++ tailWord_935868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935917 : List Nat := [1, 5, 1, 4, 2, 1, 2, 6]
def baseStart_935917 : Nat := 118140960795 + 935917 * 2 ^ 59
def prefixEnd_935917 : Nat := 4983230072969 + 3 ^ 40 * 935917 * 2
def baseEnd_935917 : Nat := 35598168423268144750615

theorem tailTrace_935917 : CollatzResearch.WordTrace tailWord_935917 prefixEnd_935917 35598168423268144750615 := by
  unfold tailWord_935917
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135697350340025743046005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22757131566893350495364003 34135697350340025743046005)
  ·
    refine ⟨3200221626594377413410563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34135697350340025743046005 3200221626594377413410563)
    ·
      refine ⟨4800332439891566120115845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200221626594377413410563 4800332439891566120115845)
      ·
        refine ⟨900062332479668647521721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4800332439891566120115845 900062332479668647521721)
        ·
          refine ⟨675046749359751485641291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900062332479668647521721 675046749359751485641291)
          ·
            refine ⟨1012570124039627228461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675046749359751485641291 1012570124039627228461937)
            ·
              refine ⟨759427593029720421346453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012570124039627228461937 759427593029720421346453)
              ·
                refine ⟨35598168423268144750615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 759427593029720421346453 35598168423268144750615)
                ·
                  rfl

theorem cell22_935917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 6].length) (baseStart_935917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935917 prefixEnd_935917 := by exact prefixLift 935917
  have htrace : WordTrace (prefixWord ++ tailWord_935917) baseStart_935917 baseEnd_935917 := by
    simpa [prefixWord, tailWord_935917, baseEnd_935917] using wordTrace_append hprefix tailTrace_935917
  have hstable : (prefixWord ++ tailWord_935917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935917).length < 2 ^ (prefixWord ++ tailWord_935917).sum := by decide
  have hdescent : baseEnd_935917 < baseStart_935917 := by decide
  rcases family_descends (prefixWord ++ tailWord_935917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935939 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 8]
def baseStart_935939 : Nat := 118140960795 + 935939 * 2 ^ 59
def prefixEnd_935939 : Nat := 4983230072969 + 3 ^ 40 * 935939 * 2
def baseEnd_935939 : Nat := 106797015619670859568489

theorem tailTrace_935939 : CollatzResearch.WordTrace tailWord_935939 prefixEnd_935939 106797015619670859568489 := by
  unfold tailWord_935939
  simp only [CollatzResearch.WordTrace]
  refine ⟨34136499756260323500346871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22757666504173549000231247 34136499756260323500346871)
  ·
    refine ⟨51204749634390485250520307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34136499756260323500346871 51204749634390485250520307)
    ·
      refine ⟨76807124451585727875780461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51204749634390485250520307 76807124451585727875780461)
      ·
        refine ⟨28802671669344647953417673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76807124451585727875780461 28802671669344647953417673)
        ·
          refine ⟨21602003752008485965063255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28802671669344647953417673 21602003752008485965063255)
          ·
            refine ⟨32403005628012728947594883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21602003752008485965063255 32403005628012728947594883)
            ·
              refine ⟨48604508442019093421392325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32403005628012728947594883 48604508442019093421392325)
              ·
                refine ⟨9113345332878580016511061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48604508442019093421392325 9113345332878580016511061)
                ·
                  refine ⟨106797015619670859568489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9113345332878580016511061 106797015619670859568489)
                  ·
                    rfl

theorem cell22_935939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_935939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935939 prefixEnd_935939 := by exact prefixLift 935939
  have htrace : WordTrace (prefixWord ++ tailWord_935939) baseStart_935939 baseEnd_935939 := by
    simpa [prefixWord, tailWord_935939, baseEnd_935939] using wordTrace_append hprefix tailTrace_935939
  have hstable : (prefixWord ++ tailWord_935939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935939).length < 2 ^ (prefixWord ++ tailWord_935939).sum := by decide
  have hdescent : baseEnd_935939 < baseStart_935939 := by decide
  rcases family_descends (prefixWord ++ tailWord_935939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935971 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 1, 5]
def baseStart_935971 : Nat := 118140960795 + 935971 * 2 ^ 59
def prefixEnd_935971 : Nat := 4983230072969 + 3 ^ 40 * 935971 * 2
def baseEnd_935971 : Nat := 320402001112975161905369

theorem tailTrace_935971 : CollatzResearch.WordTrace tailWord_935971 prefixEnd_935971 320402001112975161905369 := by
  unfold tailWord_935971
  simp only [CollatzResearch.WordTrace]
  refine ⟨34137666892144392965511767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22758444594762928643674511 34137666892144392965511767)
  ·
    refine ⟨51206500338216589448267651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34137666892144392965511767 51206500338216589448267651)
    ·
      refine ⟨76809750507324884172401477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51206500338216589448267651 76809750507324884172401477)
      ·
        refine ⟨14401828220123415782325277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76809750507324884172401477 14401828220123415782325277)
        ·
          refine ⟨5400685582546280918371979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14401828220123415782325277 5400685582546280918371979)
          ·
            refine ⟨8101028373819421377557969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400685582546280918371979 8101028373819421377557969)
            ·
              refine ⟨6075771280364566033168477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8101028373819421377557969 6075771280364566033168477)
              ·
                refine ⟨2278414230136712262438179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6075771280364566033168477 2278414230136712262438179)
                ·
                  refine ⟨3417621345205068393657269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278414230136712262438179 3417621345205068393657269)
                  ·
                    refine ⟨320402001112975161905369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3417621345205068393657269 320402001112975161905369)
                    ·
                      rfl

theorem cell22_935971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_935971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935971 prefixEnd_935971 := by exact prefixLift 935971
  have htrace : WordTrace (prefixWord ++ tailWord_935971) baseStart_935971 baseEnd_935971 := by
    simpa [prefixWord, tailWord_935971, baseEnd_935971] using wordTrace_append hprefix tailTrace_935971
  have hstable : (prefixWord ++ tailWord_935971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935971).length < 2 ^ (prefixWord ++ tailWord_935971).sum := by decide
  have hdescent : baseEnd_935971 < baseStart_935971 := by decide
  rcases family_descends (prefixWord ++ tailWord_935971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935975 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 3, 4]
def baseStart_935975 : Nat := 118140960795 + 935975 * 2 ^ 59
def prefixEnd_935975 : Nat := 4983230072969 + 3 ^ 40 * 935975 * 2
def baseEnd_935975 : Nat := 320403370394720484805357

theorem tailTrace_935975 : CollatzResearch.WordTrace tailWord_935975 prefixEnd_935975 320403370394720484805357 := by
  unfold tailWord_935975
  simp only [CollatzResearch.WordTrace]
  refine ⟨34137812784129901648657379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22758541856086601099104919 34137812784129901648657379)
  ·
    refine ⟨51206719176194852472986069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34137812784129901648657379 51206719176194852472986069)
    ·
      refine ⟨1200157480692066854835611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51206719176194852472986069 1200157480692066854835611)
      ·
        refine ⟨1800236221038100282253417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200157480692066854835611 1800236221038100282253417)
        ·
          refine ⟨1350177165778575211690063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800236221038100282253417 1350177165778575211690063)
          ·
            refine ⟨2025265748667862817535095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350177165778575211690063 2025265748667862817535095)
            ·
              refine ⟨3037898623001794226302643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025265748667862817535095 3037898623001794226302643)
              ·
                refine ⟨4556847934502691339453965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037898623001794226302643 4556847934502691339453965)
                ·
                  refine ⟨1708817975438509252295237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4556847934502691339453965 1708817975438509252295237)
                  ·
                    refine ⟨320403370394720484805357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1708817975438509252295237 320403370394720484805357)
                    ·
                      rfl

theorem cell22_935975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_935975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935975 prefixEnd_935975 := by exact prefixLift 935975
  have htrace : WordTrace (prefixWord ++ tailWord_935975) baseStart_935975 baseEnd_935975 := by
    simpa [prefixWord, tailWord_935975, baseEnd_935975] using wordTrace_append hprefix tailTrace_935975
  have hstable : (prefixWord ++ tailWord_935975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935975).length < 2 ^ (prefixWord ++ tailWord_935975).sum := by decide
  have hdescent : baseEnd_935975 < baseStart_935975 := by decide
  rcases family_descends (prefixWord ++ tailWord_935975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935990 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_935990 : Nat := 118140960795 + 935990 * 2 ^ 59
def prefixEnd_935990 : Nat := 4983230072969 + 3 ^ 40 * 935990 * 2
def baseEnd_935990 : Nat := 106802835067088481893437

theorem tailTrace_935990 : CollatzResearch.WordTrace tailWord_935990 prefixEnd_935990 106802835067088481893437 := by
  unfold tailWord_935990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133647492442222450653339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22758906586050372806968949 2133647492442222450653339)
  ·
    refine ⟨3200471238663333675980009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133647492442222450653339 3200471238663333675980009)
    ·
      refine ⟨2400353428997500256985007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3200471238663333675980009 2400353428997500256985007)
      ·
        refine ⟨3600530143496250385477511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400353428997500256985007 3600530143496250385477511)
        ·
          refine ⟨5400795215244375578216267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600530143496250385477511 5400795215244375578216267)
          ·
            refine ⟨8101192822866563367324401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400795215244375578216267 8101192822866563367324401)
            ·
              refine ⟨6075894617149922525493301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8101192822866563367324401 6075894617149922525493301)
              ·
                refine ⟨569615120357805236764997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6075894617149922525493301 569615120357805236764997)
                ·
                  refine ⟨106802835067088481893437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569615120357805236764997 106802835067088481893437)
                  ·
                    rfl

theorem cell22_935990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_935990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_935990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_935990 prefixEnd_935990 := by exact prefixLift 935990
  have htrace : WordTrace (prefixWord ++ tailWord_935990) baseStart_935990 baseEnd_935990 := by
    simpa [prefixWord, tailWord_935990, baseEnd_935990] using wordTrace_append hprefix tailTrace_935990
  have hstable : (prefixWord ++ tailWord_935990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935990).length < 2 ^ (prefixWord ++ tailWord_935990).sum := by decide
  have hdescent : baseEnd_935990 < baseStart_935990 := by decide
  rcases family_descends (prefixWord ++ tailWord_935990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936001 : List Nat := [1, 2, 5, 1, 2, 11]
def baseStart_936001 : Nat := 118140960795 + 936001 * 2 ^ 59
def prefixEnd_936001 : Nat := 4983230072969 + 3 ^ 40 * 936001 * 2
def baseEnd_936001 : Nat := 3955707046000803501917

theorem tailTrace_936001 : CollatzResearch.WordTrace tailWord_936001 prefixEnd_936001 3955707046000803501917 := by
  unfold tailWord_936001
  simp only [CollatzResearch.WordTrace]
  refine ⟨34138761082035708089103857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22759174054690472059402571 34138761082035708089103857)
  ·
    refine ⟨25604070811526781066827893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34138761082035708089103857 25604070811526781066827893)
    ·
      refine ⟨2400381638580635725015115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25604070811526781066827893 2400381638580635725015115)
      ·
        refine ⟨3600572457870953587522673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400381638580635725015115 3600572457870953587522673)
        ·
          refine ⟨2700429343403215190642005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600572457870953587522673 2700429343403215190642005)
          ·
            refine ⟨3955707046000803501917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2700429343403215190642005 3955707046000803501917)
            ·
              rfl

theorem cell22_936001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 11].length) (baseStart_936001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936001 prefixEnd_936001 := by exact prefixLift 936001
  have htrace : WordTrace (prefixWord ++ tailWord_936001) baseStart_936001 baseEnd_936001 := by
    simpa [prefixWord, tailWord_936001, baseEnd_936001] using wordTrace_append hprefix tailTrace_936001
  have hstable : (prefixWord ++ tailWord_936001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936001).length < 2 ^ (prefixWord ++ tailWord_936001).sum := by decide
  have hdescent : baseEnd_936001 < baseStart_936001 := by decide
  rcases family_descends (prefixWord ++ tailWord_936001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936022 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_936022 : Nat := 118140960795 + 936022 * 2 ^ 59
def prefixEnd_936022 : Nat := 4983230072969 + 3 ^ 40 * 936022 * 2
def baseEnd_936022 : Nat := 320419459455228028880213

theorem tailTrace_936022 : CollatzResearch.WordTrace tailWord_936022 prefixEnd_936022 320419459455228028880213 := by
  unfold tailWord_936022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133720438434976792226145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22759684676639752450412213 2133720438434976792226145)
  ·
    refine ⟨1600290328826232594169609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2133720438434976792226145 1600290328826232594169609)
    ·
      refine ⟨1200217746619674445627207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600290328826232594169609 1200217746619674445627207)
      ·
        refine ⟨1800326619929511668440811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200217746619674445627207 1800326619929511668440811)
        ·
          refine ⟨2700489929894267502661217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800326619929511668440811 2700489929894267502661217)
          ·
            refine ⟨2025367447420700626995913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2700489929894267502661217 2025367447420700626995913)
            ·
              refine ⟨1519025585565525470246935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025367447420700626995913 1519025585565525470246935)
              ·
                refine ⟨2278538378348288205370403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519025585565525470246935 2278538378348288205370403)
                ·
                  refine ⟨3417807567522432308055605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278538378348288205370403 3417807567522432308055605)
                  ·
                    refine ⟨320419459455228028880213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3417807567522432308055605 320419459455228028880213)
                    ·
                      rfl

theorem cell22_936022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_936022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936022 prefixEnd_936022 := by exact prefixLift 936022
  have htrace : WordTrace (prefixWord ++ tailWord_936022) baseStart_936022 baseEnd_936022 := by
    simpa [prefixWord, tailWord_936022, baseEnd_936022] using wordTrace_append hprefix tailTrace_936022
  have hstable : (prefixWord ++ tailWord_936022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936022).length < 2 ^ (prefixWord ++ tailWord_936022).sum := by decide
  have hdescent : baseEnd_936022 < baseStart_936022 := by decide
  rcases family_descends (prefixWord ++ tailWord_936022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936091 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 6]
def baseStart_936091 : Nat := 118140960795 + 936091 * 2 ^ 59
def prefixEnd_936091 : Nat := 4983230072969 + 3 ^ 40 * 936091 * 2
def baseEnd_936091 : Nat := 106814359855111616301667

theorem tailTrace_936091 : CollatzResearch.WordTrace tailWord_936091 prefixEnd_936091 106814359855111616301667 := by
  unfold tailWord_936091
  simp only [CollatzResearch.WordTrace]
  refine ⟨34142043651709653459880127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22761362434473102306586751 34142043651709653459880127)
  ·
    refine ⟨51213065477564480189820191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34142043651709653459880127 51213065477564480189820191)
    ·
      refine ⟨76819598216346720284730287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51213065477564480189820191 76819598216346720284730287)
      ·
        refine ⟨115229397324520080427095431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76819598216346720284730287 115229397324520080427095431)
        ·
          refine ⟨172844095986780120640643147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115229397324520080427095431 172844095986780120640643147)
          ·
            refine ⟨259266143980170180960964721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172844095986780120640643147 259266143980170180960964721)
            ·
              refine ⟨194449607985127635720723541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259266143980170180960964721 194449607985127635720723541)
              ·
                refine ⟨2278706343575714481102229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 194449607985127635720723541 2278706343575714481102229)
                ·
                  refine ⟨106814359855111616301667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2278706343575714481102229 106814359855111616301667)
                  ·
                    rfl

theorem cell22_936091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_936091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936091 prefixEnd_936091 := by exact prefixLift 936091
  have htrace : WordTrace (prefixWord ++ tailWord_936091) baseStart_936091 baseEnd_936091 := by
    simpa [prefixWord, tailWord_936091, baseEnd_936091] using wordTrace_append hprefix tailTrace_936091
  have hstable : (prefixWord ++ tailWord_936091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936091).length < 2 ^ (prefixWord ++ tailWord_936091).sum := by decide
  have hdescent : baseEnd_936091 < baseStart_936091 := by decide
  rcases family_descends (prefixWord ++ tailWord_936091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936123 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 4, 3]
def baseStart_936123 : Nat := 118140960795 + 936123 * 2 ^ 59
def prefixEnd_936123 : Nat := 4983230072969 + 3 ^ 40 * 936123 * 2
def baseEnd_936123 : Nat := 320454033819297432104903

theorem tailTrace_936123 : CollatzResearch.WordTrace tailWord_936123 prefixEnd_936123 320454033819297432104903 := by
  unfold tailWord_936123
  simp only [CollatzResearch.WordTrace]
  refine ⟨34143210787593722925045023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22762140525062481950030015 34143210787593722925045023)
  ·
    refine ⟨51214816181390584387567535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34143210787593722925045023 51214816181390584387567535)
    ·
      refine ⟨76822224272085876581351303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51214816181390584387567535 76822224272085876581351303)
      ·
        refine ⟨115233336408128814872026955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76822224272085876581351303 115233336408128814872026955)
        ·
          refine ⟨172850004612193222308040433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115233336408128814872026955 172850004612193222308040433)
          ·
            refine ⟨129637503459144916731030325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172850004612193222308040433 129637503459144916731030325)
            ·
              refine ⟨12153515949294835943534093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129637503459144916731030325 12153515949294835943534093)
              ·
                refine ⟨4557568480985563478825285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12153515949294835943534093 4557568480985563478825285)
                ·
                  refine ⟨854544090184793152279741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4557568480985563478825285 854544090184793152279741)
                  ·
                    refine ⟨320454033819297432104903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854544090184793152279741 320454033819297432104903)
                    ·
                      rfl

theorem cell22_936123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 3].length) (baseStart_936123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936123 prefixEnd_936123 := by exact prefixLift 936123
  have htrace : WordTrace (prefixWord ++ tailWord_936123) baseStart_936123 baseEnd_936123 := by
    simpa [prefixWord, tailWord_936123, baseEnd_936123] using wordTrace_append hprefix tailTrace_936123
  have hstable : (prefixWord ++ tailWord_936123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936123).length < 2 ^ (prefixWord ++ tailWord_936123).sum := by decide
  have hdescent : baseEnd_936123 < baseStart_936123 := by decide
  rcases family_descends (prefixWord ++ tailWord_936123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936138 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_936138 : Nat := 118140960795 + 936138 * 2 ^ 59
def prefixEnd_936138 : Nat := 4983230072969 + 3 ^ 40 * 936138 * 2
def baseEnd_936138 : Nat := 320459168625842392979857

theorem tailTrace_936138 : CollatzResearch.WordTrace tailWord_936138 prefixEnd_936138 320459168625842392979857 := by
  unfold tailWord_936138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535939470634845121710267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22762505255026253657894045 8535939470634845121710267)
  ·
    refine ⟨12803909205952267682565401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8535939470634845121710267 12803909205952267682565401)
    ·
      refine ⟨9602931904464200761924051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12803909205952267682565401 9602931904464200761924051)
      ·
        refine ⟨14404397856696301142886077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602931904464200761924051 14404397856696301142886077)
        ·
          refine ⟨5401649196261112928582279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14404397856696301142886077 5401649196261112928582279)
          ·
            refine ⟨8102473794391669392873419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401649196261112928582279 8102473794391669392873419)
            ·
              refine ⟨12153710691587504089310129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102473794391669392873419 12153710691587504089310129)
              ·
                refine ⟨9115283018690628066982597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12153710691587504089310129 9115283018690628066982597)
                ·
                  refine ⟨1709115566004492762559237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9115283018690628066982597 1709115566004492762559237)
                  ·
                    refine ⟨320459168625842392979857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709115566004492762559237 320459168625842392979857)
                    ·
                      rfl

theorem cell22_936138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_936138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936138 prefixEnd_936138 := by exact prefixLift 936138
  have htrace : WordTrace (prefixWord ++ tailWord_936138) baseStart_936138 baseEnd_936138 := by
    simpa [prefixWord, tailWord_936138, baseEnd_936138] using wordTrace_append hprefix tailTrace_936138
  have hstable : (prefixWord ++ tailWord_936138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936138).length < 2 ^ (prefixWord ++ tailWord_936138).sum := by decide
  have hdescent : baseEnd_936138 < baseStart_936138 := by decide
  rcases family_descends (prefixWord ++ tailWord_936138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936292 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_936292 : Nat := 118140960795 + 936292 * 2 ^ 59
def prefixEnd_936292 : Nat := 4983230072969 + 3 ^ 40 * 936292 * 2
def baseEnd_936292 : Nat := 320511885973037324629385

theorem tailTrace_936292 : CollatzResearch.WordTrace tailWord_936292 prefixEnd_936292 320511885973037324629385 := by
  unfold tailWord_936292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17074687361990732393973565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22766249815987643191964753 17074687361990732393973565)
  ·
    refine ⟨6403007760746524647740087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17074687361990732393973565 6403007760746524647740087)
    ·
      refine ⟨9604511641119786971610131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6403007760746524647740087 9604511641119786971610131)
      ·
        refine ⟨14406767461679680457415197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604511641119786971610131 14406767461679680457415197)
        ·
          refine ⟨5402537798129880171530699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14406767461679680457415197 5402537798129880171530699)
          ·
            refine ⟨8103806697194820257296049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402537798129880171530699 8103806697194820257296049)
            ·
              refine ⟨6077855022896115192972037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8103806697194820257296049 6077855022896115192972037)
              ·
                refine ⟨1139597816793021598682257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6077855022896115192972037 1139597816793021598682257)
                ·
                  refine ⟨854698362594766199011693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1139597816793021598682257 854698362594766199011693)
                  ·
                    refine ⟨320511885973037324629385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854698362594766199011693 320511885973037324629385)
                    ·
                      rfl

theorem cell22_936292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_936292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936292 prefixEnd_936292 := by exact prefixLift 936292
  have htrace : WordTrace (prefixWord ++ tailWord_936292) baseStart_936292 baseEnd_936292 := by
    simpa [prefixWord, tailWord_936292, baseEnd_936292] using wordTrace_append hprefix tailTrace_936292
  have hstable : (prefixWord ++ tailWord_936292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936292).length < 2 ^ (prefixWord ++ tailWord_936292).sum := by decide
  have hdescent : baseEnd_936292 < baseStart_936292 := by decide
  rcases family_descends (prefixWord ++ tailWord_936292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936303 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_936303 : Nat := 118140960795 + 936303 * 2 ^ 59
def prefixEnd_936303 : Nat := 4983230072969 + 3 ^ 40 * 936303 * 2
def baseEnd_936303 : Nat := 320515651497836962604351

theorem tailTrace_936303 : CollatzResearch.WordTrace tailWord_936303 prefixEnd_936303 320515651497836962604351 := by
  unfold tailWord_936303
  simp only [CollatzResearch.WordTrace]
  refine ⟨34149775926941613666597563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22766517284627742444398375 34149775926941613666597563)
  ·
    refine ⟨51224663890412420499896345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34149775926941613666597563 51224663890412420499896345)
    ·
      refine ⟨38418497917809315374922259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51224663890412420499896345 38418497917809315374922259)
      ·
        refine ⟨57627746876713973062383389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38418497917809315374922259 57627746876713973062383389)
        ·
          refine ⟨21610405078767739898393771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57627746876713973062383389 21610405078767739898393771)
          ·
            refine ⟨32415607618151609847590657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21610405078767739898393771 32415607618151609847590657)
            ·
              refine ⟨24311705713613707385692993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32415607618151609847590657 24311705713613707385692993)
              ·
                refine ⟨18233779285210280539269745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24311705713613707385692993 18233779285210280539269745)
                ·
                  refine ⟨13675334463907710404452309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18233779285210280539269745 13675334463907710404452309)
                  ·
                    refine ⟨320515651497836962604351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13675334463907710404452309 320515651497836962604351)
                    ·
                      rfl

theorem cell22_936303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_936303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936303 prefixEnd_936303 := by exact prefixLift 936303
  have htrace : WordTrace (prefixWord ++ tailWord_936303) baseStart_936303 baseEnd_936303 := by
    simpa [prefixWord, tailWord_936303, baseEnd_936303] using wordTrace_append hprefix tailTrace_936303
  have hstable : (prefixWord ++ tailWord_936303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936303).length < 2 ^ (prefixWord ++ tailWord_936303).sum := by decide
  have hdescent : baseEnd_936303 < baseStart_936303 := by decide
  rcases family_descends (prefixWord ++ tailWord_936303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936309 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_936309 : Nat := 118140960795 + 936309 * 2 ^ 59
def prefixEnd_936309 : Nat := 4983230072969 + 3 ^ 40 * 936309 * 2
def baseEnd_936309 : Nat := 320517705420454946954333

theorem tailTrace_936309 : CollatzResearch.WordTrace tailWord_936309 prefixEnd_936309 320517705420454946954333 := by
  unfold tailWord_936309
  simp only [CollatzResearch.WordTrace]
  refine ⟨34149994764919876691315981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22766663176613251127543987 34149994764919876691315981)
  ·
    refine ⟨12806248036844953759243493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34149994764919876691315981 12806248036844953759243493)
    ·
      refine ⟨2401171506908428829858155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12806248036844953759243493 2401171506908428829858155)
      ·
        refine ⟨3601757260362643244787233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401171506908428829858155 3601757260362643244787233)
        ·
          refine ⟨2701317945271982433590425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601757260362643244787233 2701317945271982433590425)
          ·
            refine ⟨2025988458953986825192819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701317945271982433590425 2025988458953986825192819)
            ·
              refine ⟨3038982688430980237789229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025988458953986825192819 3038982688430980237789229)
              ·
                refine ⟨1139618508161617589170961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3038982688430980237789229 1139618508161617589170961)
                ·
                  refine ⟨854713881121213191878221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1139618508161617589170961 854713881121213191878221)
                  ·
                    refine ⟨320517705420454946954333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854713881121213191878221 320517705420454946954333)
                    ·
                      rfl

theorem cell22_936309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_936309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936309 prefixEnd_936309 := by exact prefixLift 936309
  have htrace : WordTrace (prefixWord ++ tailWord_936309) baseStart_936309 baseEnd_936309 := by
    simpa [prefixWord, tailWord_936309, baseEnd_936309] using wordTrace_append hprefix tailTrace_936309
  have hstable : (prefixWord ++ tailWord_936309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936309).length < 2 ^ (prefixWord ++ tailWord_936309).sum := by decide
  have hdescent : baseEnd_936309 < baseStart_936309 := by decide
  rcases family_descends (prefixWord ++ tailWord_936309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936388 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_936388 : Nat := 118140960795 + 936388 * 2 ^ 59
def prefixEnd_936388 : Nat := 4983230072969 + 3 ^ 40 * 936388 * 2
def baseEnd_936388 : Nat := 320544748734925074229091

theorem tailTrace_936388 : CollatzResearch.WordTrace tailWord_936388 prefixEnd_936388 320544748734925074229091 := by
  unfold tailWord_936388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17076438065816836591720909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22768584087755782122294545 17076438065816836591720909)
  ·
    refine ⟨6403664274681313721895341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17076438065816836591720909 6403664274681313721895341)
    ·
      refine ⟨2401374103005492645710753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6403664274681313721895341 2401374103005492645710753)
      ·
        refine ⟨1801030577254119484283065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2401374103005492645710753 1801030577254119484283065)
        ·
          refine ⟨1350772932940589613212299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801030577254119484283065 1350772932940589613212299)
          ·
            refine ⟨2026159399410884419818449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350772932940589613212299 2026159399410884419818449)
            ·
              refine ⟨1519619549558163314863837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026159399410884419818449 1519619549558163314863837)
              ·
                refine ⟨569857331084311243073939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1519619549558163314863837 569857331084311243073939)
                ·
                  refine ⟨854785996626466864610909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569857331084311243073939 854785996626466864610909)
                  ·
                    refine ⟨320544748734925074229091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854785996626466864610909 320544748734925074229091)
                    ·
                      rfl

theorem cell22_936388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_936388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936388 prefixEnd_936388 := by exact prefixLift 936388
  have htrace : WordTrace (prefixWord ++ tailWord_936388) baseStart_936388 baseEnd_936388 := by
    simpa [prefixWord, tailWord_936388, baseEnd_936388] using wordTrace_append hprefix tailTrace_936388
  have hstable : (prefixWord ++ tailWord_936388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936388).length < 2 ^ (prefixWord ++ tailWord_936388).sum := by decide
  have hdescent : baseEnd_936388 < baseStart_936388 := by decide
  rcases family_descends (prefixWord ++ tailWord_936388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936418 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_936418 : Nat := 118140960795 + 936418 * 2 ^ 59
def prefixEnd_936418 : Nat := 4983230072969 + 3 ^ 40 * 936418 * 2
def baseEnd_936418 : Nat := 106851672782671665326333

theorem tailTrace_936418 : CollatzResearch.WordTrace tailWord_936418 prefixEnd_936418 106851672782671665326333 := by
  unfold tailWord_936418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538492580381247076758477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22769313547683325538022605 8538492580381247076758477)
  ·
    refine ⟨3201934717642967653784429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8538492580381247076758477 3201934717642967653784429)
    ·
      refine ⟨1200725519116112870169161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3201934717642967653784429 1200725519116112870169161)
      ·
        refine ⟨900544139337084652626871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200725519116112870169161 900544139337084652626871)
        ·
          refine ⟨1350816209005626978940307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900544139337084652626871 1350816209005626978940307)
          ·
            refine ⟨2026224313508440468410461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350816209005626978940307 2026224313508440468410461)
            ·
              refine ⟨759834117565665175653923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2026224313508440468410461 759834117565665175653923)
              ·
                refine ⟨1139751176348497763480885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759834117565665175653923 1139751176348497763480885)
                ·
                  refine ⟨106851672782671665326333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1139751176348497763480885 106851672782671665326333)
                  ·
                    rfl

theorem cell22_936418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_936418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936418 prefixEnd_936418 := by exact prefixLift 936418
  have htrace : WordTrace (prefixWord ++ tailWord_936418) baseStart_936418 baseEnd_936418 := by
    simpa [prefixWord, tailWord_936418, baseEnd_936418] using wordTrace_append hprefix tailTrace_936418
  have hstable : (prefixWord ++ tailWord_936418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936418).length < 2 ^ (prefixWord ++ tailWord_936418).sum := by decide
  have hdescent : baseEnd_936418 < baseStart_936418 := by decide
  rcases family_descends (prefixWord ++ tailWord_936418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936425 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_936425 : Nat := 118140960795 + 936425 * 2 ^ 59
def prefixEnd_936425 : Nat := 4983230072969 + 3 ^ 40 * 936425 * 2
def baseEnd_936425 : Nat := 320557414591069311053977

theorem tailTrace_936425 : CollatzResearch.WordTrace tailWord_936425 prefixEnd_936425 320557414591069311053977 := by
  unfold tailWord_936425
  simp only [CollatzResearch.WordTrace]
  refine ⟨34154225632499628502538729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22769483754999752335025819 34154225632499628502538729)
  ·
    refine ⟨25615669224374721376904047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34154225632499628502538729 25615669224374721376904047)
    ·
      refine ⟨38423503836562082065356071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25615669224374721376904047 38423503836562082065356071)
      ·
        refine ⟨57635255754843123098034107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38423503836562082065356071 57635255754843123098034107)
        ·
          refine ⟨86452883632264684647051161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57635255754843123098034107 86452883632264684647051161)
          ·
            refine ⟨64839662724198513485288371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86452883632264684647051161 64839662724198513485288371)
            ·
              refine ⟨97259494086297770227932557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64839662724198513485288371 97259494086297770227932557)
              ·
                refine ⟨36472310282361663835474709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97259494086297770227932557 36472310282361663835474709)
                ·
                  refine ⟨1709639544485702992287877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36472310282361663835474709 1709639544485702992287877)
                  ·
                    refine ⟨320557414591069311053977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709639544485702992287877 320557414591069311053977)
                    ·
                      rfl

theorem cell22_936425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_936425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936425 prefixEnd_936425 := by exact prefixLift 936425
  have htrace : WordTrace (prefixWord ++ tailWord_936425) baseStart_936425 baseEnd_936425 := by
    simpa [prefixWord, tailWord_936425, baseEnd_936425] using wordTrace_append hprefix tailTrace_936425
  have hstable : (prefixWord ++ tailWord_936425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936425).length < 2 ^ (prefixWord ++ tailWord_936425).sum := by decide
  have hdescent : baseEnd_936425 < baseStart_936425 := by decide
  rcases family_descends (prefixWord ++ tailWord_936425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936440 : List Nat := [2, 1, 2, 1, 1, 4, 3, 8]
def baseStart_936440 : Nat := 118140960795 + 936440 * 2 ^ 59
def prefixEnd_936440 : Nat := 4983230072969 + 3 ^ 40 * 936440 * 2
def baseEnd_936440 : Nat := 35618061044179363547659

theorem tailTrace_936440 : CollatzResearch.WordTrace tailWord_936440 prefixEnd_936440 35618061044179363547659 := by
  unfold tailWord_936440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17077386363722643032167387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22769848484963524042889849 17077386363722643032167387)
  ·
    refine ⟨25616079545583964548251081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17077386363722643032167387 25616079545583964548251081)
    ·
      refine ⟨19212059659187973411188311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25616079545583964548251081 19212059659187973411188311)
      ·
        refine ⟨28818089488781960116782467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19212059659187973411188311 28818089488781960116782467)
        ·
          refine ⟨43227134233172940175173701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28818089488781960116782467 43227134233172940175173701)
          ·
            refine ⟨8105087668719926282845069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43227134233172940175173701 8105087668719926282845069)
            ·
              refine ⟨3039407875769972356066901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8105087668719926282845069 3039407875769972356066901)
              ·
                refine ⟨35618061044179363547659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3039407875769972356066901 35618061044179363547659)
                ·
                  rfl

theorem cell22_936440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_936440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936440 prefixEnd_936440 := by exact prefixLift 936440
  have htrace : WordTrace (prefixWord ++ tailWord_936440) baseStart_936440 baseEnd_936440 := by
    simpa [prefixWord, tailWord_936440, baseEnd_936440] using wordTrace_append hprefix tailTrace_936440
  have hstable : (prefixWord ++ tailWord_936440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936440).length < 2 ^ (prefixWord ++ tailWord_936440).sum := by decide
  have hdescent : baseEnd_936440 < baseStart_936440 := by decide
  rcases family_descends (prefixWord ++ tailWord_936440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936519 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 5]
def baseStart_936519 : Nat := 118140960795 + 936519 * 2 ^ 59
def prefixEnd_936519 : Nat := 4983230072969 + 3 ^ 40 * 936519 * 2
def baseEnd_936519 : Nat := 106863197570694799734563

theorem tailTrace_936519 : CollatzResearch.WordTrace tailWord_936519 prefixEnd_936519 106863197570694799734563 := by
  unfold tailWord_936519
  simp only [CollatzResearch.WordTrace]
  refine ⟨34157654094159082556460611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22771769396106055037640407 34157654094159082556460611)
  ·
    refine ⟨51236481141238623834690917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34157654094159082556460611 51236481141238623834690917)
    ·
      refine ⟨9606840213982241969004547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51236481141238623834690917 9606840213982241969004547)
      ·
        refine ⟨14410260320973362953506821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9606840213982241969004547 14410260320973362953506821)
        ·
          refine ⟨2701923810182505553782529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14410260320973362953506821 2701923810182505553782529)
          ·
            refine ⟨2026442857636879165336897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701923810182505553782529 2026442857636879165336897)
            ·
              refine ⟨1519832143227659374002673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026442857636879165336897 1519832143227659374002673)
              ·
                refine ⟨1139874107420744530502005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519832143227659374002673 1139874107420744530502005)
                ·
                  refine ⟨106863197570694799734563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1139874107420744530502005 106863197570694799734563)
                  ·
                    rfl

theorem cell22_936519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 5].length) (baseStart_936519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936519 prefixEnd_936519 := by exact prefixLift 936519
  have htrace : WordTrace (prefixWord ++ tailWord_936519) baseStart_936519 baseEnd_936519 := by
    simpa [prefixWord, tailWord_936519, baseEnd_936519] using wordTrace_append hprefix tailTrace_936519
  have hstable : (prefixWord ++ tailWord_936519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936519).length < 2 ^ (prefixWord ++ tailWord_936519).sum := by decide
  have hdescent : baseEnd_936519 < baseStart_936519 := by decide
  rcases family_descends (prefixWord ++ tailWord_936519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936547 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 6]
def baseStart_936547 : Nat := 118140960795 + 936547 * 2 ^ 59
def prefixEnd_936547 : Nat := 4983230072969 + 3 ^ 40 * 936547 * 2
def baseEnd_936547 : Nat := 106866392561433886501201

theorem tailTrace_936547 : CollatzResearch.WordTrace tailWord_936547 prefixEnd_936547 106866392561433886501201 := by
  unfold tailWord_936547
  simp only [CollatzResearch.WordTrace]
  refine ⟨34158675338057643338479895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22772450225371762225653263 34158675338057643338479895)
  ·
    refine ⟨51238013007086465007719843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34158675338057643338479895 51238013007086465007719843)
    ·
      refine ⟨76857019510629697511579765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51238013007086465007719843 76857019510629697511579765)
      ·
        refine ⟨7205345579121534141710603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76857019510629697511579765 7205345579121534141710603)
        ·
          refine ⟨10808018368682301212565905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205345579121534141710603 10808018368682301212565905)
          ·
            refine ⟨8106013776511725909424429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10808018368682301212565905 8106013776511725909424429)
            ·
              refine ⟨3039755166191897216034161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8106013776511725909424429 3039755166191897216034161)
              ·
                refine ⟨2279816374643922912025621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039755166191897216034161 2279816374643922912025621)
                ·
                  refine ⟨106866392561433886501201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2279816374643922912025621 106866392561433886501201)
                  ·
                    rfl

theorem cell22_936547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_936547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936547 prefixEnd_936547 := by exact prefixLift 936547
  have htrace : WordTrace (prefixWord ++ tailWord_936547) baseStart_936547 baseEnd_936547 := by
    simpa [prefixWord, tailWord_936547, baseEnd_936547] using wordTrace_append hprefix tailTrace_936547
  have hstable : (prefixWord ++ tailWord_936547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936547).length < 2 ^ (prefixWord ++ tailWord_936547).sum := by decide
  have hdescent : baseEnd_936547 < baseStart_936547 := by decide
  rcases family_descends (prefixWord ++ tailWord_936547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936594 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_936594 : Nat := 118140960795 + 936594 * 2 ^ 59
def prefixEnd_936594 : Nat := 4983230072969 + 3 ^ 40 * 936594 * 2
def baseEnd_936594 : Nat := 320615266744809203578459

theorem tailTrace_936594 : CollatzResearch.WordTrace tailWord_936594 prefixEnd_936594 320615266744809203578459 := by
  unfold tailWord_936594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540097392221842591360209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22773593045924913576960557 8540097392221842591360209)
  ·
    refine ⟨6405073044166381943520157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8540097392221842591360209 6405073044166381943520157)
    ·
      refine ⟨2401902391562393228820059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6405073044166381943520157 2401902391562393228820059)
      ·
        refine ⟨3602853587343589843230089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401902391562393228820059 3602853587343589843230089)
        ·
          refine ⟨2702140190507692382422567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3602853587343589843230089 2702140190507692382422567)
          ·
            refine ⟨4053210285761538573633851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702140190507692382422567 4053210285761538573633851)
            ·
              refine ⟨6079815428642307860450777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053210285761538573633851 6079815428642307860450777)
              ·
                refine ⟨4559861571481730895338083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079815428642307860450777 4559861571481730895338083)
                ·
                  refine ⟨6839792357222596343007125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559861571481730895338083 6839792357222596343007125)
                  ·
                    refine ⟨320615266744809203578459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6839792357222596343007125 320615266744809203578459)
                    ·
                      rfl

theorem cell22_936594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_936594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936594 prefixEnd_936594 := by exact prefixLift 936594
  have htrace : WordTrace (prefixWord ++ tailWord_936594) baseStart_936594 baseEnd_936594 := by
    simpa [prefixWord, tailWord_936594, baseEnd_936594] using wordTrace_append hprefix tailTrace_936594
  have hstable : (prefixWord ++ tailWord_936594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936594).length < 2 ^ (prefixWord ++ tailWord_936594).sum := by decide
  have hdescent : baseEnd_936594 < baseStart_936594 := by decide
  rcases family_descends (prefixWord ++ tailWord_936594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936596 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_936596 : Nat := 118140960795 + 936596 * 2 ^ 59
def prefixEnd_936596 : Nat := 4983230072969 + 3 ^ 40 * 936596 * 2
def baseEnd_936596 : Nat := 320615951385681865028453

theorem tailTrace_936596 : CollatzResearch.WordTrace tailWord_936596 prefixEnd_936596 320615951385681865028453 := by
  unfold tailWord_936596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17080231257440062353506821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22773641676586749804675761 17080231257440062353506821)
  ·
    refine ⟨3202543360770011691282529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17080231257440062353506821 3202543360770011691282529)
    ·
      refine ⟨2401907520577508768461897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3202543360770011691282529 2401907520577508768461897)
      ·
        refine ⟨1801430640433131576346423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2401907520577508768461897 1801430640433131576346423)
        ·
          refine ⟨2702145960649697364519635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801430640433131576346423 2702145960649697364519635)
          ·
            refine ⟨4053218940974546046779453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702145960649697364519635 4053218940974546046779453)
            ·
              refine ⟨1519957102865454767542295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4053218940974546046779453 1519957102865454767542295)
              ·
                refine ⟨2279935654298182151313443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519957102865454767542295 2279935654298182151313443)
                ·
                  refine ⟨3419903481447273226970165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279935654298182151313443 3419903481447273226970165)
                  ·
                    refine ⟨320615951385681865028453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3419903481447273226970165 320615951385681865028453)
                    ·
                      rfl

theorem cell22_936596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_936596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936596 prefixEnd_936596 := by exact prefixLift 936596
  have htrace : WordTrace (prefixWord ++ tailWord_936596) baseStart_936596 baseEnd_936596 := by
    simpa [prefixWord, tailWord_936596, baseEnd_936596] using wordTrace_append hprefix tailTrace_936596
  have hstable : (prefixWord ++ tailWord_936596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936596).length < 2 ^ (prefixWord ++ tailWord_936596).sum := by decide
  have hdescent : baseEnd_936596 < baseStart_936596 := by decide
  rcases family_descends (prefixWord ++ tailWord_936596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936609 : List Nat := [1, 2, 3, 3, 3, 1, 1, 8]
def baseStart_936609 : Nat := 118140960795 + 936609 * 2 ^ 59
def prefixEnd_936609 : Nat := 4983230072969 + 3 ^ 40 * 936609 * 2
def baseEnd_936609 : Nat := 35624489061261573828157

theorem tailTrace_936609 : CollatzResearch.WordTrace tailWord_936609 prefixEnd_936609 35624489061261573828157 := by
  unfold tailWord_936609
  simp only [CollatzResearch.WordTrace]
  refine ⟨34160936663833027927236881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22773957775888685284824587 34160936663833027927236881)
  ·
    refine ⟨25620702497874770945427661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34160936663833027927236881 25620702497874770945427661)
    ·
      refine ⟨9607763436703039104535373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25620702497874770945427661 9607763436703039104535373)
      ·
        refine ⟨3602911288763639664200765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9607763436703039104535373 3602911288763639664200765)
        ·
          refine ⟨1351091733286364874075287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3602911288763639664200765 1351091733286364874075287)
          ·
            refine ⟨2026637599929547311112931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351091733286364874075287 2026637599929547311112931)
            ·
              refine ⟨3039956399894320966669397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026637599929547311112931 3039956399894320966669397)
              ·
                refine ⟨35624489061261573828157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3039956399894320966669397 35624489061261573828157)
                ·
                  rfl

theorem cell22_936609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 8].length) (baseStart_936609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936609 prefixEnd_936609 := by exact prefixLift 936609
  have htrace : WordTrace (prefixWord ++ tailWord_936609) baseStart_936609 baseEnd_936609 := by
    simpa [prefixWord, tailWord_936609, baseEnd_936609] using wordTrace_append hprefix tailTrace_936609
  have hstable : (prefixWord ++ tailWord_936609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936609).length < 2 ^ (prefixWord ++ tailWord_936609).sum := by decide
  have hdescent : baseEnd_936609 < baseStart_936609 := by decide
  rcases family_descends (prefixWord ++ tailWord_936609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936615 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 4]
def baseStart_936615 : Nat := 118140960795 + 936615 * 2 ^ 59
def prefixEnd_936615 : Nat := 4983230072969 + 3 ^ 40 * 936615 * 2
def baseEnd_936615 : Nat := 106874151824657382934465

theorem tailTrace_936615 : CollatzResearch.WordTrace tailWord_936615 prefixEnd_936615 106874151824657382934465 := by
  unfold tailWord_936615
  simp only [CollatzResearch.WordTrace]
  refine ⟨34161155501811290951955299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22774103667874193967970199 34161155501811290951955299)
  ·
    refine ⟨51241733252716936427932949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34161155501811290951955299 51241733252716936427932949)
    ·
      refine ⟨2401956246221106395059357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51241733252716936427932949 2401956246221106395059357)
      ·
        refine ⟨900733592332914898147259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2401956246221106395059357 900733592332914898147259)
        ·
          refine ⟨1351100388499372347220889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900733592332914898147259 1351100388499372347220889)
          ·
            refine ⟨1013325291374529260415667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351100388499372347220889 1013325291374529260415667)
            ·
              refine ⟨1519987937061793890623501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013325291374529260415667 1519987937061793890623501)
              ·
                refine ⟨569995476398172708983813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1519987937061793890623501 569995476398172708983813)
                ·
                  refine ⟨106874151824657382934465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569995476398172708983813 106874151824657382934465)
                  ·
                    rfl

theorem cell22_936615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 4].length) (baseStart_936615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936615 prefixEnd_936615 := by exact prefixLift 936615
  have htrace : WordTrace (prefixWord ++ tailWord_936615) baseStart_936615 baseEnd_936615 := by
    simpa [prefixWord, tailWord_936615, baseEnd_936615] using wordTrace_append hprefix tailTrace_936615
  have hstable : (prefixWord ++ tailWord_936615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936615).length < 2 ^ (prefixWord ++ tailWord_936615).sum := by decide
  have hdescent : baseEnd_936615 < baseStart_936615 := by decide
  rcases family_descends (prefixWord ++ tailWord_936615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936729 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_936729 : Nat := 118140960795 + 936729 * 2 ^ 59
def prefixEnd_936729 : Nat := 4983230072969 + 3 ^ 40 * 936729 * 2
def baseEnd_936729 : Nat := 320661480003713851453045

theorem tailTrace_936729 : CollatzResearch.WordTrace tailWord_936729 prefixEnd_936729 320661480003713851453045 := by
  unfold tailWord_936729
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165313423398288421605241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22776875615598858947736827 34165313423398288421605241)
  ·
    refine ⟨25623985067548716316203931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34165313423398288421605241 25623985067548716316203931)
    ·
      refine ⟨38435977601323074474305897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25623985067548716316203931 38435977601323074474305897)
      ·
        refine ⟨28826983200992305855729423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38435977601323074474305897 28826983200992305855729423)
        ·
          refine ⟨43240474801488458783594135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28826983200992305855729423 43240474801488458783594135)
          ·
            refine ⟨64860712202232688175391203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43240474801488458783594135 64860712202232688175391203)
            ·
              refine ⟨97291068303349032263086805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64860712202232688175391203 97291068303349032263086805)
              ·
                refine ⟨2280259413359742943666097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97291068303349032263086805 2280259413359742943666097)
                ·
                  refine ⟨1710194560019807207749573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280259413359742943666097 1710194560019807207749573)
                  ·
                    refine ⟨320661480003713851453045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710194560019807207749573 320661480003713851453045)
                    ·
                      rfl

theorem cell22_936729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_936729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936729 prefixEnd_936729 := by exact prefixLift 936729
  have htrace : WordTrace (prefixWord ++ tailWord_936729) baseStart_936729 baseEnd_936729 := by
    simpa [prefixWord, tailWord_936729, baseEnd_936729] using wordTrace_append hprefix tailTrace_936729
  have hstable : (prefixWord ++ tailWord_936729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936729).length < 2 ^ (prefixWord ++ tailWord_936729).sum := by decide
  have hdescent : baseEnd_936729 < baseStart_936729 := by decide
  rcases family_descends (prefixWord ++ tailWord_936729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936744 : List Nat := [2, 1, 5, 1, 1, 1, 11]
def baseStart_936744 : Nat := 118140960795 + 936744 * 2 ^ 59
def prefixEnd_936744 : Nat := 4983230072969 + 3 ^ 40 * 936744 * 2
def baseEnd_936744 : Nat := 11876541289268844901037

theorem tailTrace_936744 : CollatzResearch.WordTrace tailWord_936744 prefixEnd_936744 11876541289268844901037 := by
  unfold tailWord_936744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17082930259171972991700643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22777240345562630655600857 17082930259171972991700643)
  ·
    refine ⟨25624395388757959487550965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17082930259171972991700643 25624395388757959487550965)
    ·
      refine ⟨2402287067696058701957903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25624395388757959487550965 2402287067696058701957903)
      ·
        refine ⟨3603430601544088052936855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402287067696058701957903 3603430601544088052936855)
        ·
          refine ⟨5405145902316132079405283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603430601544088052936855 5405145902316132079405283)
          ·
            refine ⟨8107718853474198119107925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405145902316132079405283 8107718853474198119107925)
            ·
              refine ⟨11876541289268844901037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8107718853474198119107925 11876541289268844901037)
              ·
                rfl

theorem cell22_936744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 11].length) (baseStart_936744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936744 prefixEnd_936744 := by exact prefixLift 936744
  have htrace : WordTrace (prefixWord ++ tailWord_936744) baseStart_936744 baseEnd_936744 := by
    simpa [prefixWord, tailWord_936744, baseEnd_936744] using wordTrace_append hprefix tailTrace_936744
  have hstable : (prefixWord ++ tailWord_936744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936744).length < 2 ^ (prefixWord ++ tailWord_936744).sum := by decide
  have hdescent : baseEnd_936744 < baseStart_936744 := by decide
  rcases family_descends (prefixWord ++ tailWord_936744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936765 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_936765 : Nat := 118140960795 + 936765 * 2 ^ 59
def prefixEnd_936765 : Nat := 4983230072969 + 3 ^ 40 * 936765 * 2
def baseEnd_936765 : Nat := 320673803539421757552935

theorem tailTrace_936765 : CollatzResearch.WordTrace tailWord_936765 prefixEnd_936765 320673803539421757552935 := by
  unfold tailWord_936765
  simp only [CollatzResearch.WordTrace]
  refine ⟨34166626451267866569915749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22777750967511911046610499 34166626451267866569915749)
  ·
    refine ⟨6406242459612724981859203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34166626451267866569915749 6406242459612724981859203)
    ·
      refine ⟨9609363689419087472788805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406242459612724981859203 9609363689419087472788805)
      ·
        refine ⟨1801755691766078901147901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9609363689419087472788805 1801755691766078901147901)
        ·
          refine ⟨675658384412279587930463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1801755691766078901147901 675658384412279587930463)
          ·
            refine ⟨1013487576618419381895695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675658384412279587930463 1013487576618419381895695)
            ·
              refine ⟨1520231364927629072843543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013487576618419381895695 1520231364927629072843543)
              ·
                refine ⟨2280347047391443609265315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520231364927629072843543 2280347047391443609265315)
                ·
                  refine ⟨3420520571087165413897973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280347047391443609265315 3420520571087165413897973)
                  ·
                    refine ⟨320673803539421757552935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3420520571087165413897973 320673803539421757552935)
                    ·
                      rfl

theorem cell22_936765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_936765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936765 prefixEnd_936765 := by exact prefixLift 936765
  have htrace : WordTrace (prefixWord ++ tailWord_936765) baseStart_936765 baseEnd_936765 := by
    simpa [prefixWord, tailWord_936765, baseEnd_936765] using wordTrace_append hprefix tailTrace_936765
  have hstable : (prefixWord ++ tailWord_936765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936765).length < 2 ^ (prefixWord ++ tailWord_936765).sum := by decide
  have hdescent : baseEnd_936765 < baseStart_936765 := by decide
  rcases family_descends (prefixWord ++ tailWord_936765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936776 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_936776 : Nat := 118140960795 + 936776 * 2 ^ 59
def prefixEnd_936776 : Nat := 4983230072969 + 3 ^ 40 * 936776 * 2
def baseEnd_936776 : Nat := 320677569064221395527901

theorem tailTrace_936776 : CollatzResearch.WordTrace tailWord_936776 prefixEnd_936776 320677569064221395527901 := by
  unfold tailWord_936776
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083513827114007724283091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22778018436152010299044121 17083513827114007724283091)
  ·
    refine ⟨25625270740671011586424637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17083513827114007724283091 25625270740671011586424637)
    ·
      refine ⟨9609476527751629344909239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25625270740671011586424637 9609476527751629344909239)
      ·
        refine ⟨14414214791627444017363859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609476527751629344909239 14414214791627444017363859)
        ·
          refine ⟨21621322187441166026045789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14414214791627444017363859 21621322187441166026045789)
          ·
            refine ⟨8107995820290437259767171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21621322187441166026045789 8107995820290437259767171)
            ·
              refine ⟨12161993730435655889650757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107995820290437259767171 12161993730435655889650757)
              ·
                refine ⟨2280373824456685479309517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12161993730435655889650757 2280373824456685479309517)
                ·
                  refine ⟨855140184171257054741069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2280373824456685479309517 855140184171257054741069)
                  ·
                    refine ⟨320677569064221395527901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855140184171257054741069 320677569064221395527901)
                    ·
                      rfl

theorem cell22_936776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_936776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936776 prefixEnd_936776 := by exact prefixLift 936776
  have htrace : WordTrace (prefixWord ++ tailWord_936776) baseStart_936776 baseEnd_936776 := by
    simpa [prefixWord, tailWord_936776, baseEnd_936776] using wordTrace_append hprefix tailTrace_936776
  have hstable : (prefixWord ++ tailWord_936776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936776).length < 2 ^ (prefixWord ++ tailWord_936776).sum := by decide
  have hdescent : baseEnd_936776 < baseStart_936776 := by decide
  rcases family_descends (prefixWord ++ tailWord_936776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936789 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 9]
def baseStart_936789 : Nat := 118140960795 + 936789 * 2 ^ 59
def prefixEnd_936789 : Nat := 4983230072969 + 3 ^ 40 * 936789 * 2
def baseEnd_936789 : Nat := 106894006409964564984287

theorem tailTrace_936789 : CollatzResearch.WordTrace tailWord_936789 prefixEnd_936789 106894006409964564984287 := by
  unfold tailWord_936789
  simp only [CollatzResearch.WordTrace]
  refine ⟨34167501803180918668789421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22778334535453945779192947 34167501803180918668789421)
  ·
    refine ⟨12812813176192844500796033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34167501803180918668789421 12812813176192844500796033)
    ·
      refine ⟨9609609882144633375597025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12812813176192844500796033 9609609882144633375597025)
      ·
        refine ⟨7207207411608475031697769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9609609882144633375597025 7207207411608475031697769)
        ·
          refine ⟨5405405558706356273773327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207207411608475031697769 5405405558706356273773327)
          ·
            refine ⟨8108108338059534410659991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405405558706356273773327 8108108338059534410659991)
            ·
              refine ⟨12162162507089301615989987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108108338059534410659991 12162162507089301615989987)
              ·
                refine ⟨18243243760633952423984981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12162162507089301615989987 18243243760633952423984981)
                ·
                  refine ⟨106894006409964564984287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18243243760633952423984981 106894006409964564984287)
                  ·
                    rfl

theorem cell22_936789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_936789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936789 prefixEnd_936789 := by exact prefixLift 936789
  have htrace : WordTrace (prefixWord ++ tailWord_936789) baseStart_936789 baseEnd_936789 := by
    simpa [prefixWord, tailWord_936789, baseEnd_936789] using wordTrace_append hprefix tailTrace_936789
  have hstable : (prefixWord ++ tailWord_936789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936789).length < 2 ^ (prefixWord ++ tailWord_936789).sum := by decide
  have hdescent : baseEnd_936789 < baseStart_936789 := by decide
  rcases family_descends (prefixWord ++ tailWord_936789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936868 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 4]
def baseStart_936868 : Nat := 118140960795 + 936868 * 2 ^ 59
def prefixEnd_936868 : Nat := 4983230072969 + 3 ^ 40 * 936868 * 2
def baseEnd_936868 : Nat := 106903020848121274075873

theorem tailTrace_936868 : CollatzResearch.WordTrace tailWord_936868 prefixEnd_936868 106903020848121274075873 := by
  unfold tailWord_936868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085191584947357580457629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22780255446596476773943505 17085191584947357580457629)
  ·
    refine ⟨6406946844355259092671611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17085191584947357580457629 6406946844355259092671611)
    ·
      refine ⟨9610420266532888639007417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406946844355259092671611 9610420266532888639007417)
      ·
        refine ⟨7207815199899666479255563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9610420266532888639007417 7207815199899666479255563)
        ·
          refine ⟨10811722799849499718883345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207815199899666479255563 10811722799849499718883345)
          ·
            refine ⟨8108792099887124789162509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10811722799849499718883345 8108792099887124789162509)
            ·
              refine ⟨3040797037457671795935941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8108792099887124789162509 3040797037457671795935941)
              ·
                refine ⟨570149444523313461737989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3040797037457671795935941 570149444523313461737989)
                ·
                  refine ⟨106903020848121274075873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570149444523313461737989 106903020848121274075873)
                  ·
                    rfl

theorem cell22_936868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_936868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936868 prefixEnd_936868 := by exact prefixLift 936868
  have htrace : WordTrace (prefixWord ++ tailWord_936868) baseStart_936868 baseEnd_936868 := by
    simpa [prefixWord, tailWord_936868, baseEnd_936868] using wordTrace_append hprefix tailTrace_936868
  have hstable : (prefixWord ++ tailWord_936868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936868).length < 2 ^ (prefixWord ++ tailWord_936868).sum := by decide
  have hdescent : baseEnd_936868 < baseStart_936868 := by decide
  rcases family_descends (prefixWord ++ tailWord_936868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936879 : List Nat := [1, 1, 2, 1, 2, 2, 2, 11]
def baseStart_936879 : Nat := 118140960795 + 936879 * 2 ^ 59
def prefixEnd_936879 : Nat := 4983230072969 + 3 ^ 40 * 936879 * 2
def baseEnd_936879 : Nat := 35634758674351495578065

theorem tailTrace_936879 : CollatzResearch.WordTrace tailWord_936879 prefixEnd_936879 35634758674351495578065 := by
  unfold tailWord_936879
  simp only [CollatzResearch.WordTrace]
  refine ⟨34170784372854864039565691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22780522915236576026377127 34170784372854864039565691)
  ·
    refine ⟨51256176559282296059348537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34170784372854864039565691 51256176559282296059348537)
    ·
      refine ⟨38442132419461722044511403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51256176559282296059348537 38442132419461722044511403)
      ·
        refine ⟨57663198629192583066767105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38442132419461722044511403 57663198629192583066767105)
        ·
          refine ⟨43247398971894437300075329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57663198629192583066767105 43247398971894437300075329)
          ·
            refine ⟨32435549228920827975056497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43247398971894437300075329 32435549228920827975056497)
            ·
              refine ⟨24326661921690620981292373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32435549228920827975056497 24326661921690620981292373)
              ·
                refine ⟨35634758674351495578065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24326661921690620981292373 35634758674351495578065)
                ·
                  rfl

theorem cell22_936879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 11].length) (baseStart_936879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936879 prefixEnd_936879 := by exact prefixLift 936879
  have htrace : WordTrace (prefixWord ++ tailWord_936879) baseStart_936879 baseEnd_936879 := by
    simpa [prefixWord, tailWord_936879, baseEnd_936879] using wordTrace_append hprefix tailTrace_936879
  have hstable : (prefixWord ++ tailWord_936879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936879).length < 2 ^ (prefixWord ++ tailWord_936879).sum := by decide
  have hdescent : baseEnd_936879 < baseStart_936879 := by decide
  rcases family_descends (prefixWord ++ tailWord_936879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936917 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_936917 : Nat := 118140960795 + 936917 * 2 ^ 59
def prefixEnd_936917 : Nat := 4983230072969 + 3 ^ 40 * 936917 * 2
def baseEnd_936917 : Nat := 320725836245744027752469

theorem tailTrace_936917 : CollatzResearch.WordTrace tailWord_936917 prefixEnd_936917 320725836245744027752469 := by
  unfold tailWord_936917
  simp only [CollatzResearch.WordTrace]
  refine ⟨34172170346717196529449005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22781446897811464352966003 34172170346717196529449005)
  ·
    refine ⟨12814563880018948698543377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34172170346717196529449005 12814563880018948698543377)
    ·
      refine ⟨9610922910014211523907533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12814563880018948698543377 9610922910014211523907533)
      ·
        refine ⟨3604096091255329321465325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9610922910014211523907533 3604096091255329321465325)
        ·
          refine ⟨1351536034220748495549497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3604096091255329321465325 1351536034220748495549497)
          ·
            refine ⟨1013652025665561371662123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351536034220748495549497 1013652025665561371662123)
            ·
              refine ⟨1520478038498342057493185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013652025665561371662123 1520478038498342057493185)
              ·
                refine ⟨1140358528873756543119889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520478038498342057493185 1140358528873756543119889)
                ·
                  refine ⟨855268896655317407339917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1140358528873756543119889 855268896655317407339917)
                  ·
                    refine ⟨320725836245744027752469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855268896655317407339917 320725836245744027752469)
                    ·
                      rfl

theorem cell22_936917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_936917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_936917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_936917 prefixEnd_936917 := by exact prefixLift 936917
  have htrace : WordTrace (prefixWord ++ tailWord_936917) baseStart_936917 baseEnd_936917 := by
    simpa [prefixWord, tailWord_936917, baseEnd_936917] using wordTrace_append hprefix tailTrace_936917
  have hstable : (prefixWord ++ tailWord_936917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936917).length < 2 ^ (prefixWord ++ tailWord_936917).sum := by decide
  have hdescent : baseEnd_936917 < baseStart_936917 := by decide
  rcases family_descends (prefixWord ++ tailWord_936917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937018 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_937018 : Nat := 118140960795 + 937018 * 2 ^ 59
def prefixEnd_937018 : Nat := 4983230072969 + 3 ^ 40 * 937018 * 2
def baseEnd_937018 : Nat := 320760410609813430977159

theorem tailTrace_937018 : CollatzResearch.WordTrace tailWord_937018 prefixEnd_937018 320760410609813430977159 := by
  unfold tailWord_937018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543963529837822694718927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22783902746234193852583805 8543963529837822694718927)
  ·
    refine ⟨12815945294756734042078391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8543963529837822694718927 12815945294756734042078391)
    ·
      refine ⟨19223917942135101063117587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12815945294756734042078391 19223917942135101063117587)
      ·
        refine ⟨28835876913202651594676381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19223917942135101063117587 28835876913202651594676381)
        ·
          refine ⟨10813453842450994348003643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28835876913202651594676381 10813453842450994348003643)
          ·
            refine ⟨16220180763676491522005465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10813453842450994348003643 16220180763676491522005465)
            ·
              refine ⟨12165135572757368641504099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16220180763676491522005465 12165135572757368641504099)
              ·
                refine ⟨18247703359136052962256149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12165135572757368641504099 18247703359136052962256149)
                ·
                  refine ⟨855361094959502482605757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18247703359136052962256149 855361094959502482605757)
                  ·
                    refine ⟨320760410609813430977159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855361094959502482605757 320760410609813430977159)
                    ·
                      rfl

theorem cell22_937018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_937018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937018 prefixEnd_937018 := by exact prefixLift 937018
  have htrace : WordTrace (prefixWord ++ tailWord_937018) baseStart_937018 baseEnd_937018 := by
    simpa [prefixWord, tailWord_937018, baseEnd_937018] using wordTrace_append hprefix tailTrace_937018
  have hstable : (prefixWord ++ tailWord_937018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937018).length < 2 ^ (prefixWord ++ tailWord_937018).sum := by decide
  have hdescent : baseEnd_937018 < baseStart_937018 := by decide
  rcases family_descends (prefixWord ++ tailWord_937018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937031 : List Nat := [1, 1, 4, 1, 3, 12]
def baseStart_937031 : Nat := 118140960795 + 937031 * 2 ^ 59
def prefixEnd_937031 : Nat := 4983230072969 + 3 ^ 40 * 937031 * 2
def baseEnd_937031 : Nat := 3960060009573897906199

theorem tailTrace_937031 : CollatzResearch.WordTrace tailWord_937031 prefixEnd_937031 3960060009573897906199 := by
  unfold tailWord_937031
  simp only [CollatzResearch.WordTrace]
  refine ⟨34176328268304193999098947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22784218845536129332732631 34176328268304193999098947)
  ·
    refine ⟨51264492402456290998648421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34176328268304193999098947 51264492402456290998648421)
    ·
      refine ⟨9612092325460554562246579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51264492402456290998648421 9612092325460554562246579)
      ·
        refine ⟨14418138488190831843369869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612092325460554562246579 14418138488190831843369869)
        ·
          refine ⟨5406801933071561941263701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14418138488190831843369869 5406801933071561941263701)
          ·
            refine ⟨3960060009573897906199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5406801933071561941263701 3960060009573897906199)
            ·
              rfl

theorem cell22_937031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 12].length) (baseStart_937031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937031 prefixEnd_937031 := by exact prefixLift 937031
  have htrace : WordTrace (prefixWord ++ tailWord_937031) baseStart_937031 baseEnd_937031 := by
    simpa [prefixWord, tailWord_937031, baseEnd_937031] using wordTrace_append hprefix tailTrace_937031
  have hstable : (prefixWord ++ tailWord_937031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937031).length < 2 ^ (prefixWord ++ tailWord_937031).sum := by decide
  have hdescent : baseEnd_937031 < baseStart_937031 := by decide
  rcases family_descends (prefixWord ++ tailWord_937031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937037 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 4]
def baseStart_937037 : Nat := 118140960795 + 937037 * 2 ^ 59
def prefixEnd_937037 : Nat := 4983230072969 + 3 ^ 40 * 937037 * 2
def baseEnd_937037 : Nat := 106922304899367904917367

theorem tailTrace_937037 : CollatzResearch.WordTrace tailWord_937037 prefixEnd_937037 106922304899367904917367 := by
  unfold tailWord_937037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34176547106282457023817365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22784364737521638015878243 34176547106282457023817365)
  ·
    refine ⟨1602025645606990172991439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34176547106282457023817365 1602025645606990172991439)
    ·
      refine ⟨2403038468410485259487159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602025645606990172991439 2403038468410485259487159)
      ·
        refine ⟨3604557702615727889230739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403038468410485259487159 3604557702615727889230739)
        ·
          refine ⟨5406836553923591833846109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604557702615727889230739 5406836553923591833846109)
          ·
            refine ⟨2027563707721346937692291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5406836553923591833846109 2027563707721346937692291)
            ·
              refine ⟨3041345561582020406538437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027563707721346937692291 3041345561582020406538437)
              ·
                refine ⟨570252292796628826225957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3041345561582020406538437 570252292796628826225957)
                ·
                  refine ⟨106922304899367904917367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570252292796628826225957 106922304899367904917367)
                  ·
                    rfl

theorem cell22_937037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_937037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937037 prefixEnd_937037 := by exact prefixLift 937037
  have htrace : WordTrace (prefixWord ++ tailWord_937037) baseStart_937037 baseEnd_937037 := by
    simpa [prefixWord, tailWord_937037, baseEnd_937037] using wordTrace_append hprefix tailTrace_937037
  have hstable : (prefixWord ++ tailWord_937037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937037).length < 2 ^ (prefixWord ++ tailWord_937037).sum := by decide
  have hdescent : baseEnd_937037 < baseStart_937037 := by decide
  rcases family_descends (prefixWord ++ tailWord_937037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937086 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_937086 : Nat := 118140960795 + 937086 * 2 ^ 59
def prefixEnd_937086 : Nat := 4983230072969 + 3 ^ 40 * 937086 * 2
def baseEnd_937086 : Nat := 320783688399483920276951

theorem tailTrace_937086 : CollatzResearch.WordTrace tailWord_937086 prefixEnd_937086 320783688399483920276951 := by
  unfold tailWord_937086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272291785388117299043889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22785556188736625594900741 4272291785388117299043889)
  ·
    refine ⟨3204218839041087974282917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4272291785388117299043889 3204218839041087974282917)
    ·
      refine ⟨600791032320203995178047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3204218839041087974282917 600791032320203995178047)
      ·
        refine ⟨901186548480305992767071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600791032320203995178047 901186548480305992767071)
        ·
          refine ⟨1351779822720458989150607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901186548480305992767071 1351779822720458989150607)
          ·
            refine ⟨2027669734080688483725911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351779822720458989150607 2027669734080688483725911)
            ·
              refine ⟨3041504601121032725588867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027669734080688483725911 3041504601121032725588867)
              ·
                refine ⟨4562256901681549088383301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041504601121032725588867 4562256901681549088383301)
                ·
                  refine ⟨855423169065290454071869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4562256901681549088383301 855423169065290454071869)
                  ·
                    refine ⟨320783688399483920276951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855423169065290454071869 320783688399483920276951)
                    ·
                      rfl

theorem cell22_937086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_937086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937086 prefixEnd_937086 := by exact prefixLift 937086
  have htrace : WordTrace (prefixWord ++ tailWord_937086) baseStart_937086 baseEnd_937086 := by
    simpa [prefixWord, tailWord_937086, baseEnd_937086] using wordTrace_append hprefix tailTrace_937086
  have hstable : (prefixWord ++ tailWord_937086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937086).length < 2 ^ (prefixWord ++ tailWord_937086).sum := by decide
  have hdescent : baseEnd_937086 < baseStart_937086 := by decide
  rcases family_descends (prefixWord ++ tailWord_937086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937097 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 1, 3]
def baseStart_937097 : Nat := 118140960795 + 937097 * 2 ^ 59
def prefixEnd_937097 : Nat := 4983230072969 + 3 ^ 40 * 937097 * 2
def baseEnd_937097 : Nat := 320787453924283558251917

theorem tailTrace_937097 : CollatzResearch.WordTrace tailWord_937097 prefixEnd_937097 320787453924283558251917 := by
  unfold tailWord_937097
  simp only [CollatzResearch.WordTrace]
  refine ⟨34178735486065087271001545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22785823657376724847334363 34178735486065087271001545)
  ·
    refine ⟨25634051614548815453251159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34178735486065087271001545 25634051614548815453251159)
    ·
      refine ⟨38451077421823223179876739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25634051614548815453251159 38451077421823223179876739)
      ·
        refine ⟨57676616132734834769815109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38451077421823223179876739 57676616132734834769815109)
        ·
          refine ⟨10814365524887781519340333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57676616132734834769815109 10814365524887781519340333)
          ·
            refine ⟨4055387071832918069752625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10814365524887781519340333 4055387071832918069752625)
            ·
              refine ⟨3041540303874688552314469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055387071832918069752625 3041540303874688552314469)
              ·
                refine ⟨570288806976504103558963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3041540303874688552314469 570288806976504103558963)
                ·
                  refine ⟨855433210464756155338445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570288806976504103558963 855433210464756155338445)
                  ·
                    refine ⟨320787453924283558251917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855433210464756155338445 320787453924283558251917)
                    ·
                      rfl

theorem cell22_937097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_937097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937097 prefixEnd_937097 := by exact prefixLift 937097
  have htrace : WordTrace (prefixWord ++ tailWord_937097) baseStart_937097 baseEnd_937097 := by
    simpa [prefixWord, tailWord_937097, baseEnd_937097] using wordTrace_append hprefix tailTrace_937097
  have hstable : (prefixWord ++ tailWord_937097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937097).length < 2 ^ (prefixWord ++ tailWord_937097).sum := by decide
  have hdescent : baseEnd_937097 < baseStart_937097 := by decide
  rcases family_descends (prefixWord ++ tailWord_937097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937123 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 3, 4]
def baseStart_937123 : Nat := 118140960795 + 937123 * 2 ^ 59
def prefixEnd_937123 : Nat := 4983230072969 + 3 ^ 40 * 937123 * 2
def baseEnd_937123 : Nat := 320796354255628157101837

theorem tailTrace_937123 : CollatzResearch.WordTrace tailWord_937123 prefixEnd_937123 320796354255628157101837 := by
  unfold tailWord_937123
  simp only [CollatzResearch.WordTrace]
  refine ⟨34179683783970893711448023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22786455855980595807632015 34179683783970893711448023)
  ·
    refine ⟨51269525675956340567172035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34179683783970893711448023 51269525675956340567172035)
    ·
      refine ⟨76904288513934510850758053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51269525675956340567172035 76904288513934510850758053)
      ·
        refine ⟨14419554096362720784517135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76904288513934510850758053 14419554096362720784517135)
        ·
          refine ⟨21629331144544081176775703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14419554096362720784517135 21629331144544081176775703)
          ·
            refine ⟨32443996716816121765163555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21629331144544081176775703 32443996716816121765163555)
            ·
              refine ⟨48665995075224182647745333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32443996716816121765163555 48665995075224182647745333)
              ·
                refine ⟨4562437038302267123226125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48665995075224182647745333 4562437038302267123226125)
                ·
                  refine ⟨1710913889363350171209797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4562437038302267123226125 1710913889363350171209797)
                  ·
                    refine ⟨320796354255628157101837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710913889363350171209797 320796354255628157101837)
                    ·
                      rfl

theorem cell22_937123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_937123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937123 prefixEnd_937123 := by exact prefixLift 937123
  have htrace : WordTrace (prefixWord ++ tailWord_937123) baseStart_937123 baseEnd_937123 := by
    simpa [prefixWord, tailWord_937123, baseEnd_937123] using wordTrace_append hprefix tailTrace_937123
  have hstable : (prefixWord ++ tailWord_937123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937123).length < 2 ^ (prefixWord ++ tailWord_937123).sum := by decide
  have hdescent : baseEnd_937123 < baseStart_937123 := by decide
  rcases family_descends (prefixWord ++ tailWord_937123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937170 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_937170 : Nat := 118140960795 + 937170 * 2 ^ 59
def prefixEnd_937170 : Nat := 4983230072969 + 3 ^ 40 * 937170 * 2
def baseEnd_937170 : Nat := 320812443316135701176693

theorem tailTrace_937170 : CollatzResearch.WordTrace tailWord_937170 prefixEnd_937170 320812443316135701176693 := by
  unfold tailWord_937170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545349503700155184602241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22787598676533747158939309 8545349503700155184602241)
  ·
    refine ⟨6409012127775116388451681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8545349503700155184602241 6409012127775116388451681)
    ·
      refine ⟨4806759095831337291338761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6409012127775116388451681 4806759095831337291338761)
      ·
        refine ⟨3605069321873502968504071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4806759095831337291338761 3605069321873502968504071)
        ·
          refine ⟨5407603982810254452756107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605069321873502968504071 5407603982810254452756107)
          ·
            refine ⟨8111405974215381679134161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407603982810254452756107 8111405974215381679134161)
            ·
              refine ⟨6083554480661536259350621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8111405974215381679134161 6083554480661536259350621)
              ·
                refine ⟨2281332930248076097256483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6083554480661536259350621 2281332930248076097256483)
                ·
                  refine ⟨3421999395372114145884725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281332930248076097256483 3421999395372114145884725)
                  ·
                    refine ⟨320812443316135701176693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3421999395372114145884725 320812443316135701176693)
                    ·
                      rfl

theorem cell22_937170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_937170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937170 prefixEnd_937170 := by exact prefixLift 937170
  have htrace : WordTrace (prefixWord ++ tailWord_937170) baseStart_937170 baseEnd_937170 := by
    simpa [prefixWord, tailWord_937170, baseEnd_937170] using wordTrace_append hprefix tailTrace_937170
  have hstable : (prefixWord ++ tailWord_937170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937170).length < 2 ^ (prefixWord ++ tailWord_937170).sum := by decide
  have hdescent : baseEnd_937170 < baseStart_937170 := by decide
  rcases family_descends (prefixWord ++ tailWord_937170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937174 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_937174 : Nat := 118140960795 + 937174 * 2 ^ 59
def prefixEnd_937174 : Nat := 4983230072969 + 3 ^ 40 * 937174 * 2
def baseEnd_937174 : Nat := 320813812597881024076681

theorem tailTrace_937174 : CollatzResearch.WordTrace tailWord_937174 prefixEnd_937174 320813812597881024076681 := by
  unfold tailWord_937174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136346494174133088847161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22787695937857419614369717 2136346494174133088847161)
  ·
    refine ⟨1602259870630599816635371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2136346494174133088847161 1602259870630599816635371)
    ·
      refine ⟨2403389805945899724953057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602259870630599816635371 2403389805945899724953057)
      ·
        refine ⟨1802542354459424793714793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403389805945899724953057 1802542354459424793714793)
        ·
          refine ⟨1351906765844568595286095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802542354459424793714793 1351906765844568595286095)
          ·
            refine ⟨2027860148766852892929143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351906765844568595286095 2027860148766852892929143)
            ·
              refine ⟨3041790223150279339393715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027860148766852892929143 3041790223150279339393715)
              ·
                refine ⟨4562685334725419009090573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041790223150279339393715 4562685334725419009090573)
                ·
                  refine ⟨1711007000522032128408965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4562685334725419009090573 1711007000522032128408965)
                  ·
                    refine ⟨320813812597881024076681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1711007000522032128408965 320813812597881024076681)
                    ·
                      rfl

theorem cell22_937174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_937174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937174 prefixEnd_937174 := by exact prefixLift 937174
  have htrace : WordTrace (prefixWord ++ tailWord_937174) baseStart_937174 baseEnd_937174 := by
    simpa [prefixWord, tailWord_937174, baseEnd_937174] using wordTrace_append hprefix tailTrace_937174
  have hstable : (prefixWord ++ tailWord_937174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937174).length < 2 ^ (prefixWord ++ tailWord_937174).sum := by decide
  have hdescent : baseEnd_937174 < baseStart_937174 := by decide
  rcases family_descends (prefixWord ++ tailWord_937174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937183 : List Nat := [1, 1, 2, 3, 2, 1, 4, 8]
def baseStart_937183 : Nat := 118140960795 + 937183 * 2 ^ 59
def prefixEnd_937183 : Nat := 4983230072969 + 3 ^ 40 * 937183 * 2
def baseEnd_937183 : Nat := 35646321497978666733517

theorem tailTrace_937183 : CollatzResearch.WordTrace tailWord_937183 prefixEnd_937183 35646321497978666733517 := by
  unfold tailWord_937183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34181872163753523958632203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22787914775835682639088135 34181872163753523958632203)
  ·
    refine ⟨51272808245630285937948305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34181872163753523958632203 51272808245630285937948305)
    ·
      refine ⟨38454606184222714453461229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51272808245630285937948305 38454606184222714453461229)
      ·
        refine ⟨14420477319083517920047961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38454606184222714453461229 14420477319083517920047961)
        ·
          refine ⟨10815357989312638440035971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14420477319083517920047961 10815357989312638440035971)
          ·
            refine ⟨16223036983968957660053957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10815357989312638440035971 16223036983968957660053957)
            ·
              refine ⟨3041819434494179561260117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16223036983968957660053957 3041819434494179561260117)
              ·
                refine ⟨35646321497978666733517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3041819434494179561260117 35646321497978666733517)
                ·
                  rfl

theorem cell22_937183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 8].length) (baseStart_937183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937183 prefixEnd_937183 := by exact prefixLift 937183
  have htrace : WordTrace (prefixWord ++ tailWord_937183) baseStart_937183 baseEnd_937183 := by
    simpa [prefixWord, tailWord_937183, baseEnd_937183] using wordTrace_append hprefix tailTrace_937183
  have hstable : (prefixWord ++ tailWord_937183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937183).length < 2 ^ (prefixWord ++ tailWord_937183).sum := by decide
  have hdescent : baseEnd_937183 < baseStart_937183 := by decide
  rcases family_descends (prefixWord ++ tailWord_937183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937185 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_937185 : Nat := 118140960795 + 937185 * 2 ^ 59
def prefixEnd_937185 : Nat := 4983230072969 + 3 ^ 40 * 937185 * 2
def baseEnd_937185 : Nat := 320817578122680662051647

theorem tailTrace_937185 : CollatzResearch.WordTrace tailWord_937185 prefixEnd_937185 320817578122680662051647 := by
  unfold tailWord_937185
  simp only [CollatzResearch.WordTrace]
  refine ⟨34181945109746278300205009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22787963406497518866803339 34181945109746278300205009)
  ·
    refine ⟨25636458832309708725153757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34181945109746278300205009 25636458832309708725153757)
    ·
      refine ⟨9613672062116140771932659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25636458832309708725153757 9613672062116140771932659)
      ·
        refine ⟨14420508093174211157898989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613672062116140771932659 14420508093174211157898989)
        ·
          refine ⟨5407690534940329184212121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14420508093174211157898989 5407690534940329184212121)
          ·
            refine ⟨4055767901205246888159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407690534940329184212121 4055767901205246888159091)
            ·
              refine ⟨6083651851807870332238637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055767901205246888159091 6083651851807870332238637)
              ·
                refine ⟨2281369444427951374589489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6083651851807870332238637 2281369444427951374589489)
                ·
                  refine ⟨1711027083320963530942117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2281369444427951374589489 1711027083320963530942117)
                  ·
                    refine ⟨320817578122680662051647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1711027083320963530942117 320817578122680662051647)
                    ·
                      rfl

theorem cell22_937185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_937185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937185 prefixEnd_937185 := by exact prefixLift 937185
  have htrace : WordTrace (prefixWord ++ tailWord_937185) baseStart_937185 baseEnd_937185 := by
    simpa [prefixWord, tailWord_937185, baseEnd_937185] using wordTrace_append hprefix tailTrace_937185
  have hstable : (prefixWord ++ tailWord_937185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937185).length < 2 ^ (prefixWord ++ tailWord_937185).sum := by decide
  have hdescent : baseEnd_937185 < baseStart_937185 := by decide
  rcases family_descends (prefixWord ++ tailWord_937185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937243 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_937243 : Nat := 118140960795 + 937243 * 2 ^ 59
def prefixEnd_937243 : Nat := 4983230072969 + 3 ^ 40 * 937243 * 2
def baseEnd_937243 : Nat := 320837432707987844101469

theorem tailTrace_937243 : CollatzResearch.WordTrace tailWord_937243 prefixEnd_937243 320837432707987844101469 := by
  unfold tailWord_937243
  simp only [CollatzResearch.WordTrace]
  refine ⟨34184060543536154205816383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22789373695690769470544255 34184060543536154205816383)
  ·
    refine ⟨51276090815304231308724575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34184060543536154205816383 51276090815304231308724575)
    ·
      refine ⟨76914136222956346963086863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51276090815304231308724575 76914136222956346963086863)
      ·
        refine ⟨115371204334434520444630295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76914136222956346963086863 115371204334434520444630295)
        ·
          refine ⟨173056806501651780666945443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115371204334434520444630295 173056806501651780666945443)
          ·
            refine ⟨259585209752477671000418165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173056806501651780666945443 259585209752477671000418165)
            ·
              refine ⟨24336113414294781656289203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259585209752477671000418165 24336113414294781656289203)
              ·
                refine ⟨36504170121442172484433805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24336113414294781656289203 36504170121442172484433805)
                ·
                  refine ⟨13689063795540814681662677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36504170121442172484433805 13689063795540814681662677)
                  ·
                    refine ⟨320837432707987844101469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13689063795540814681662677 320837432707987844101469)
                    ·
                      rfl

theorem cell22_937243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_937243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937243 prefixEnd_937243 := by exact prefixLift 937243
  have htrace : WordTrace (prefixWord ++ tailWord_937243) baseStart_937243 baseEnd_937243 := by
    simpa [prefixWord, tailWord_937243, baseEnd_937243] using wordTrace_append hprefix tailTrace_937243
  have hstable : (prefixWord ++ tailWord_937243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937243).length < 2 ^ (prefixWord ++ tailWord_937243).sum := by decide
  have hdescent : baseEnd_937243 < baseStart_937243 := by decide
  rcases family_descends (prefixWord ++ tailWord_937243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937292 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_937292 : Nat := 118140960795 + 937292 * 2 ^ 59
def prefixEnd_937292 : Nat := 4983230072969 + 3 ^ 40 * 937292 * 2
def baseEnd_937292 : Nat := 320854206409368049626319

theorem tailTrace_937292 : CollatzResearch.WordTrace tailWord_937292 prefixEnd_937292 320854206409368049626319 := by
  unfold tailWord_937292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17092923860179317787175065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22790565146905757049566753 17092923860179317787175065)
  ·
    refine ⟨12819692895134488340381299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17092923860179317787175065 12819692895134488340381299)
    ·
      refine ⟨19229539342701732510571949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12819692895134488340381299 19229539342701732510571949)
      ·
        refine ⟨7211077253513149691464481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19229539342701732510571949 7211077253513149691464481)
        ·
          refine ⟨5408307940134862268598361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7211077253513149691464481 5408307940134862268598361)
          ·
            refine ⟨4056230955101146701448771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5408307940134862268598361 4056230955101146701448771)
            ·
              refine ⟨6084346432651720052173157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056230955101146701448771 6084346432651720052173157)
              ·
                refine ⟨1140814956122197509782467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6084346432651720052173157 1140814956122197509782467)
                ·
                  refine ⟨1711222434183296264673701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140814956122197509782467 1711222434183296264673701)
                  ·
                    refine ⟨320854206409368049626319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1711222434183296264673701 320854206409368049626319)
                    ·
                      rfl

theorem cell22_937292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_937292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937292 prefixEnd_937292 := by exact prefixLift 937292
  have htrace : WordTrace (prefixWord ++ tailWord_937292) baseStart_937292 baseEnd_937292 := by
    simpa [prefixWord, tailWord_937292, baseEnd_937292] using wordTrace_append hprefix tailTrace_937292
  have hstable : (prefixWord ++ tailWord_937292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937292).length < 2 ^ (prefixWord ++ tailWord_937292).sum := by decide
  have hdescent : baseEnd_937292 < baseStart_937292 := by decide
  rcases family_descends (prefixWord ++ tailWord_937292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937305 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_937305 : Nat := 118140960795 + 937305 * 2 ^ 59
def prefixEnd_937305 : Nat := 4983230072969 + 3 ^ 40 * 937305 * 2
def baseEnd_937305 : Nat := 320858656575040349051279

theorem tailTrace_937305 : CollatzResearch.WordTrace tailWord_937305 prefixEnd_937305 320858656575040349051279 := by
  unfold tailWord_937305
  simp only [CollatzResearch.WordTrace]
  refine ⟨34186321869311538794573369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22790881246207692529715579 34186321869311538794573369)
  ·
    refine ⟨25639741401983654095930027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34186321869311538794573369 25639741401983654095930027)
    ·
      refine ⟨38459612102975481143895041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25639741401983654095930027 38459612102975481143895041)
      ·
        refine ⟨28844709077231610857921281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38459612102975481143895041 28844709077231610857921281)
        ·
          refine ⟨21633531807923708143440961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28844709077231610857921281 21633531807923708143440961)
          ·
            refine ⟨16225148855942781107580721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21633531807923708143440961 16225148855942781107580721)
            ·
              refine ⟨12168861641957085830685541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16225148855942781107580721 12168861641957085830685541)
              ·
                refine ⟨2281661557866953593253539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12168861641957085830685541 2281661557866953593253539)
                ·
                  refine ⟨3422492336800430389880309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281661557866953593253539 3422492336800430389880309)
                  ·
                    refine ⟨320858656575040349051279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3422492336800430389880309 320858656575040349051279)
                    ·
                      rfl

theorem cell22_937305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_937305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937305 prefixEnd_937305 := by exact prefixLift 937305
  have htrace : WordTrace (prefixWord ++ tailWord_937305) baseStart_937305 baseEnd_937305 := by
    simpa [prefixWord, tailWord_937305, baseEnd_937305] using wordTrace_append hprefix tailTrace_937305
  have hstable : (prefixWord ++ tailWord_937305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937305).length < 2 ^ (prefixWord ++ tailWord_937305).sum := by decide
  have hdescent : baseEnd_937305 < baseStart_937305 := by decide
  rcases family_descends (prefixWord ++ tailWord_937305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937335 : List Nat := [1, 1, 3, 1, 1, 2, 6, 7]
def baseStart_937335 : Nat := 118140960795 + 937335 * 2 ^ 59
def prefixEnd_937335 : Nat := 4983230072969 + 3 ^ 40 * 937335 * 2
def baseEnd_937335 : Nat := 35652102909792252311243

theorem tailTrace_937335 : CollatzResearch.WordTrace tailWord_937335 prefixEnd_937335 35652102909792252311243 := by
  unfold tailWord_937335
  simp only [CollatzResearch.WordTrace]
  refine ⟨34187416059202853918165459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22791610706135235945443639 34187416059202853918165459)
  ·
    refine ⟨51281124088804280877248189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34187416059202853918165459 51281124088804280877248189)
    ·
      refine ⟨19230421533301605328968071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51281124088804280877248189 19230421533301605328968071)
      ·
        refine ⟨28845632299952407993452107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19230421533301605328968071 28845632299952407993452107)
        ·
          refine ⟨43268448449928611990178161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28845632299952407993452107 43268448449928611990178161)
          ·
            refine ⟨32451336337446458992633621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43268448449928611990178161 32451336337446458992633621)
            ·
              refine ⟨1521156390817802765279701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32451336337446458992633621 1521156390817802765279701)
              ·
                refine ⟨35652102909792252311243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1521156390817802765279701 35652102909792252311243)
                ·
                  rfl

theorem cell22_937335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 7].length) (baseStart_937335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937335 prefixEnd_937335 := by exact prefixLift 937335
  have htrace : WordTrace (prefixWord ++ tailWord_937335) baseStart_937335 baseEnd_937335 := by
    simpa [prefixWord, tailWord_937335, baseEnd_937335] using wordTrace_append hprefix tailTrace_937335
  have hstable : (prefixWord ++ tailWord_937335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937335).length < 2 ^ (prefixWord ++ tailWord_937335).sum := by decide
  have hdescent : baseEnd_937335 < baseStart_937335 := by decide
  rcases family_descends (prefixWord ++ tailWord_937335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937461 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_937461 : Nat := 118140960795 + 937461 * 2 ^ 59
def prefixEnd_937461 : Nat := 4983230072969 + 3 ^ 40 * 937461 * 2
def baseEnd_937461 : Nat := 320912058563107942150801

theorem tailTrace_937461 : CollatzResearch.WordTrace tailWord_937461 prefixEnd_937461 320912058563107942150801 := by
  unfold tailWord_937461
  simp only [CollatzResearch.WordTrace]
  refine ⟨34192011656746377437252237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22794674437830918291501491 34192011656746377437252237)
  ·
    refine ⟨12822004371279891538969589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34192011656746377437252237 12822004371279891538969589)
    ·
      refine ⟨1202062909807489831778399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12822004371279891538969589 1202062909807489831778399)
      ·
        refine ⟨1803094364711234747667599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202062909807489831778399 1803094364711234747667599)
        ·
          refine ⟨2704641547066852121501399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803094364711234747667599 2704641547066852121501399)
          ·
            refine ⟨4056962320600278182252099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704641547066852121501399 4056962320600278182252099)
            ·
              refine ⟨6085443480900417273378149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056962320600278182252099 6085443480900417273378149)
              ·
                refine ⟨1141020652668828238758403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6085443480900417273378149 1141020652668828238758403)
                ·
                  refine ⟨1711530979003242358137605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141020652668828238758403 1711530979003242358137605)
                  ·
                    refine ⟨320912058563107942150801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1711530979003242358137605 320912058563107942150801)
                    ·
                      rfl

theorem cell22_937461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_937461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937461 prefixEnd_937461 := by exact prefixLift 937461
  have htrace : WordTrace (prefixWord ++ tailWord_937461) baseStart_937461 baseEnd_937461 := by
    simpa [prefixWord, tailWord_937461, baseEnd_937461] using wordTrace_append hprefix tailTrace_937461
  have hstable : (prefixWord ++ tailWord_937461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937461).length < 2 ^ (prefixWord ++ tailWord_937461).sum := by decide
  have hdescent : baseEnd_937461 < baseStart_937461 := by decide
  rcases family_descends (prefixWord ++ tailWord_937461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937504 : List Nat := [2, 1, 1, 6, 1, 2, 2, 7]
def baseStart_937504 : Nat := 118140960795 + 937504 * 2 ^ 59
def prefixEnd_937504 : Nat := 4983230072969 + 3 ^ 40 * 937504 * 2
def baseEnd_937504 : Nat := 35658530926874462591741

theorem tailTrace_937504 : CollatzResearch.WordTrace tailWord_937504 prefixEnd_937504 35658530926874462591741 := by
  unfold tailWord_937504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096789997795297890533783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22795719997060397187378377 17096789997795297890533783)
  ·
    refine ⟨25645184996692946835800675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17096789997795297890533783 25645184996692946835800675)
    ·
      refine ⟨38467777495039420253701013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25645184996692946835800675 38467777495039420253701013)
      ·
        refine ⟨1803177070079972824392235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38467777495039420253701013 1803177070079972824392235)
        ·
          refine ⟨2704765605119959236588353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803177070079972824392235 2704765605119959236588353)
          ·
            refine ⟨2028574203839969427441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704765605119959236588353 2028574203839969427441265)
            ·
              refine ⟨1521430652879977070580949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028574203839969427441265 1521430652879977070580949)
              ·
                refine ⟨35658530926874462591741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1521430652879977070580949 35658530926874462591741)
                ·
                  rfl

theorem cell22_937504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_937504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937504 prefixEnd_937504 := by exact prefixLift 937504
  have htrace : WordTrace (prefixWord ++ tailWord_937504) baseStart_937504 baseEnd_937504 := by
    simpa [prefixWord, tailWord_937504, baseEnd_937504] using wordTrace_append hprefix tailTrace_937504
  have hstable : (prefixWord ++ tailWord_937504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937504).length < 2 ^ (prefixWord ++ tailWord_937504).sum := by decide
  have hdescent : baseEnd_937504 < baseStart_937504 := by decide
  rcases family_descends (prefixWord ++ tailWord_937504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937536 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 1, 3]
def baseStart_937536 : Nat := 118140960795 + 937536 * 2 ^ 59
def prefixEnd_937536 : Nat := 4983230072969 + 3 ^ 40 * 937536 * 2
def baseEnd_937536 : Nat := 320937732595832746525571

theorem tailTrace_937536 : CollatzResearch.WordTrace tailWord_937536 prefixEnd_937536 320937732595832746525571 := by
  unfold tailWord_937536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097373565737332623116231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22796498087649776830821641 17097373565737332623116231)
  ·
    refine ⟨25646060348605998934674347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097373565737332623116231 25646060348605998934674347)
    ·
      refine ⟨38469090522908998402011521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25646060348605998934674347 38469090522908998402011521)
      ·
        refine ⟨28851817892181748801508641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38469090522908998402011521 28851817892181748801508641)
        ·
          refine ⟨21638863419136311601131481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28851817892181748801508641 21638863419136311601131481)
          ·
            refine ⟨16229147564352233700848611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21638863419136311601131481 16229147564352233700848611)
            ·
              refine ⟨24343721346528350551272917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16229147564352233700848611 24343721346528350551272917)
              ·
                refine ⟨570555969059258216045459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24343721346528350551272917 570555969059258216045459)
                ·
                  refine ⟨855833953588887324068189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570555969059258216045459 855833953588887324068189)
                  ·
                    refine ⟨320937732595832746525571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855833953588887324068189 320937732595832746525571)
                    ·
                      rfl

theorem cell22_937536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_937536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937536 prefixEnd_937536 := by exact prefixLift 937536
  have htrace : WordTrace (prefixWord ++ tailWord_937536) baseStart_937536 baseEnd_937536 := by
    simpa [prefixWord, tailWord_937536, baseEnd_937536] using wordTrace_append hprefix tailTrace_937536
  have hstable : (prefixWord ++ tailWord_937536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937536).length < 2 ^ (prefixWord ++ tailWord_937536).sum := by decide
  have hdescent : baseEnd_937536 < baseStart_937536 := by decide
  rcases family_descends (prefixWord ++ tailWord_937536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937547 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_937547 : Nat := 118140960795 + 937547 * 2 ^ 59
def prefixEnd_937547 : Nat := 4983230072969 + 3 ^ 40 * 937547 * 2
def baseEnd_937547 : Nat := 320941498120632384500537

theorem tailTrace_937547 : CollatzResearch.WordTrace tailWord_937547 prefixEnd_937547 320941498120632384500537 := by
  unfold tailWord_937547
  simp only [CollatzResearch.WordTrace]
  refine ⟨34195148334434814124882895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22796765556289876083255263 34195148334434814124882895)
  ·
    refine ⟨51292722501652221187324343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34195148334434814124882895 51292722501652221187324343)
    ·
      refine ⟨76939083752478331780986515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51292722501652221187324343 76939083752478331780986515)
      ·
        refine ⟨115408625628717497671479773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76939083752478331780986515 115408625628717497671479773)
        ·
          refine ⟨43278234610769061626804915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115408625628717497671479773 43278234610769061626804915)
          ·
            refine ⟨64917351916153592440207373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43278234610769061626804915 64917351916153592440207373)
            ·
              refine ⟨24344006968557597165077765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64917351916153592440207373 24344006968557597165077765)
              ·
                refine ⟨4564501306604549468452081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24344006968557597165077765 4564501306604549468452081)
                ·
                  refine ⟨3423375979953412101339061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4564501306604549468452081 3423375979953412101339061)
                  ·
                    refine ⟨320941498120632384500537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3423375979953412101339061 320941498120632384500537)
                    ·
                      rfl

theorem cell22_937547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_937547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937547 prefixEnd_937547 := by exact prefixLift 937547
  have htrace : WordTrace (prefixWord ++ tailWord_937547) baseStart_937547 baseEnd_937547 := by
    simpa [prefixWord, tailWord_937547, baseEnd_937547] using wordTrace_append hprefix tailTrace_937547
  have hstable : (prefixWord ++ tailWord_937547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937547).length < 2 ^ (prefixWord ++ tailWord_937547).sum := by decide
  have hdescent : baseEnd_937547 < baseStart_937547 := by decide
  rcases family_descends (prefixWord ++ tailWord_937547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937564 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_937564 : Nat := 118140960795 + 937564 * 2 ^ 59
def prefixEnd_937564 : Nat := 4983230072969 + 3 ^ 40 * 937564 * 2
def baseEnd_937564 : Nat := 320947317568050006825485

theorem tailTrace_937564 : CollatzResearch.WordTrace tailWord_937564 prefixEnd_937564 320947317568050006825485 := by
  unfold tailWord_937564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097884187686613014125873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22797178916915484018834497 17097884187686613014125873)
  ·
    refine ⟨12823413140764959760594405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17097884187686613014125873 12823413140764959760594405)
    ·
      refine ⟨2404389963893429955111451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12823413140764959760594405 2404389963893429955111451)
      ·
        refine ⟨3606584945840144932667177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404389963893429955111451 3606584945840144932667177)
        ·
          refine ⟨2704938709380108699500383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606584945840144932667177 2704938709380108699500383)
          ·
            refine ⟨4057408064070163049250575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704938709380108699500383 4057408064070163049250575)
            ·
              refine ⟨6086112096105244573875863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057408064070163049250575 6086112096105244573875863)
              ·
                refine ⟨9129168144157866860813795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086112096105244573875863 9129168144157866860813795)
                ·
                  refine ⟨13693752216236800291220693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9129168144157866860813795 13693752216236800291220693)
                  ·
                    refine ⟨320947317568050006825485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13693752216236800291220693 320947317568050006825485)
                    ·
                      rfl

theorem cell22_937564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_937564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937564 prefixEnd_937564 := by exact prefixLift 937564
  have htrace : WordTrace (prefixWord ++ tailWord_937564) baseStart_937564 baseEnd_937564 := by
    simpa [prefixWord, tailWord_937564, baseEnd_937564] using wordTrace_append hprefix tailTrace_937564
  have hstable : (prefixWord ++ tailWord_937564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937564).length < 2 ^ (prefixWord ++ tailWord_937564).sum := by decide
  have hdescent : baseEnd_937564 < baseStart_937564 := by decide
  rcases family_descends (prefixWord ++ tailWord_937564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937577 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 8]
def baseStart_937577 : Nat := 118140960795 + 937577 * 2 ^ 59
def prefixEnd_937577 : Nat := 4983230072969 + 3 ^ 40 * 937577 * 2
def baseEnd_937577 : Nat := 106983922577907435416815

theorem tailTrace_937577 : CollatzResearch.WordTrace tailWord_937577 prefixEnd_937577 106983922577907435416815 := by
  unfold tailWord_937577
  simp only [CollatzResearch.WordTrace]
  refine ⟨34196242524326129248474985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22797495016217419498983323 34196242524326129248474985)
  ·
    refine ⟨25647181893244596936356239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34196242524326129248474985 25647181893244596936356239)
    ·
      refine ⟨38470772839866895404534359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25647181893244596936356239 38470772839866895404534359)
      ·
        refine ⟨57706159259800343106801539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38470772839866895404534359 57706159259800343106801539)
        ·
          refine ⟨86559238889700514660202309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57706159259800343106801539 86559238889700514660202309)
          ·
            refine ⟨16229857291818846498787933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86559238889700514660202309 16229857291818846498787933)
            ·
              refine ⟨6086196484432067437045475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16229857291818846498787933 6086196484432067437045475)
              ·
                refine ⟨9129294726648101155568213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086196484432067437045475 9129294726648101155568213)
                ·
                  refine ⟨106983922577907435416815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9129294726648101155568213 106983922577907435416815)
                  ·
                    rfl

theorem cell22_937577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_937577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937577 prefixEnd_937577 := by exact prefixLift 937577
  have htrace : WordTrace (prefixWord ++ tailWord_937577) baseStart_937577 baseEnd_937577 := by
    simpa [prefixWord, tailWord_937577, baseEnd_937577] using wordTrace_append hprefix tailTrace_937577
  have hstable : (prefixWord ++ tailWord_937577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937577).length < 2 ^ (prefixWord ++ tailWord_937577).sum := by decide
  have hdescent : baseEnd_937577 < baseStart_937577 := by decide
  rcases family_descends (prefixWord ++ tailWord_937577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937624 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_937624 : Nat := 118140960795 + 937624 * 2 ^ 59
def prefixEnd_937624 : Nat := 4983230072969 + 3 ^ 40 * 937624 * 2
def baseEnd_937624 : Nat := 320967856794229850325301

theorem tailTrace_937624 : CollatzResearch.WordTrace tailWord_937624 prefixEnd_937624 320967856794229850325301 := by
  unfold tailWord_937624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17098978377577928137717963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22798637836770570850290617 17098978377577928137717963)
  ·
    refine ⟨25648467566366892206576945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17098978377577928137717963 25648467566366892206576945)
    ·
      refine ⟨19236350674775169154932709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25648467566366892206576945 19236350674775169154932709)
      ·
        refine ⟨3606815751520344216549883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19236350674775169154932709 3606815751520344216549883)
        ·
          refine ⟨5410223627280516324824825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606815751520344216549883 5410223627280516324824825)
          ·
            refine ⟨4057667720460387243618619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5410223627280516324824825 4057667720460387243618619)
            ·
              refine ⟨6086501580690580865427929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057667720460387243618619 6086501580690580865427929)
              ·
                refine ⟨4564876185517935649070947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6086501580690580865427929 4564876185517935649070947)
                ·
                  refine ⟨6847314278276903473606421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564876185517935649070947 6847314278276903473606421)
                  ·
                    refine ⟨320967856794229850325301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6847314278276903473606421 320967856794229850325301)
                    ·
                      rfl

theorem cell22_937624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_937624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937624 prefixEnd_937624 := by exact prefixLift 937624
  have htrace : WordTrace (prefixWord ++ tailWord_937624) baseStart_937624 baseEnd_937624 := by
    simpa [prefixWord, tailWord_937624, baseEnd_937624] using wordTrace_append hprefix tailTrace_937624
  have hstable : (prefixWord ++ tailWord_937624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937624).length < 2 ^ (prefixWord ++ tailWord_937624).sum := by decide
  have hdescent : baseEnd_937624 < baseStart_937624 := by decide
  rcases family_descends (prefixWord ++ tailWord_937624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937677 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_937677 : Nat := 118140960795 + 937677 * 2 ^ 59
def prefixEnd_937677 : Nat := 4983230072969 + 3 ^ 40 * 937677 * 2
def baseEnd_937677 : Nat := 320985999777355378750139

theorem tailTrace_937677 : CollatzResearch.WordTrace tailWord_937677 prefixEnd_937677 320985999777355378750139 := by
  unfold tailWord_937677
  simp only [CollatzResearch.WordTrace]
  refine ⟨34199889823963846327115285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22799926549309230884743523 34199889823963846327115285)
  ·
    refine ⟨1603119835498305296583529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34199889823963846327115285 1603119835498305296583529)
    ·
      refine ⟨1202339876623728972437647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1603119835498305296583529 1202339876623728972437647)
      ·
        refine ⟨1803509814935593458656471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202339876623728972437647 1803509814935593458656471)
        ·
          refine ⟨2705264722403390187984707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803509814935593458656471 2705264722403390187984707)
          ·
            refine ⟨4057897083605085281977061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705264722403390187984707 4057897083605085281977061)
            ·
              refine ⟨760855703175953490370699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4057897083605085281977061 760855703175953490370699)
              ·
                refine ⟨1141283554763930235556049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760855703175953490370699 1141283554763930235556049)
                ·
                  refine ⟨855962666072947676667037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141283554763930235556049 855962666072947676667037)
                  ·
                    refine ⟨320985999777355378750139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855962666072947676667037 320985999777355378750139)
                    ·
                      rfl

theorem cell22_937677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_937677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937677 prefixEnd_937677 := by exact prefixLift 937677
  have htrace : WordTrace (prefixWord ++ tailWord_937677) baseStart_937677 baseEnd_937677 := by
    simpa [prefixWord, tailWord_937677, baseEnd_937677] using wordTrace_append hprefix tailTrace_937677
  have hstable : (prefixWord ++ tailWord_937677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937677).length < 2 ^ (prefixWord ++ tailWord_937677).sum := by decide
  have hdescent : baseEnd_937677 < baseStart_937677 := by decide
  rcases family_descends (prefixWord ++ tailWord_937677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937718 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_937718 : Nat := 118140960795 + 937718 * 2 ^ 59
def prefixEnd_937718 : Nat := 4983230072969 + 3 ^ 40 * 937718 * 2
def baseEnd_937718 : Nat := 107000011638414979491671

theorem tailTrace_937718 : CollatzResearch.WordTrace tailWord_937718 prefixEnd_937718 107000011638414979491671 := by
  unfold tailWord_937718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137586576050956895584863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22800923477876873552905205 2137586576050956895584863)
  ·
    refine ⟨3206379864076435343377295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2137586576050956895584863 3206379864076435343377295)
    ·
      refine ⟨4809569796114653015065943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206379864076435343377295 4809569796114653015065943)
      ·
        refine ⟨7214354694171979522598915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809569796114653015065943 7214354694171979522598915)
        ·
          refine ⟨10821532041257969283898373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214354694171979522598915 10821532041257969283898373)
          ·
            refine ⟨2029037257735869240730945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10821532041257969283898373 2029037257735869240730945)
            ·
              refine ⟨1521777943301901930548209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029037257735869240730945 1521777943301901930548209)
              ·
                refine ⟨1141333457476426447911157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521777943301901930548209 1141333457476426447911157)
                ·
                  refine ⟨107000011638414979491671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1141333457476426447911157 107000011638414979491671)
                  ·
                    rfl

theorem cell22_937718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_937718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937718 prefixEnd_937718 := by exact prefixLift 937718
  have htrace : WordTrace (prefixWord ++ tailWord_937718) baseStart_937718 baseEnd_937718 := by
    simpa [prefixWord, tailWord_937718, baseEnd_937718] using wordTrace_append hprefix tailTrace_937718
  have hstable : (prefixWord ++ tailWord_937718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937718).length < 2 ^ (prefixWord ++ tailWord_937718).sum := by decide
  have hdescent : baseEnd_937718 < baseStart_937718 := by decide
  rcases family_descends (prefixWord ++ tailWord_937718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937761 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_937761 : Nat := 118140960795 + 937761 * 2 ^ 59
def prefixEnd_937761 : Nat := 4983230072969 + 3 ^ 40 * 937761 * 2
def baseEnd_937761 : Nat := 321014754694007159649881

theorem tailTrace_937761 : CollatzResearch.WordTrace tailWord_937761 prefixEnd_937761 321014754694007159649881 := by
  unfold tailWord_937761
  simp only [CollatzResearch.WordTrace]
  refine ⟨34202953555659528673173137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22801969037106352448782091 34202953555659528673173137)
  ·
    refine ⟨25652215166744646504879853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34202953555659528673173137 25652215166744646504879853)
    ·
      refine ⟨9619580687529242439329945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25652215166744646504879853 9619580687529242439329945)
      ·
        refine ⟨7214685515646931829497459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9619580687529242439329945 7214685515646931829497459)
        ·
          refine ⟨10822028273470397744246189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214685515646931829497459 10822028273470397744246189)
          ·
            refine ⟨4058260602551399154092321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10822028273470397744246189 4058260602551399154092321)
            ·
              refine ⟨3043695451913549365569241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058260602551399154092321 3043695451913549365569241)
              ·
                refine ⟨2282771588935162024176931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043695451913549365569241 2282771588935162024176931)
                ·
                  refine ⟨3424157383402743036265397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282771588935162024176931 3424157383402743036265397)
                  ·
                    refine ⟨321014754694007159649881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3424157383402743036265397 321014754694007159649881)
                    ·
                      rfl

theorem cell22_937761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_937761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937761 prefixEnd_937761 := by exact prefixLift 937761
  have htrace : WordTrace (prefixWord ++ tailWord_937761) baseStart_937761 baseEnd_937761 := by
    simpa [prefixWord, tailWord_937761, baseEnd_937761] using wordTrace_append hprefix tailTrace_937761
  have hstable : (prefixWord ++ tailWord_937761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937761).length < 2 ^ (prefixWord ++ tailWord_937761).sum := by decide
  have hdescent : baseEnd_937761 < baseStart_937761 := by decide
  rcases family_descends (prefixWord ++ tailWord_937761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937765 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_937765 : Nat := 118140960795 + 937765 * 2 ^ 59
def prefixEnd_937765 : Nat := 4983230072969 + 3 ^ 40 * 937765 * 2
def baseEnd_937765 : Nat := 321016123975752482549869

theorem tailTrace_937765 : CollatzResearch.WordTrace tailWord_937765 prefixEnd_937765 321016123975752482549869 := by
  unfold tailWord_937765
  simp only [CollatzResearch.WordTrace]
  refine ⟨34203099447645037356318749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22802066298430024904212499 34203099447645037356318749)
  ·
    refine ⟨12826162292866889008619531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34203099447645037356318749 12826162292866889008619531)
    ·
      refine ⟨19239243439300333512929297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12826162292866889008619531 19239243439300333512929297)
      ·
        refine ⟨14429432579475250134696973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19239243439300333512929297 14429432579475250134696973)
        ·
          refine ⟨5411037217303218800511365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14429432579475250134696973 5411037217303218800511365)
          ·
            refine ⟨1014569478244353525095881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5411037217303218800511365 1014569478244353525095881)
            ·
              refine ⟨760927108683265143821911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014569478244353525095881 760927108683265143821911)
              ·
                refine ⟨1141390663024897715732867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760927108683265143821911 1141390663024897715732867)
                ·
                  refine ⟨1712085994537346573599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141390663024897715732867 1712085994537346573599301)
                  ·
                    refine ⟨321016123975752482549869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712085994537346573599301 321016123975752482549869)
                    ·
                      rfl

theorem cell22_937765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_937765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937765 prefixEnd_937765 := by exact prefixLift 937765
  have htrace : WordTrace (prefixWord ++ tailWord_937765) baseStart_937765 baseEnd_937765 := by
    simpa [prefixWord, tailWord_937765, baseEnd_937765] using wordTrace_append hprefix tailTrace_937765
  have hstable : (prefixWord ++ tailWord_937765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937765).length < 2 ^ (prefixWord ++ tailWord_937765).sum := by decide
  have hdescent : baseEnd_937765 < baseStart_937765 := by decide
  rcases family_descends (prefixWord ++ tailWord_937765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937778 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_937778 : Nat := 118140960795 + 937778 * 2 ^ 59
def prefixEnd_937778 : Nat := 4983230072969 + 3 ^ 40 * 937778 * 2
def baseEnd_937778 : Nat := 321020574141424781974829

theorem tailTrace_937778 : CollatzResearch.WordTrace tailWord_937778 prefixEnd_937778 321020574141424781974829 := by
  unfold tailWord_937778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8550893399149485144135497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22802382397731960384361325 8550893399149485144135497)
  ·
    refine ⟨6413170049362113858101623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8550893399149485144135497 6413170049362113858101623)
    ·
      refine ⟨9619755074043170787152435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6413170049362113858101623 9619755074043170787152435)
      ·
        refine ⟨14429632611064756180728653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9619755074043170787152435 14429632611064756180728653)
        ·
          refine ⟨5411112229149283567773245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14429632611064756180728653 5411112229149283567773245)
          ·
            refine ⟨2029167085930981337914967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5411112229149283567773245 2029167085930981337914967)
            ·
              refine ⟨3043750628896472006872451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029167085930981337914967 3043750628896472006872451)
              ·
                refine ⟨4565625943344708010308677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043750628896472006872451 4565625943344708010308677)
                ·
                  refine ⟨856054864377132751932877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4565625943344708010308677 856054864377132751932877)
                  ·
                    refine ⟨321020574141424781974829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856054864377132751932877 321020574141424781974829)
                    ·
                      rfl

theorem cell22_937778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_937778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937778 prefixEnd_937778 := by exact prefixLift 937778
  have htrace : WordTrace (prefixWord ++ tailWord_937778) baseStart_937778 baseEnd_937778 := by
    simpa [prefixWord, tailWord_937778, baseEnd_937778] using wordTrace_append hprefix tailTrace_937778
  have hstable : (prefixWord ++ tailWord_937778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937778).length < 2 ^ (prefixWord ++ tailWord_937778).sum := by decide
  have hdescent : baseEnd_937778 < baseStart_937778 := by decide
  rcases family_descends (prefixWord ++ tailWord_937778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937780 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 4]
def baseStart_937780 : Nat := 118140960795 + 937780 * 2 ^ 59
def prefixEnd_937780 : Nat := 4983230072969 + 3 ^ 40 * 937780 * 2
def baseEnd_937780 : Nat := 107007086260765814474941

theorem tailTrace_937780 : CollatzResearch.WordTrace tailWord_937780 prefixEnd_937780 107007086260765814474941 := by
  unfold tailWord_937780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101823271295347459057397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22802431028393796612076529 17101823271295347459057397)
  ·
    refine ⟨1603295931683938824286631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17101823271295347459057397 1603295931683938824286631)
    ·
      refine ⟨2404943897525908236429947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603295931683938824286631 2404943897525908236429947)
      ·
        refine ⟨3607415846288862354644921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404943897525908236429947 3607415846288862354644921)
        ·
          refine ⟨2705561884716646765983691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3607415846288862354644921 2705561884716646765983691)
          ·
            refine ⟨4058342827074970148975537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705561884716646765983691 4058342827074970148975537)
            ·
              refine ⟨3043757120306227611731653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058342827074970148975537 3043757120306227611731653)
              ·
                refine ⟨570704460057417677199685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3043757120306227611731653 570704460057417677199685)
                ·
                  refine ⟨107007086260765814474941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570704460057417677199685 107007086260765814474941)
                  ·
                    rfl

theorem cell22_937780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_937780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937780 prefixEnd_937780 := by exact prefixLift 937780
  have htrace : WordTrace (prefixWord ++ tailWord_937780) baseStart_937780 baseEnd_937780 := by
    simpa [prefixWord, tailWord_937780, baseEnd_937780] using wordTrace_append hprefix tailTrace_937780
  have hstable : (prefixWord ++ tailWord_937780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937780).length < 2 ^ (prefixWord ++ tailWord_937780).sum := by decide
  have hdescent : baseEnd_937780 < baseStart_937780 := by decide
  rcases family_descends (prefixWord ++ tailWord_937780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937795 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 2, 3]
def baseStart_937795 : Nat := 118140960795 + 937795 * 2 ^ 59
def prefixEnd_937795 : Nat := 4983230072969 + 3 ^ 40 * 937795 * 2
def baseEnd_937795 : Nat := 321026393588842404299777

theorem tailTrace_937795 : CollatzResearch.WordTrace tailWord_937795 prefixEnd_937795 321026393588842404299777 := by
  unfold tailWord_937795
  simp only [CollatzResearch.WordTrace]
  refine ⟨34204193637536352479910839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22802795758357568319940559 34204193637536352479910839)
  ·
    refine ⟨51306290456304528719866259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34204193637536352479910839 51306290456304528719866259)
    ·
      refine ⟨76959435684456793079799389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51306290456304528719866259 76959435684456793079799389)
      ·
        refine ⟨28859788381671297404924771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76959435684456793079799389 28859788381671297404924771)
        ·
          refine ⟨43289682572506946107387157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28859788381671297404924771 43289682572506946107387157)
          ·
            refine ⟨2029203870586263098783773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43289682572506946107387157 2029203870586263098783773)
            ·
              refine ⟨760951451469848662043915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2029203870586263098783773 760951451469848662043915)
              ·
                refine ⟨1141427177204772993065873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760951451469848662043915 1141427177204772993065873)
                ·
                  refine ⟨856070382903579744799405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141427177204772993065873 856070382903579744799405)
                  ·
                    refine ⟨321026393588842404299777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856070382903579744799405 321026393588842404299777)
                    ·
                      rfl

theorem cell22_937795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 3].length) (baseStart_937795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937795 prefixEnd_937795 := by exact prefixLift 937795
  have htrace : WordTrace (prefixWord ++ tailWord_937795) baseStart_937795 baseEnd_937795 := by
    simpa [prefixWord, tailWord_937795, baseEnd_937795] using wordTrace_append hprefix tailTrace_937795
  have hstable : (prefixWord ++ tailWord_937795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937795).length < 2 ^ (prefixWord ++ tailWord_937795).sum := by decide
  have hdescent : baseEnd_937795 < baseStart_937795 := by decide
  rcases family_descends (prefixWord ++ tailWord_937795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937836 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_937836 : Nat := 118140960795 + 937836 * 2 ^ 59
def prefixEnd_937836 : Nat := 4983230072969 + 3 ^ 40 * 937836 * 2
def baseEnd_937836 : Nat := 107013476242243988008217

theorem tailTrace_937836 : CollatzResearch.WordTrace tailWord_937836 prefixEnd_937836 107013476242243988008217 := by
  unfold tailWord_937836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17102844515193908241076681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22803792686925210988102241 17102844515193908241076681)
  ·
    refine ⟨12827133386395431180807511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17102844515193908241076681 12827133386395431180807511)
    ·
      refine ⟨19240700079593146771211267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12827133386395431180807511 19240700079593146771211267)
      ·
        refine ⟨28861050119389720156816901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19240700079593146771211267 28861050119389720156816901)
        ·
          refine ⟨5411446897385572529403169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28861050119389720156816901 5411446897385572529403169)
          ·
            refine ⟨4058585173039179397052377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5411446897385572529403169 4058585173039179397052377)
            ·
              refine ⟨3043938879779384547789283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058585173039179397052377 3043938879779384547789283)
              ·
                refine ⟨4565908319669076821683925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043938879779384547789283 4565908319669076821683925)
                ·
                  refine ⟨107013476242243988008217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4565908319669076821683925 107013476242243988008217)
                  ·
                    rfl

theorem cell22_937836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_937836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937836 prefixEnd_937836 := by exact prefixLift 937836
  have htrace : WordTrace (prefixWord ++ tailWord_937836) baseStart_937836 baseEnd_937836 := by
    simpa [prefixWord, tailWord_937836, baseEnd_937836] using wordTrace_append hprefix tailTrace_937836
  have hstable : (prefixWord ++ tailWord_937836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937836).length < 2 ^ (prefixWord ++ tailWord_937836).sum := by decide
  have hdescent : baseEnd_937836 < baseStart_937836 := by decide
  rcases family_descends (prefixWord ++ tailWord_937836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937846 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_937846 : Nat := 118140960795 + 937846 * 2 ^ 59
def prefixEnd_937846 : Nat := 4983230072969 + 3 ^ 40 * 937846 * 2
def baseEnd_937846 : Nat := 321043851931095271274621

theorem tailTrace_937846 : CollatzResearch.WordTrace tailWord_937846 prefixEnd_937846 321043851931095271274621 := by
  unfold tailWord_937846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137878360021974261876087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22804035840234392126678261 2137878360021974261876087)
  ·
    refine ⟨3206817540032961392814131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2137878360021974261876087 3206817540032961392814131)
    ·
      refine ⟨4810226310049442089221197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206817540032961392814131 4810226310049442089221197)
      ·
        refine ⟨1803834866268540783457949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4810226310049442089221197 1803834866268540783457949)
        ·
          refine ⟨676438074850702793796731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1803834866268540783457949 676438074850702793796731)
          ·
            refine ⟨1014657112276054190695097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676438074850702793796731 1014657112276054190695097)
            ·
              refine ⟨760992834207040643021323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014657112276054190695097 760992834207040643021323)
              ·
                refine ⟨1141489251310560964531985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760992834207040643021323 1141489251310560964531985)
                ·
                  refine ⟨856116938482920723398989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141489251310560964531985 856116938482920723398989)
                  ·
                    refine ⟨321043851931095271274621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856116938482920723398989 321043851931095271274621)
                    ·
                      rfl

theorem cell22_937846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_937846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937846 prefixEnd_937846 := by exact prefixLift 937846
  have htrace : WordTrace (prefixWord ++ tailWord_937846) baseStart_937846 baseEnd_937846 := by
    simpa [prefixWord, tailWord_937846, baseEnd_937846] using wordTrace_append hprefix tailTrace_937846
  have hstable : (prefixWord ++ tailWord_937846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937846).length < 2 ^ (prefixWord ++ tailWord_937846).sum := by decide
  have hdescent : baseEnd_937846 < baseStart_937846 := by decide
  rcases family_descends (prefixWord ++ tailWord_937846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937911 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_937911 : Nat := 118140960795 + 937911 * 2 ^ 59
def prefixEnd_937911 : Nat := 4983230072969 + 3 ^ 40 * 937911 * 2
def baseEnd_937911 : Nat := 321066102759456768399421

theorem tailTrace_937911 : CollatzResearch.WordTrace tailWord_937911 prefixEnd_937911 321066102759456768399421 := by
  unfold tailWord_937911
  simp only [CollatzResearch.WordTrace]
  refine ⟨34208424505116104291133587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22805616336744069527422391 34208424505116104291133587)
  ·
    refine ⟨51312636757674156436700381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34208424505116104291133587 51312636757674156436700381)
    ·
      refine ⟨19242238784127808663762643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51312636757674156436700381 19242238784127808663762643)
      ·
        refine ⟨28863358176191712995643965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19242238784127808663762643 28863358176191712995643965)
        ·
          refine ⟨10823759316071892373366487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28863358176191712995643965 10823759316071892373366487)
          ·
            refine ⟨16235638974107838560049731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823759316071892373366487 16235638974107838560049731)
            ·
              refine ⟨24353458461161757840074597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16235638974107838560049731 24353458461161757840074597)
              ·
                refine ⟨4566273461467829595013987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24353458461161757840074597 4566273461467829595013987)
                ·
                  refine ⟨6849410192201744392520981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566273461467829595013987 6849410192201744392520981)
                  ·
                    refine ⟨321066102759456768399421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6849410192201744392520981 321066102759456768399421)
                    ·
                      rfl

theorem cell22_937911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_937911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937911 prefixEnd_937911 := by exact prefixLift 937911
  have htrace : WordTrace (prefixWord ++ tailWord_937911) baseStart_937911 baseEnd_937911 := by
    simpa [prefixWord, tailWord_937911, baseEnd_937911] using wordTrace_append hprefix tailTrace_937911
  have hstable : (prefixWord ++ tailWord_937911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937911).length < 2 ^ (prefixWord ++ tailWord_937911).sum := by decide
  have hdescent : baseEnd_937911 < baseStart_937911 := by decide
  rcases family_descends (prefixWord ++ tailWord_937911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937913 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_937913 : Nat := 118140960795 + 937913 * 2 ^ 59
def prefixEnd_937913 : Nat := 4983230072969 + 3 ^ 40 * 937913 * 2
def baseEnd_937913 : Nat := 321066787400329429849415

theorem tailTrace_937913 : CollatzResearch.WordTrace tailWord_937913 prefixEnd_937913 321066787400329429849415 := by
  unfold tailWord_937913
  simp only [CollatzResearch.WordTrace]
  refine ⟨34208497451108858632706393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22805664967405905755137595 34208497451108858632706393)
  ·
    refine ⟨25656373088331643974529795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34208497451108858632706393 25656373088331643974529795)
    ·
      refine ⟨38484559632497465961794693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25656373088331643974529795 38484559632497465961794693)
      ·
        refine ⟨7215854931093274867836505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38484559632497465961794693 7215854931093274867836505)
        ·
          refine ⟨5411891198319956150877379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7215854931093274867836505 5411891198319956150877379)
          ·
            refine ⟨8117836797479934226316069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411891198319956150877379 8117836797479934226316069)
            ·
              refine ⟨1522094399527487667434263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8117836797479934226316069 1522094399527487667434263)
              ·
                refine ⟨2283141599291231501151395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522094399527487667434263 2283141599291231501151395)
                ·
                  refine ⟨3424712398936847251727093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283141599291231501151395 3424712398936847251727093)
                  ·
                    refine ⟨321066787400329429849415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3424712398936847251727093 321066787400329429849415)
                    ·
                      rfl

theorem cell22_937913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_937913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937913 prefixEnd_937913 := by exact prefixLift 937913
  have htrace : WordTrace (prefixWord ++ tailWord_937913) baseStart_937913 baseEnd_937913 := by
    simpa [prefixWord, tailWord_937913, baseEnd_937913] using wordTrace_append hprefix tailTrace_937913
  have hstable : (prefixWord ++ tailWord_937913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937913).length < 2 ^ (prefixWord ++ tailWord_937913).sum := by decide
  have hdescent : baseEnd_937913 < baseStart_937913 := by decide
  rcases family_descends (prefixWord ++ tailWord_937913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937928 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_937928 : Nat := 118140960795 + 937928 * 2 ^ 59
def prefixEnd_937928 : Nat := 4983230072969 + 3 ^ 40 * 937928 * 2
def baseEnd_937928 : Nat := 321071922206874390724369

theorem tailTrace_937928 : CollatzResearch.WordTrace tailWord_937928 prefixEnd_937928 321071922206874390724369 := by
  unfold tailWord_937928
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104522273027258097251219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22806029697369677463001625 17104522273027258097251219)
  ·
    refine ⟨25656783409540887145876829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17104522273027258097251219 25656783409540887145876829)
    ·
      refine ⟨9621293778577832679703811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25656783409540887145876829 9621293778577832679703811)
      ·
        refine ⟨14431940667866749019555717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621293778577832679703811 14431940667866749019555717)
        ·
          refine ⟨2705988875225015441166697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14431940667866749019555717 2705988875225015441166697)
          ·
            refine ⟨2029491656418761580875023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2705988875225015441166697 2029491656418761580875023)
            ·
              refine ⟨3044237484628142371312535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029491656418761580875023 3044237484628142371312535)
              ·
                refine ⟨4566356226942213556968803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044237484628142371312535 4566356226942213556968803)
                ·
                  refine ⟨6849534340413320335453205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566356226942213556968803 6849534340413320335453205)
                  ·
                    refine ⟨321071922206874390724369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6849534340413320335453205 321071922206874390724369)
                    ·
                      rfl

theorem cell22_937928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_937928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_937928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_937928 prefixEnd_937928 := by exact prefixLift 937928
  have htrace : WordTrace (prefixWord ++ tailWord_937928) baseStart_937928 baseEnd_937928 := by
    simpa [prefixWord, tailWord_937928, baseEnd_937928] using wordTrace_append hprefix tailTrace_937928
  have hstable : (prefixWord ++ tailWord_937928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937928).length < 2 ^ (prefixWord ++ tailWord_937928).sum := by decide
  have hdescent : baseEnd_937928 < baseStart_937928 := by decide
  rcases family_descends (prefixWord ++ tailWord_937928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938035 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 1, 4]
def baseStart_938035 : Nat := 118140960795 + 938035 * 2 ^ 59
def prefixEnd_938035 : Nat := 4983230072969 + 3 ^ 40 * 938035 * 2
def baseEnd_938035 : Nat := 321108550493561778299041

theorem tailTrace_938035 : CollatzResearch.WordTrace tailWord_938035 prefixEnd_938035 321108550493561778299041 := by
  unfold tailWord_938035
  simp only [CollatzResearch.WordTrace]
  refine ⟨34212947156666873468647559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22808631437777915645765039 34212947156666873468647559)
  ·
    refine ⟨51319420735000310202971339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34212947156666873468647559 51319420735000310202971339)
    ·
      refine ⟨76979131102500465304457009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51319420735000310202971339 76979131102500465304457009)
      ·
        refine ⟨57734348326875348978342757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76979131102500465304457009 57734348326875348978342757)
        ·
          refine ⟨10825190311289127933439267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57734348326875348978342757 10825190311289127933439267)
          ·
            refine ⟨16237785466933691900158901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825190311289127933439267 16237785466933691900158901)
            ·
              refine ⟨1522292387525033615639897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16237785466933691900158901 1522292387525033615639897)
              ·
                refine ⟨1141719290643775211729923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522292387525033615639897 1141719290643775211729923)
                ·
                  refine ⟨1712578935965662817594885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141719290643775211729923 1712578935965662817594885)
                  ·
                    refine ⟨321108550493561778299041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712578935965662817594885 321108550493561778299041)
                    ·
                      rfl

theorem cell22_938035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 4].length) (baseStart_938035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938035 prefixEnd_938035 := by exact prefixLift 938035
  have htrace : WordTrace (prefixWord ++ tailWord_938035) baseStart_938035 baseEnd_938035 := by
    simpa [prefixWord, tailWord_938035, baseEnd_938035] using wordTrace_append hprefix tailTrace_938035
  have hstable : (prefixWord ++ tailWord_938035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938035).length < 2 ^ (prefixWord ++ tailWord_938035).sum := by decide
  have hdescent : baseEnd_938035 < baseStart_938035 := by decide
  rcases family_descends (prefixWord ++ tailWord_938035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938048 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_938048 : Nat := 118140960795 + 938048 * 2 ^ 59
def prefixEnd_938048 : Nat := 4983230072969 + 3 ^ 40 * 938048 * 2
def baseEnd_938048 : Nat := 321113000659234077724001

theorem tailTrace_938048 : CollatzResearch.WordTrace tailWord_938048 prefixEnd_938048 321113000659234077724001 := by
  unfold tailWord_938048
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106710652809888344435399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22808947537079851125913865 17106710652809888344435399)
  ·
    refine ⟨25660065979214832516653099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17106710652809888344435399 25660065979214832516653099)
    ·
      refine ⟨38490098968822248774979649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25660065979214832516653099 38490098968822248774979649)
      ·
        refine ⟨28867574226616686581234737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38490098968822248774979649 28867574226616686581234737)
        ·
          refine ⟨21650680669962514935926053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28867574226616686581234737 21650680669962514935926053)
          ·
            refine ⟨4059502625617971550486135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21650680669962514935926053 4059502625617971550486135)
            ·
              refine ⟨6089253938426957325729203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059502625617971550486135 6089253938426957325729203)
              ·
                refine ⟨9133880907640435988593805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089253938426957325729203 9133880907640435988593805)
                ·
                  refine ⟨3425205340365163495722677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9133880907640435988593805 3425205340365163495722677)
                  ·
                    refine ⟨321113000659234077724001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3425205340365163495722677 321113000659234077724001)
                    ·
                      rfl

theorem cell22_938048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_938048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938048 prefixEnd_938048 := by exact prefixLift 938048
  have htrace : WordTrace (prefixWord ++ tailWord_938048) baseStart_938048 baseEnd_938048 := by
    simpa [prefixWord, tailWord_938048, baseEnd_938048] using wordTrace_append hprefix tailTrace_938048
  have hstable : (prefixWord ++ tailWord_938048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938048).length < 2 ^ (prefixWord ++ tailWord_938048).sum := by decide
  have hdescent : baseEnd_938048 < baseStart_938048 := by decide
  rcases family_descends (prefixWord ++ tailWord_938048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938095 : List Nat := [1, 1, 2, 1, 3, 5, 3, 6]
def baseStart_938095 : Nat := 118140960795 + 938095 * 2 ^ 59
def prefixEnd_938095 : Nat := 4983230072969 + 3 ^ 40 * 938095 * 2
def baseEnd_938095 : Nat := 35681009968860180199873

theorem tailTrace_938095 : CollatzResearch.WordTrace tailWord_938095 prefixEnd_938095 35681009968860180199873 := by
  unfold tailWord_938095
  simp only [CollatzResearch.WordTrace]
  refine ⟨34215135536449503715831739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22810090357633002477221159 34215135536449503715831739)
  ·
    refine ⟨51322703304674255573747609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34215135536449503715831739 51322703304674255573747609)
    ·
      refine ⟨38492027478505691680310707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51322703304674255573747609 38492027478505691680310707)
      ·
        refine ⟨57738041217758537520466061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38492027478505691680310707 57738041217758537520466061)
        ·
          refine ⟨21651765456659451570174773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57738041217758537520466061 21651765456659451570174773)
          ·
            refine ⟨2029853011561823584703885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21651765456659451570174773 2029853011561823584703885)
            ·
              refine ⟨761194879335683844263957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2029853011561823584703885 761194879335683844263957)
              ·
                refine ⟨35681009968860180199873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 761194879335683844263957 35681009968860180199873)
                ·
                  rfl

theorem cell22_938095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 6].length) (baseStart_938095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938095 prefixEnd_938095 := by exact prefixLift 938095
  have htrace : WordTrace (prefixWord ++ tailWord_938095) baseStart_938095 baseEnd_938095 := by
    simpa [prefixWord, tailWord_938095, baseEnd_938095] using wordTrace_append hprefix tailTrace_938095
  have hstable : (prefixWord ++ tailWord_938095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938095).length < 2 ^ (prefixWord ++ tailWord_938095).sum := by decide
  have hdescent : baseEnd_938095 < baseStart_938095 := by decide
  rcases family_descends (prefixWord ++ tailWord_938095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938178 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_938178 : Nat := 118140960795 + 938178 * 2 ^ 59
def prefixEnd_938178 : Nat := 4983230072969 + 3 ^ 40 * 938178 * 2
def baseEnd_938178 : Nat := 321157502315957071973603

theorem tailTrace_938178 : CollatzResearch.WordTrace tailWord_938178 prefixEnd_938178 321157502315957071973603 := by
  unfold tailWord_938178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554540698787202222775797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22812108530099205927402125 8554540698787202222775797)
  ·
    refine ⟨801988190511300208385231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8554540698787202222775797 801988190511300208385231)
    ·
      refine ⟨1202982285766950312577847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801988190511300208385231 1202982285766950312577847)
      ·
        refine ⟨1804473428650425468866771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202982285766950312577847 1804473428650425468866771)
        ·
          refine ⟨2706710142975638203300157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804473428650425468866771 2706710142975638203300157)
          ·
            refine ⟨1015016303615864326237559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2706710142975638203300157 1015016303615864326237559)
            ·
              refine ⟨1522524455423796489356339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015016303615864326237559 1522524455423796489356339)
              ·
                refine ⟨2283786683135694734034509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522524455423796489356339 2283786683135694734034509)
                ·
                  refine ⟨856420006175885525262941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2283786683135694734034509 856420006175885525262941)
                  ·
                    refine ⟨321157502315957071973603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856420006175885525262941 321157502315957071973603)
                    ·
                      rfl

theorem cell22_938178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_938178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938178 prefixEnd_938178 := by exact prefixLift 938178
  have htrace : WordTrace (prefixWord ++ tailWord_938178) baseStart_938178 baseEnd_938178 := by
    simpa [prefixWord, tailWord_938178, baseEnd_938178] using wordTrace_append hprefix tailTrace_938178
  have hstable : (prefixWord ++ tailWord_938178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938178).length < 2 ^ (prefixWord ++ tailWord_938178).sum := by decide
  have hdescent : baseEnd_938178 < baseStart_938178 := by decide
  rcases family_descends (prefixWord ++ tailWord_938178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938221 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_938221 : Nat := 118140960795 + 938221 * 2 ^ 59
def prefixEnd_938221 : Nat := 4983230072969 + 3 ^ 40 * 938221 * 2
def baseEnd_938221 : Nat := 321172222094719293148471

theorem tailTrace_938221 : CollatzResearch.WordTrace tailWord_938221 prefixEnd_938221 321172222094719293148471 := by
  unfold tailWord_938221
  simp only [CollatzResearch.WordTrace]
  refine ⟨34219731133993027234918517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22813154089328684823279011 34219731133993027234918517)
  ·
    refine ⟨3208099793811846303273611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34219731133993027234918517 3208099793811846303273611)
    ·
      refine ⟨4812149690717769454910417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3208099793811846303273611 4812149690717769454910417)
      ·
        refine ⟨3609112268038327091182813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4812149690717769454910417 3609112268038327091182813)
        ·
          refine ⟨1353417100514372659193555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3609112268038327091182813 1353417100514372659193555)
          ·
            refine ⟨2030125650771558988790333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353417100514372659193555 2030125650771558988790333)
            ·
              refine ⟨761297119039334620796375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030125650771558988790333 761297119039334620796375)
              ·
                refine ⟨1141945678559001931194563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761297119039334620796375 1141945678559001931194563)
                ·
                  refine ⟨1712918517838502896791845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141945678559001931194563 1712918517838502896791845)
                  ·
                    refine ⟨321172222094719293148471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712918517838502896791845 321172222094719293148471)
                    ·
                      rfl

theorem cell22_938221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_938221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938221 prefixEnd_938221 := by exact prefixLift 938221
  have htrace : WordTrace (prefixWord ++ tailWord_938221) baseStart_938221 baseEnd_938221 := by
    simpa [prefixWord, tailWord_938221, baseEnd_938221] using wordTrace_append hprefix tailTrace_938221
  have hstable : (prefixWord ++ tailWord_938221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938221).length < 2 ^ (prefixWord ++ tailWord_938221).sum := by decide
  have hdescent : baseEnd_938221 < baseStart_938221 := by decide
  rcases family_descends (prefixWord ++ tailWord_938221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938234 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_938234 : Nat := 118140960795 + 938234 * 2 ^ 59
def prefixEnd_938234 : Nat := 4983230072969 + 3 ^ 40 * 938234 * 2
def baseEnd_938234 : Nat := 321176672260391592573431

theorem tailTrace_938234 : CollatzResearch.WordTrace tailWord_938234 prefixEnd_938234 321176672260391592573431 := by
  unfold tailWord_938234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555051320736482613785439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22813470188630620303427837 8555051320736482613785439)
  ·
    refine ⟨12832576981104723920678159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8555051320736482613785439 12832576981104723920678159)
    ·
      refine ⟨19248865471657085881017239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832576981104723920678159 19248865471657085881017239)
      ·
        refine ⟨28873298207485628821525859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19248865471657085881017239 28873298207485628821525859)
        ·
          refine ⟨43309947311228443232288789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28873298207485628821525859 43309947311228443232288789)
          ·
            refine ⟨2030153780213833276513537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43309947311228443232288789 2030153780213833276513537)
            ·
              refine ⟨1522615335160374957385153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030153780213833276513537 1522615335160374957385153)
              ·
                refine ⟨1141961501370281218038865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522615335160374957385153 1141961501370281218038865)
                ·
                  refine ⟨856471126027710913529149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141961501370281218038865 856471126027710913529149)
                  ·
                    refine ⟨321176672260391592573431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856471126027710913529149 321176672260391592573431)
                    ·
                      rfl

theorem cell22_938234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_938234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938234 prefixEnd_938234 := by exact prefixLift 938234
  have htrace : WordTrace (prefixWord ++ tailWord_938234) baseStart_938234 baseEnd_938234 := by
    simpa [prefixWord, tailWord_938234, baseEnd_938234] using wordTrace_append hprefix tailTrace_938234
  have hstable : (prefixWord ++ tailWord_938234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938234).length < 2 ^ (prefixWord ++ tailWord_938234).sum := by decide
  have hdescent : baseEnd_938234 < baseStart_938234 := by decide
  rcases family_descends (prefixWord ++ tailWord_938234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938236 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 4]
def baseStart_938236 : Nat := 118140960795 + 938236 * 2 ^ 59
def prefixEnd_938236 : Nat := 4983230072969 + 3 ^ 40 * 938236 * 2
def baseEnd_938236 : Nat := 107059118967088084674475

theorem tailTrace_938236 : CollatzResearch.WordTrace tailWord_938236 prefixEnd_938236 107059118967088084674475 := by
  unfold tailWord_938236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17110139114469342398357281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22813518819292456531143041 17110139114469342398357281)
  ·
    refine ⟨12832604335852006798767961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17110139114469342398357281 12832604335852006798767961)
    ·
      refine ⟨9624453251889005099075971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12832604335852006798767961 9624453251889005099075971)
      ·
        refine ⟨14436679877833507648613957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624453251889005099075971 14436679877833507648613957)
        ·
          refine ⟨2706877477093782684115117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14436679877833507648613957 2706877477093782684115117)
          ·
            refine ⟨1015079053910168506543169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2706877477093782684115117 1015079053910168506543169)
            ·
              refine ⟨761309290432626379907377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015079053910168506543169 761309290432626379907377)
              ·
                refine ⟨570981967824469784930533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761309290432626379907377 570981967824469784930533)
                ·
                  refine ⟨107059118967088084674475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570981967824469784930533 107059118967088084674475)
                  ·
                    rfl

theorem cell22_938236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_938236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938236 prefixEnd_938236 := by exact prefixLift 938236
  have htrace : WordTrace (prefixWord ++ tailWord_938236) baseStart_938236 baseEnd_938236 := by
    simpa [prefixWord, tailWord_938236, baseEnd_938236] using wordTrace_append hprefix tailTrace_938236
  have hstable : (prefixWord ++ tailWord_938236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938236).length < 2 ^ (prefixWord ++ tailWord_938236).sum := by decide
  have hdescent : baseEnd_938236 < baseStart_938236 := by decide
  rcases family_descends (prefixWord ++ tailWord_938236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938266 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_938266 : Nat := 118140960795 + 938266 * 2 ^ 59
def prefixEnd_938266 : Nat := 4983230072969 + 3 ^ 40 * 938266 * 2
def baseEnd_938266 : Nat := 321187626514354175773333

theorem tailTrace_938266 : CollatzResearch.WordTrace tailWord_938266 prefixEnd_938266 321187626514354175773333 := by
  unfold tailWord_938266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555343104707499980076663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22814248279219999946871101 8555343104707499980076663)
  ·
    refine ⟨12833014657061249970114995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8555343104707499980076663 12833014657061249970114995)
    ·
      refine ⟨19249521985591874955172493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12833014657061249970114995 19249521985591874955172493)
      ·
        refine ⟨7218570744596953108189685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19249521985591874955172493 7218570744596953108189685)
        ·
          refine ⟨676741007305964353892783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7218570744596953108189685 676741007305964353892783)
          ·
            refine ⟨1015111510958946530839175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676741007305964353892783 1015111510958946530839175)
            ·
              refine ⟨1522667266438419796258763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015111510958946530839175 1522667266438419796258763)
              ·
                refine ⟨2284000899657629694388145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522667266438419796258763 2284000899657629694388145)
                ·
                  refine ⟨1713000674743222270791109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2284000899657629694388145 1713000674743222270791109)
                  ·
                    refine ⟨321187626514354175773333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713000674743222270791109 321187626514354175773333)
                    ·
                      rfl

theorem cell22_938266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_938266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938266 prefixEnd_938266 := by exact prefixLift 938266
  have htrace : WordTrace (prefixWord ++ tailWord_938266) baseStart_938266 baseEnd_938266 := by
    simpa [prefixWord, tailWord_938266, baseEnd_938266] using wordTrace_append hprefix tailTrace_938266
  have hstable : (prefixWord ++ tailWord_938266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938266).length < 2 ^ (prefixWord ++ tailWord_938266).sum := by decide
  have hdescent : baseEnd_938266 < baseStart_938266 := by decide
  rcases family_descends (prefixWord ++ tailWord_938266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938275 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 7]
def baseStart_938275 : Nat := 118140960795 + 938275 * 2 ^ 59
def prefixEnd_938275 : Nat := 4983230072969 + 3 ^ 40 * 938275 * 2
def baseEnd_938275 : Nat := 107063569132760384099435

theorem tailTrace_938275 : CollatzResearch.WordTrace tailWord_938275 prefixEnd_938275 107063569132760384099435 := by
  unfold tailWord_938275
  simp only [CollatzResearch.WordTrace]
  refine ⟨34221700675797394457384279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22814467117198262971589519 34221700675797394457384279)
  ·
    refine ⟨51332551013696091686076419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34221700675797394457384279 51332551013696091686076419)
    ·
      refine ⟨76998826520544137529114629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51332551013696091686076419 76998826520544137529114629)
      ·
        refine ⟨14437279972602025786708993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76998826520544137529114629 14437279972602025786708993)
        ·
          refine ⟨10827959979451519340031745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14437279972602025786708993 10827959979451519340031745)
          ·
            refine ⟨8120969984588639505023809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10827959979451519340031745 8120969984588639505023809)
            ·
              refine ⟨6090727488441479628767857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120969984588639505023809 6090727488441479628767857)
              ·
                refine ⟨4568045616331109721575893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090727488441479628767857 4568045616331109721575893)
                ·
                  refine ⟨107063569132760384099435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4568045616331109721575893 107063569132760384099435)
                  ·
                    rfl

theorem cell22_938275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_938275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938275 prefixEnd_938275 := by exact prefixLift 938275
  have htrace : WordTrace (prefixWord ++ tailWord_938275) baseStart_938275 baseEnd_938275 := by
    simpa [prefixWord, tailWord_938275, baseEnd_938275] using wordTrace_append hprefix tailTrace_938275
  have hstable : (prefixWord ++ tailWord_938275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938275).length < 2 ^ (prefixWord ++ tailWord_938275).sum := by decide
  have hdescent : baseEnd_938275 < baseStart_938275 := by decide
  rcases family_descends (prefixWord ++ tailWord_938275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938285 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_938285 : Nat := 118140960795 + 938285 * 2 ^ 59
def prefixEnd_938285 : Nat := 4983230072969 + 3 ^ 40 * 938285 * 2
def baseEnd_938285 : Nat := 321194130602644459548275

theorem tailTrace_938285 : CollatzResearch.WordTrace tailWord_938285 prefixEnd_938285 321194130602644459548275 := by
  unfold tailWord_938285
  simp only [CollatzResearch.WordTrace]
  refine ⟨34222065405761166165248309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22814710270507444110165539 34222065405761166165248309)
  ·
    refine ⟨3208318631790109327992029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34222065405761166165248309 3208318631790109327992029)
    ·
      refine ⟨1203119486921290997997011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3208318631790109327992029 1203119486921290997997011)
      ·
        refine ⟨1804679230381936496995517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203119486921290997997011 1804679230381936496995517)
        ·
          refine ⟨676754711393226186373319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1804679230381936496995517 676754711393226186373319)
          ·
            refine ⟨1015132067089839279559979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676754711393226186373319 1015132067089839279559979)
            ·
              refine ⟨1522698100634758919339969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015132067089839279559979 1522698100634758919339969)
              ·
                refine ⟨1142023575476069189504977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522698100634758919339969 1142023575476069189504977)
                ·
                  refine ⟨856517681607051892128733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142023575476069189504977 856517681607051892128733)
                  ·
                    refine ⟨321194130602644459548275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856517681607051892128733 321194130602644459548275)
                    ·
                      rfl

theorem cell22_938285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_938285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938285 prefixEnd_938285 := by exact prefixLift 938285
  have htrace : WordTrace (prefixWord ++ tailWord_938285) baseStart_938285 baseEnd_938285 := by
    simpa [prefixWord, tailWord_938285, baseEnd_938285] using wordTrace_append hprefix tailTrace_938285
  have hstable : (prefixWord ++ tailWord_938285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938285).length < 2 ^ (prefixWord ++ tailWord_938285).sum := by decide
  have hdescent : baseEnd_938285 < baseStart_938285 := by decide
  rcases family_descends (prefixWord ++ tailWord_938285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938322 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_938322 : Nat := 118140960795 + 938322 * 2 ^ 59
def prefixEnd_938322 : Nat := 4983230072969 + 3 ^ 40 * 938322 * 2
def baseEnd_938322 : Nat := 321206796458788696373161

theorem tailTrace_938322 : CollatzResearch.WordTrace tailWord_938322 prefixEnd_938322 321206796458788696373161 := by
  unfold tailWord_938322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555853726656780371086305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22815609937751414322896813 8555853726656780371086305)
  ·
    refine ⟨6416890294992585278314729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8555853726656780371086305 6416890294992585278314729)
    ·
      refine ⟨4812667721244438958736047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6416890294992585278314729 4812667721244438958736047)
      ·
        refine ⟨7219001581866658438104071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812667721244438958736047 7219001581866658438104071)
        ·
          refine ⟨10828502372799987657156107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219001581866658438104071 10828502372799987657156107)
          ·
            refine ⟨16242753559199981485734161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828502372799987657156107 16242753559199981485734161)
            ·
              refine ⟨12182065169399986114300621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16242753559199981485734161 12182065169399986114300621)
              ·
                refine ⟨4568274438524994792862733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12182065169399986114300621 4568274438524994792862733)
                ·
                  refine ⟨1713102914446873047323525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4568274438524994792862733 1713102914446873047323525)
                  ·
                    refine ⟨321206796458788696373161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713102914446873047323525 321206796458788696373161)
                    ·
                      rfl

theorem cell22_938322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_938322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938322 prefixEnd_938322 := by exact prefixLift 938322
  have htrace : WordTrace (prefixWord ++ tailWord_938322) baseStart_938322 baseEnd_938322 := by
    simpa [prefixWord, tailWord_938322, baseEnd_938322] using wordTrace_append hprefix tailTrace_938322
  have hstable : (prefixWord ++ tailWord_938322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938322).length < 2 ^ (prefixWord ++ tailWord_938322).sum := by decide
  have hdescent : baseEnd_938322 < baseStart_938322 := by decide
  rcases family_descends (prefixWord ++ tailWord_938322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938354 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_938354 : Nat := 118140960795 + 938354 * 2 ^ 59
def prefixEnd_938354 : Nat := 4983230072969 + 3 ^ 40 * 938354 * 2
def baseEnd_938354 : Nat := 107072583570917093191021

theorem tailTrace_938354 : CollatzResearch.WordTrace tailWord_938354 prefixEnd_938354 107072583570917093191021 := by
  unfold tailWord_938354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556145510627797737377529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22816388028340793966340077 8556145510627797737377529)
  ·
    refine ⟨6417109132970848303033147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8556145510627797737377529 6417109132970848303033147)
    ·
      refine ⟨9625663699456272454549721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417109132970848303033147 9625663699456272454549721)
      ·
        refine ⟨7219247774592204340912291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9625663699456272454549721 7219247774592204340912291)
        ·
          refine ⟨10828871661888306511368437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219247774592204340912291 10828871661888306511368437)
          ·
            refine ⟨1015206718302028735440791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10828871661888306511368437 1015206718302028735440791)
            ·
              refine ⟨1522810077453043103161187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015206718302028735440791 1522810077453043103161187)
              ·
                refine ⟨2284215116179564654741781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522810077453043103161187 2284215116179564654741781)
                ·
                  refine ⟨107072583570917093191021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2284215116179564654741781 107072583570917093191021)
                  ·
                    rfl

theorem cell22_938354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_938354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938354 prefixEnd_938354 := by exact prefixLift 938354
  have htrace : WordTrace (prefixWord ++ tailWord_938354) baseStart_938354 baseEnd_938354 := by
    simpa [prefixWord, tailWord_938354, baseEnd_938354] using wordTrace_append hprefix tailTrace_938354
  have hstable : (prefixWord ++ tailWord_938354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938354).length < 2 ^ (prefixWord ++ tailWord_938354).sum := by decide
  have hdescent : baseEnd_938354 < baseStart_938354 := by decide
  rcases family_descends (prefixWord ++ tailWord_938354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938442 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_938442 : Nat := 118140960795 + 938442 * 2 ^ 59
def prefixEnd_938442 : Nat := 4983230072969 + 3 ^ 40 * 938442 * 2
def baseEnd_938442 : Nat := 321247874911148383372793

theorem tailTrace_938442 : CollatzResearch.WordTrace tailWord_938442 prefixEnd_938442 321247874911148383372793 := by
  unfold tailWord_938442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556947916548095494678395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22818527777461587985809053 8556947916548095494678395)
  ·
    refine ⟨12835421874822143242017593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556947916548095494678395 12835421874822143242017593)
    ·
      refine ⟨9626566406116607431513195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12835421874822143242017593 9626566406116607431513195)
      ·
        refine ⟨14439849609174911147269793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626566406116607431513195 14439849609174911147269793)
        ·
          refine ⟨10829887206881183360452345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14439849609174911147269793 10829887206881183360452345)
          ·
            refine ⟨8122415405160887520339259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829887206881183360452345 8122415405160887520339259)
            ·
              refine ⟨12183623107741331280508889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122415405160887520339259 12183623107741331280508889)
              ·
                refine ⟨9137717330805998460381667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183623107741331280508889 9137717330805998460381667)
                ·
                  refine ⟨13706575996208997690572501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137717330805998460381667 13706575996208997690572501)
                  ·
                    refine ⟨321247874911148383372793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13706575996208997690572501 321247874911148383372793)
                    ·
                      rfl

theorem cell22_938442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_938442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938442 prefixEnd_938442 := by exact prefixLift 938442
  have htrace : WordTrace (prefixWord ++ tailWord_938442) baseStart_938442 baseEnd_938442 := by
    simpa [prefixWord, tailWord_938442, baseEnd_938442] using wordTrace_append hprefix tailTrace_938442
  have hstable : (prefixWord ++ tailWord_938442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938442).length < 2 ^ (prefixWord ++ tailWord_938442).sum := by decide
  have hdescent : baseEnd_938442 < baseStart_938442 := by decide
  rcases family_descends (prefixWord ++ tailWord_938442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938538 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_938538 : Nat := 118140960795 + 938538 * 2 ^ 59
def prefixEnd_938538 : Nat := 4983230072969 + 3 ^ 40 * 938538 * 2
def baseEnd_938538 : Nat := 321280737673036132972499

theorem tailTrace_938538 : CollatzResearch.WordTrace tailWord_938538 prefixEnd_938538 321280737673036132972499 := by
  unfold tailWord_938538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557823268461147593552067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22820862049229726916138845 8557823268461147593552067)
  ·
    refine ⟨12836734902691721390328101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8557823268461147593552067 12836734902691721390328101)
    ·
      refine ⟨2406887794254697760686519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12836734902691721390328101 2406887794254697760686519)
      ·
        refine ⟨3610331691382046641029779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406887794254697760686519 3610331691382046641029779)
        ·
          refine ⟨5415497537073069961544669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610331691382046641029779 5415497537073069961544669)
          ·
            refine ⟨2030811576402401235579251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5415497537073069961544669 2030811576402401235579251)
            ·
              refine ⟨3046217364603601853368877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030811576402401235579251 3046217364603601853368877)
              ·
                refine ⟨1142331511726350695013329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3046217364603601853368877 1142331511726350695013329)
                ·
                  refine ⟨856748633794763021259997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142331511726350695013329 856748633794763021259997)
                  ·
                    refine ⟨321280737673036132972499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856748633794763021259997 321280737673036132972499)
                    ·
                      rfl

theorem cell22_938538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_938538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938538 prefixEnd_938538 := by exact prefixLift 938538
  have htrace : WordTrace (prefixWord ++ tailWord_938538) baseStart_938538 baseEnd_938538 := by
    simpa [prefixWord, tailWord_938538, baseEnd_938538] using wordTrace_append hprefix tailTrace_938538
  have hstable : (prefixWord ++ tailWord_938538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938538).length < 2 ^ (prefixWord ++ tailWord_938538).sum := by decide
  have hdescent : baseEnd_938538 < baseStart_938538 := by decide
  rcases family_descends (prefixWord ++ tailWord_938538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938583 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 1, 3]
def baseStart_938583 : Nat := 118140960795 + 938583 * 2 ^ 59
def prefixEnd_938583 : Nat := 4983230072969 + 3 ^ 40 * 938583 * 2
def baseEnd_938583 : Nat := 321296142092671015597361

theorem tailTrace_938583 : CollatzResearch.WordTrace tailWord_938583 prefixEnd_938583 321296142092671015597361 := by
  unfold tailWord_938583
  simp only [CollatzResearch.WordTrace]
  refine ⟨34232934358681563059596403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22821956239121042039730935 34232934358681563059596403)
  ·
    refine ⟨51349401538022344589394605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34232934358681563059596403 51349401538022344589394605)
    ·
      refine ⟨19256025576758379221022977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51349401538022344589394605 19256025576758379221022977)
      ·
        refine ⟨14442019182568784415767233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19256025576758379221022977 14442019182568784415767233)
        ·
          refine ⟨10831514386926588311825425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14442019182568784415767233 10831514386926588311825425)
          ·
            refine ⟨8123635790194941233869069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10831514386926588311825425 8123635790194941233869069)
            ·
              refine ⟨3046363421323102962700901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8123635790194941233869069 3046363421323102962700901)
              ·
                refine ⟨571193141498081805506419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3046363421323102962700901 571193141498081805506419)
                ·
                  refine ⟨856789712247122708259629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571193141498081805506419 856789712247122708259629)
                  ·
                    refine ⟨321296142092671015597361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856789712247122708259629 321296142092671015597361)
                    ·
                      rfl

theorem cell22_938583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_938583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938583 prefixEnd_938583 := by exact prefixLift 938583
  have htrace : WordTrace (prefixWord ++ tailWord_938583) baseStart_938583 baseEnd_938583 := by
    simpa [prefixWord, tailWord_938583, baseEnd_938583] using wordTrace_append hprefix tailTrace_938583
  have hstable : (prefixWord ++ tailWord_938583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938583).length < 2 ^ (prefixWord ++ tailWord_938583).sum := by decide
  have hdescent : baseEnd_938583 < baseStart_938583 := by decide
  rcases family_descends (prefixWord ++ tailWord_938583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938748 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_938748 : Nat := 118140960795 + 938748 * 2 ^ 59
def prefixEnd_938748 : Nat := 4983230072969 + 3 ^ 40 * 938748 * 2
def baseEnd_938748 : Nat := 107117541654888528407285

theorem tailTrace_938748 : CollatzResearch.WordTrace tailWord_938748 prefixEnd_938748 107117541654888528407285 := by
  unfold tailWord_938748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119476201541898119676449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22825968268722530826235265 17119476201541898119676449)
  ·
    refine ⟨12839607151156423589757337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17119476201541898119676449 12839607151156423589757337)
    ·
      refine ⟨9629705363367317692318003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12839607151156423589757337 9629705363367317692318003)
      ·
        refine ⟨14444558045050976538477005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9629705363367317692318003 14444558045050976538477005)
        ·
          refine ⟨5416709266894116201928877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14444558045050976538477005 5416709266894116201928877)
          ·
            refine ⟨2031265975085293575723329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5416709266894116201928877 2031265975085293575723329)
            ·
              refine ⟨1523449481313970181792497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2031265975085293575723329 1523449481313970181792497)
              ·
                refine ⟨1142587110985477636344373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523449481313970181792497 1142587110985477636344373)
                ·
                  refine ⟨107117541654888528407285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1142587110985477636344373 107117541654888528407285)
                  ·
                    rfl

theorem cell22_938748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_938748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938748 prefixEnd_938748 := by exact prefixLift 938748
  have htrace : WordTrace (prefixWord ++ tailWord_938748) baseStart_938748 baseEnd_938748 := by
    simpa [prefixWord, tailWord_938748, baseEnd_938748] using wordTrace_append hprefix tailTrace_938748
  have hstable : (prefixWord ++ tailWord_938748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938748).length < 2 ^ (prefixWord ++ tailWord_938748).sum := by decide
  have hdescent : baseEnd_938748 < baseStart_938748 := by decide
  rcases family_descends (prefixWord ++ tailWord_938748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938761 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_938761 : Nat := 118140960795 + 938761 * 2 ^ 59
def prefixEnd_938761 : Nat := 4983230072969 + 3 ^ 40 * 938761 * 2
def baseEnd_938761 : Nat := 321357075130337884646815

theorem tailTrace_938761 : CollatzResearch.WordTrace tailWord_938761 prefixEnd_938761 321357075130337884646815 := by
  unfold tailWord_938761
  simp only [CollatzResearch.WordTrace]
  refine ⟨34239426552036699459576137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22826284368024466306384091 34239426552036699459576137)
  ·
    refine ⟨25679569914027524594682103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34239426552036699459576137 25679569914027524594682103)
    ·
      refine ⟨38519354871041286892023155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25679569914027524594682103 38519354871041286892023155)
      ·
        refine ⟨57779032306561930338034733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38519354871041286892023155 57779032306561930338034733)
        ·
          refine ⟨21667137114960723876763025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57779032306561930338034733 21667137114960723876763025)
          ·
            refine ⟨16250352836220542907572269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21667137114960723876763025 16250352836220542907572269)
            ·
              refine ⟨6093882313582703590339601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16250352836220542907572269 6093882313582703590339601)
              ·
                refine ⟨4570411735187027692754701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093882313582703590339601 4570411735187027692754701)
                ·
                  refine ⟨1713904400695135384783013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4570411735187027692754701 1713904400695135384783013)
                  ·
                    refine ⟨321357075130337884646815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713904400695135384783013 321357075130337884646815)
                    ·
                      rfl

theorem cell22_938761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_938761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938761 prefixEnd_938761 := by exact prefixLift 938761
  have htrace : WordTrace (prefixWord ++ tailWord_938761) baseStart_938761 baseEnd_938761 := by
    simpa [prefixWord, tailWord_938761, baseEnd_938761] using wordTrace_append hprefix tailTrace_938761
  have hstable : (prefixWord ++ tailWord_938761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938761).length < 2 ^ (prefixWord ++ tailWord_938761).sum := by decide
  have hdescent : baseEnd_938761 < baseStart_938761 := by decide
  rcases family_descends (prefixWord ++ tailWord_938761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938778 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_938778 : Nat := 118140960795 + 938778 * 2 ^ 59
def prefixEnd_938778 : Nat := 4983230072969 + 3 ^ 40 * 938778 * 2
def baseEnd_938778 : Nat := 321362894577755506971763

theorem tailTrace_938778 : CollatzResearch.WordTrace tailWord_938778 prefixEnd_938778 321362894577755506971763 := by
  unfold tailWord_938778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560011648243777840736247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22826697728650074241963325 8560011648243777840736247)
  ·
    refine ⟨12840017472365666761104371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8560011648243777840736247 12840017472365666761104371)
    ·
      refine ⟨19260026208548500141656557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12840017472365666761104371 19260026208548500141656557)
      ·
        refine ⟨7222509828205687553121209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19260026208548500141656557 7222509828205687553121209)
        ·
          refine ⟨5416882371154265664840907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7222509828205687553121209 5416882371154265664840907)
          ·
            refine ⟨8125323556731398497261361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416882371154265664840907 8125323556731398497261361)
            ·
              refine ⟨6093992667548548872946021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8125323556731398497261361 6093992667548548872946021)
              ·
                refine ⟨1142623625165352913677379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6093992667548548872946021 1142623625165352913677379)
                ·
                  refine ⟨1713935437748029370516069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142623625165352913677379 1713935437748029370516069)
                  ·
                    refine ⟨321362894577755506971763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713935437748029370516069 321362894577755506971763)
                    ·
                      rfl

theorem cell22_938778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_938778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938778 prefixEnd_938778 := by exact prefixLift 938778
  have htrace : WordTrace (prefixWord ++ tailWord_938778) baseStart_938778 baseEnd_938778 := by
    simpa [prefixWord, tailWord_938778, baseEnd_938778] using wordTrace_append hprefix tailTrace_938778
  have hstable : (prefixWord ++ tailWord_938778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938778).length < 2 ^ (prefixWord ++ tailWord_938778).sum := by decide
  have hdescent : baseEnd_938778 < baseStart_938778 := by decide
  rcases family_descends (prefixWord ++ tailWord_938778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938808 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_938808 : Nat := 118140960795 + 938808 * 2 ^ 59
def prefixEnd_938808 : Nat := 4983230072969 + 3 ^ 40 * 938808 * 2
def baseEnd_938808 : Nat := 321373164190845428721671

theorem tailTrace_938808 : CollatzResearch.WordTrace tailWord_938808 prefixEnd_938808 321373164190845428721671 := by
  unfold tailWord_938808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120570391433213243268539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22827427188577617657691385 17120570391433213243268539)
  ·
    refine ⟨25680855587149819864902809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17120570391433213243268539 25680855587149819864902809)
    ·
      refine ⟨19260641690362364898677107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25680855587149819864902809 19260641690362364898677107)
      ·
        refine ⟨28890962535543547348015661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19260641690362364898677107 28890962535543547348015661)
        ·
          refine ⟨10834110950828830255505873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28890962535543547348015661 10834110950828830255505873)
          ·
            refine ⟨8125583213121622691629405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10834110950828830255505873 8125583213121622691629405)
            ·
              refine ⟨3047093704920608509361027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8125583213121622691629405 3047093704920608509361027)
              ·
                refine ⟨4570640557380912764041541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047093704920608509361027 4570640557380912764041541)
                ·
                  refine ⟨856995104508921143257789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4570640557380912764041541 856995104508921143257789)
                  ·
                    refine ⟨321373164190845428721671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856995104508921143257789 321373164190845428721671)
                    ·
                      rfl

theorem cell22_938808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_938808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938808 prefixEnd_938808 := by exact prefixLift 938808
  have htrace : WordTrace (prefixWord ++ tailWord_938808) baseStart_938808 baseEnd_938808 := by
    simpa [prefixWord, tailWord_938808, baseEnd_938808] using wordTrace_append hprefix tailTrace_938808
  have hstable : (prefixWord ++ tailWord_938808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938808).length < 2 ^ (prefixWord ++ tailWord_938808).sum := by decide
  have hdescent : baseEnd_938808 < baseStart_938808 := by decide
  rcases family_descends (prefixWord ++ tailWord_938808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938853 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_938853 : Nat := 118140960795 + 938853 * 2 ^ 59
def prefixEnd_938853 : Nat := 4983230072969 + 3 ^ 40 * 938853 * 2
def baseEnd_938853 : Nat := 321388568610480311346533

theorem tailTrace_938853 : CollatzResearch.WordTrace tailWord_938853 prefixEnd_938853 321388568610480311346533 := by
  unfold tailWord_938853
  simp only [CollatzResearch.WordTrace]
  refine ⟨34242782067703399171925213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22828521378468932781283475 34242782067703399171925213)
  ·
    refine ⟨12841043275388774689471955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34242782067703399171925213 12841043275388774689471955)
    ·
      refine ⟨19261564913083162034207933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841043275388774689471955 19261564913083162034207933)
      ·
        refine ⟨7223086842406185762827975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19261564913083162034207933 7223086842406185762827975)
        ·
          refine ⟨10834630263609278644241963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223086842406185762827975 10834630263609278644241963)
          ·
            refine ⟨16251945395413917966362945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10834630263609278644241963 16251945395413917966362945)
            ·
              refine ⟨12188959046560438474772209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16251945395413917966362945 12188959046560438474772209)
              ·
                refine ⟨9141719284920328856079157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12188959046560438474772209 9141719284920328856079157)
                ·
                  refine ⟨857036182961280830257421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9141719284920328856079157 857036182961280830257421)
                  ·
                    refine ⟨321388568610480311346533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857036182961280830257421 321388568610480311346533)
                    ·
                      rfl

theorem cell22_938853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_938853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938853 prefixEnd_938853 := by exact prefixLift 938853
  have htrace : WordTrace (prefixWord ++ tailWord_938853) baseStart_938853 baseEnd_938853 := by
    simpa [prefixWord, tailWord_938853, baseEnd_938853] using wordTrace_append hprefix tailTrace_938853
  have hstable : (prefixWord ++ tailWord_938853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938853).length < 2 ^ (prefixWord ++ tailWord_938853).sum := by decide
  have hdescent : baseEnd_938853 < baseStart_938853 := by decide
  rcases family_descends (prefixWord ++ tailWord_938853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938883 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 5]
def baseStart_938883 : Nat := 118140960795 + 938883 * 2 ^ 59
def prefixEnd_938883 : Nat := 4983230072969 + 3 ^ 40 * 938883 * 2
def baseEnd_938883 : Nat := 107132946074523411032147

theorem tailTrace_938883 : CollatzResearch.WordTrace tailWord_938883 prefixEnd_938883 107132946074523411032147 := by
  unfold tailWord_938883
  simp only [CollatzResearch.WordTrace]
  refine ⟨34243876257594714295517303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22829250838396476197011535 34243876257594714295517303)
  ·
    refine ⟨51365814386392071443275955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34243876257594714295517303 51365814386392071443275955)
    ·
      refine ⟨77048721579588107164913933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51365814386392071443275955 77048721579588107164913933)
      ·
        refine ⟨28893270592345540186842725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77048721579588107164913933 28893270592345540186842725)
        ·
          refine ⟨5417488236064788785033011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28893270592345540186842725 5417488236064788785033011)
          ·
            refine ⟨8126232354097183177549517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417488236064788785033011 8126232354097183177549517)
            ·
              refine ⟨3047337132786443691581069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8126232354097183177549517 3047337132786443691581069)
              ·
                refine ⟨1142751424794916384342901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3047337132786443691581069 1142751424794916384342901)
                ·
                  refine ⟨107132946074523411032147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1142751424794916384342901 107132946074523411032147)
                  ·
                    rfl

theorem cell22_938883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 5].length) (baseStart_938883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938883 prefixEnd_938883 := by exact prefixLift 938883
  have htrace : WordTrace (prefixWord ++ tailWord_938883) baseStart_938883 baseEnd_938883 := by
    simpa [prefixWord, tailWord_938883, baseEnd_938883] using wordTrace_append hprefix tailTrace_938883
  have hstable : (prefixWord ++ tailWord_938883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938883).length < 2 ^ (prefixWord ++ tailWord_938883).sum := by decide
  have hdescent : baseEnd_938883 < baseStart_938883 := by decide
  rcases family_descends (prefixWord ++ tailWord_938883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938932 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_938932 : Nat := 118140960795 + 938932 * 2 ^ 59
def prefixEnd_938932 : Nat := 4983230072969 + 3 ^ 40 * 938932 * 2
def baseEnd_938932 : Nat := 321415611924950438621291

theorem tailTrace_938932 : CollatzResearch.WordTrace tailWord_938932 prefixEnd_938932 321415611924950438621291 := by
  unfold tailWord_938932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17122831717208597832025525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22830442289611463776034033 17122831717208597832025525)
  ·
    refine ⟨1605265473488306046752393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17122831717208597832025525 1605265473488306046752393)
    ·
      refine ⟨1203949105116229535064295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1605265473488306046752393 1203949105116229535064295)
      ·
        refine ⟨1805923657674344302596443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203949105116229535064295 1805923657674344302596443)
        ·
          refine ⟨2708885486511516453894665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805923657674344302596443 2708885486511516453894665)
          ·
            refine ⟨2031664114883637340420999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2708885486511516453894665 2031664114883637340420999)
            ·
              refine ⟨3047496172325456010631499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031664114883637340420999 3047496172325456010631499)
              ·
                refine ⟨4571244258488184015947249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047496172325456010631499 4571244258488184015947249)
                ·
                  refine ⟨3428433193866138011960437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4571244258488184015947249 3428433193866138011960437)
                  ·
                    refine ⟨321415611924950438621291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3428433193866138011960437 321415611924950438621291)
                    ·
                      rfl

theorem cell22_938932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_938932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938932 prefixEnd_938932 := by exact prefixLift 938932
  have htrace : WordTrace (prefixWord ++ tailWord_938932) baseStart_938932 baseEnd_938932 := by
    simpa [prefixWord, tailWord_938932, baseEnd_938932] using wordTrace_append hprefix tailTrace_938932
  have hstable : (prefixWord ++ tailWord_938932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938932).length < 2 ^ (prefixWord ++ tailWord_938932).sum := by decide
  have hdescent : baseEnd_938932 < baseStart_938932 := by decide
  rcases family_descends (prefixWord ++ tailWord_938932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938962 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_938962 : Nat := 118140960795 + 938962 * 2 ^ 59
def prefixEnd_938962 : Nat := 4983230072969 + 3 ^ 40 * 938962 * 2
def baseEnd_938962 : Nat := 107141960512680120123733

theorem tailTrace_938962 : CollatzResearch.WordTrace tailWord_938962 prefixEnd_938962 107141960512680120123733 := by
  unfold tailWord_938962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561689406077127696910785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22831171749539007191762093 8561689406077127696910785)
  ·
    refine ⟨6421267054557845772683089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8561689406077127696910785 6421267054557845772683089)
    ·
      refine ⟨4815950290918384329512317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6421267054557845772683089 4815950290918384329512317)
      ·
        refine ⟨1805981359094394123567119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4815950290918384329512317 1805981359094394123567119)
        ·
          refine ⟨2708972038641591185350679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805981359094394123567119 2708972038641591185350679)
          ·
            refine ⟨4063458057962386778026019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708972038641591185350679 4063458057962386778026019)
            ·
              refine ⟨6095187086943580167039029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063458057962386778026019 6095187086943580167039029)
              ·
                refine ⟨571423789400960640659909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6095187086943580167039029 571423789400960640659909)
                ·
                  refine ⟨107141960512680120123733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571423789400960640659909 107141960512680120123733)
                  ·
                    rfl

theorem cell22_938962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_938962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938962 prefixEnd_938962 := by exact prefixLift 938962
  have htrace : WordTrace (prefixWord ++ tailWord_938962) baseStart_938962 baseEnd_938962 := by
    simpa [prefixWord, tailWord_938962, baseEnd_938962] using wordTrace_append hprefix tailTrace_938962
  have hstable : (prefixWord ++ tailWord_938962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938962).length < 2 ^ (prefixWord ++ tailWord_938962).sum := by decide
  have hdescent : baseEnd_938962 < baseStart_938962 := by decide
  rcases family_descends (prefixWord ++ tailWord_938962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938964 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_938964 : Nat := 118140960795 + 938964 * 2 ^ 59
def prefixEnd_938964 : Nat := 4983230072969 + 3 ^ 40 * 938964 * 2
def baseEnd_938964 : Nat := 321426566178913021821193

theorem tailTrace_938964 : CollatzResearch.WordTrace tailWord_938964 prefixEnd_938964 321426566178913021821193 := by
  unfold tailWord_938964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123415285150632564607973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22831220380200843419477297 17123415285150632564607973)
  ·
    refine ⟨3210640365965743605863995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17123415285150632564607973 3210640365965743605863995)
    ·
      refine ⟨4815960548948615408795993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210640365965743605863995 4815960548948615408795993)
      ·
        refine ⟨3611970411711461556596995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4815960548948615408795993 3611970411711461556596995)
        ·
          refine ⟨5417955617567192334895493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611970411711461556596995 5417955617567192334895493)
          ·
            refine ⟨1015866678293848562792905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5417955617567192334895493 1015866678293848562792905)
            ·
              refine ⟨761900008720386422094679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015866678293848562792905 761900008720386422094679)
              ·
                refine ⟨1142850013080579633142019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761900008720386422094679 1142850013080579633142019)
                ·
                  refine ⟨1714275019620869449713029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142850013080579633142019 1714275019620869449713029)
                  ·
                    refine ⟨321426566178913021821193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714275019620869449713029 321426566178913021821193)
                    ·
                      rfl

theorem cell22_938964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_938964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938964 prefixEnd_938964 := by exact prefixLift 938964
  have htrace : WordTrace (prefixWord ++ tailWord_938964) baseStart_938964 baseEnd_938964 := by
    simpa [prefixWord, tailWord_938964, baseEnd_938964] using wordTrace_append hprefix tailTrace_938964
  have hstable : (prefixWord ++ tailWord_938964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938964).length < 2 ^ (prefixWord ++ tailWord_938964).sum := by decide
  have hdescent : baseEnd_938964 < baseStart_938964 := by decide
  rcases family_descends (prefixWord ++ tailWord_938964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938994 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_938994 : Nat := 118140960795 + 938994 * 2 ^ 59
def prefixEnd_938994 : Nat := 4983230072969 + 3 ^ 40 * 938994 * 2
def baseEnd_938994 : Nat := 321436835792002943571101

theorem tailTrace_938994 : CollatzResearch.WordTrace tailWord_938994 prefixEnd_938994 321436835792002943571101 := by
  unfold tailWord_938994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561981190048145063202009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22831949840128386835205357 8561981190048145063202009)
  ·
    refine ⟨6421485892536108797401507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8561981190048145063202009 6421485892536108797401507)
    ·
      refine ⟨9632228838804163196102261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421485892536108797401507 9632228838804163196102261)
      ·
        refine ⟨903021453637890299634587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9632228838804163196102261 903021453637890299634587)
        ·
          refine ⟨1354532180456835449451881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903021453637890299634587 1354532180456835449451881)
          ·
            refine ⟨1015899135342626587088911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354532180456835449451881 1015899135342626587088911)
            ·
              refine ⟨1523848703013939880633367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015899135342626587088911 1523848703013939880633367)
              ·
                refine ⟨2285773054520909820950051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523848703013939880633367 2285773054520909820950051)
                ·
                  refine ⟨3428659581781364731425077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285773054520909820950051 3428659581781364731425077)
                  ·
                    refine ⟨321436835792002943571101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3428659581781364731425077 321436835792002943571101)
                    ·
                      rfl

theorem cell22_938994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_938994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_938994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_938994 prefixEnd_938994 := by exact prefixLift 938994
  have htrace : WordTrace (prefixWord ++ tailWord_938994) baseStart_938994 baseEnd_938994 := by
    simpa [prefixWord, tailWord_938994, baseEnd_938994] using wordTrace_append hprefix tailTrace_938994
  have hstable : (prefixWord ++ tailWord_938994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938994).length < 2 ^ (prefixWord ++ tailWord_938994).sum := by decide
  have hdescent : baseEnd_938994 < baseStart_938994 := by decide
  rcases family_descends (prefixWord ++ tailWord_938994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939026 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_939026 : Nat := 118140960795 + 939026 * 2 ^ 59
def prefixEnd_939026 : Nat := 4983230072969 + 3 ^ 40 * 939026 * 2
def baseEnd_939026 : Nat := 321447790045965526771003

theorem tailTrace_939026 : CollatzResearch.WordTrace tailWord_939026 prefixEnd_939026 321447790045965526771003 := by
  unfold tailWord_939026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562272974019162429493233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22832727930717766478648621 8562272974019162429493233)
  ·
    refine ⟨6421704730514371822119925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8562272974019162429493233 6421704730514371822119925)
    ·
      refine ⟨602034818485722358323743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6421704730514371822119925 602034818485722358323743)
      ·
        refine ⟨903052227728583537485615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602034818485722358323743 903052227728583537485615)
        ·
          refine ⟨1354578341592875306228423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903052227728583537485615 1354578341592875306228423)
          ·
            refine ⟨2031867512389312959342635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354578341592875306228423 2031867512389312959342635)
            ·
              refine ⟨3047801268583969439013953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031867512389312959342635 3047801268583969439013953)
              ·
                refine ⟨2285850951437977079260465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047801268583969439013953 2285850951437977079260465)
                ·
                  refine ⟨1714388213578482809445349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285850951437977079260465 1714388213578482809445349)
                  ·
                    refine ⟨321447790045965526771003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714388213578482809445349 321447790045965526771003)
                    ·
                      rfl

theorem cell22_939026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_939026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939026 prefixEnd_939026 := by exact prefixLift 939026
  have htrace : WordTrace (prefixWord ++ tailWord_939026) baseStart_939026 baseEnd_939026 := by
    simpa [prefixWord, tailWord_939026, baseEnd_939026] using wordTrace_append hprefix tailTrace_939026
  have hstable : (prefixWord ++ tailWord_939026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939026).length < 2 ^ (prefixWord ++ tailWord_939026).sum := by decide
  have hdescent : baseEnd_939026 < baseStart_939026 := by decide
  rcases family_descends (prefixWord ++ tailWord_939026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939033 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_939033 : Nat := 118140960795 + 939033 * 2 ^ 59
def prefixEnd_939033 : Nat := 4983230072969 + 3 ^ 40 * 939033 * 2
def baseEnd_939033 : Nat := 321450186289019841845981

theorem tailTrace_939033 : CollatzResearch.WordTrace tailWord_939033 prefixEnd_939033 321450186289019841845981 := by
  unfold tailWord_939033
  simp only [CollatzResearch.WordTrace]
  refine ⟨34249347207051289913477753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22832898138034193275651835 34249347207051289913477753)
  ·
    refine ⟨25687010405288467435108315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34249347207051289913477753 25687010405288467435108315)
    ·
      refine ⟨38530515607932701152662473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25687010405288467435108315 38530515607932701152662473)
      ·
        refine ⟨28897886705949525864496855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38530515607932701152662473 28897886705949525864496855)
        ·
          refine ⟨43346830058924288796745283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28897886705949525864496855 43346830058924288796745283)
          ·
            refine ⟨65020245088386433195117925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43346830058924288796745283 65020245088386433195117925)
            ·
              refine ⟨12191295954072456224084611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65020245088386433195117925 12191295954072456224084611)
              ·
                refine ⟨18286943931108684336126917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12191295954072456224084611 18286943931108684336126917)
                ·
                  refine ⟨3428801987082878313023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18286943931108684336126917 3428801987082878313023797)
                  ·
                    refine ⟨321450186289019841845981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3428801987082878313023797 321450186289019841845981)
                    ·
                      rfl

theorem cell22_939033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_939033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939033 prefixEnd_939033 := by exact prefixLift 939033
  have htrace : WordTrace (prefixWord ++ tailWord_939033) baseStart_939033 baseEnd_939033 := by
    simpa [prefixWord, tailWord_939033, baseEnd_939033] using wordTrace_append hprefix tailTrace_939033
  have hstable : (prefixWord ++ tailWord_939033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939033).length < 2 ^ (prefixWord ++ tailWord_939033).sum := by decide
  have hdescent : baseEnd_939033 < baseStart_939033 := by decide
  rcases family_descends (prefixWord ++ tailWord_939033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939063 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 8]
def baseStart_939063 : Nat := 118140960795 + 939063 * 2 ^ 59
def prefixEnd_939063 : Nat := 4983230072969 + 3 ^ 40 * 939063 * 2
def baseEnd_939063 : Nat := 107153485300703254531963

theorem tailTrace_939063 : CollatzResearch.WordTrace tailWord_939063 prefixEnd_939063 107153485300703254531963 := by
  unfold tailWord_939063
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250441396942605037069843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22833627597961736691379895 34250441396942605037069843)
  ·
    refine ⟨51375662095413907555604765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34250441396942605037069843 51375662095413907555604765)
    ·
      refine ⟨19265873285780215333351787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51375662095413907555604765 19265873285780215333351787)
      ·
        refine ⟨28898809928670323000027681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19265873285780215333351787 28898809928670323000027681)
        ·
          refine ⟨21674107446502742250020761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28898809928670323000027681 21674107446502742250020761)
          ·
            refine ⟨16255580584877056687515571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21674107446502742250020761 16255580584877056687515571)
            ·
              refine ⟨24383370877315585031273357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16255580584877056687515571 24383370877315585031273357)
              ·
                refine ⟨9143764078993344386727509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24383370877315585031273357 9143764078993344386727509)
                ·
                  refine ⟨107153485300703254531963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9143764078993344386727509 107153485300703254531963)
                  ·
                    rfl

theorem cell22_939063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_939063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939063 prefixEnd_939063 := by exact prefixLift 939063
  have htrace : WordTrace (prefixWord ++ tailWord_939063) baseStart_939063 baseEnd_939063 := by
    simpa [prefixWord, tailWord_939063, baseEnd_939063] using wordTrace_append hprefix tailTrace_939063
  have hstable : (prefixWord ++ tailWord_939063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939063).length < 2 ^ (prefixWord ++ tailWord_939063).sum := by decide
  have hdescent : baseEnd_939063 < baseStart_939063 := by decide
  rcases family_descends (prefixWord ++ tailWord_939063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939215 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 6]
def baseStart_939215 : Nat := 118140960795 + 939215 * 2 ^ 59
def prefixEnd_939215 : Nat := 4983230072969 + 3 ^ 40 * 939215 * 2
def baseEnd_939215 : Nat := 107170829536144011265141

theorem tailTrace_939215 : CollatzResearch.WordTrace tailWord_939215 prefixEnd_939215 107170829536144011265141 := by
  unfold tailWord_939215
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255985292391934996603099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22837323528261289997735399 34255985292391934996603099)
  ·
    refine ⟨51383977938587902494904649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34255985292391934996603099 51383977938587902494904649)
    ·
      refine ⟨38537983453940926871178487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51383977938587902494904649 38537983453940926871178487)
      ·
        refine ⟨57806975180911390306767731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38537983453940926871178487 57806975180911390306767731)
        ·
          refine ⟨86710462771367085460151597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57806975180911390306767731 86710462771367085460151597)
          ·
            refine ⟨32516423539262657047556849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86710462771367085460151597 32516423539262657047556849)
            ·
              refine ⟨24387317654446992785667637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32516423539262657047556849 24387317654446992785667637)
              ·
                refine ⟨2286311030104405573656341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24387317654446992785667637 2286311030104405573656341)
                ·
                  refine ⟨107170829536144011265141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2286311030104405573656341 107170829536144011265141)
                  ·
                    rfl

theorem cell22_939215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 6].length) (baseStart_939215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939215 prefixEnd_939215 := by exact prefixLift 939215
  have htrace : WordTrace (prefixWord ++ tailWord_939215) baseStart_939215 baseEnd_939215 := by
    simpa [prefixWord, tailWord_939215, baseEnd_939215] using wordTrace_append hprefix tailTrace_939215
  have hstable : (prefixWord ++ tailWord_939215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939215).length < 2 ^ (prefixWord ++ tailWord_939215).sum := by decide
  have hdescent : baseEnd_939215 < baseStart_939215 := by decide
  rcases family_descends (prefixWord ++ tailWord_939215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939221 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 5]
def baseStart_939221 : Nat := 118140960795 + 939221 * 2 ^ 59
def prefixEnd_939221 : Nat := 4983230072969 + 3 ^ 40 * 939221 * 2
def baseEnd_939221 : Nat := 107171514177016672715135

theorem tailTrace_939221 : CollatzResearch.WordTrace tailWord_939221 prefixEnd_939221 107171514177016672715135 := by
  unfold tailWord_939221
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256204130370198021321517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22837469420246798680881011 34256204130370198021321517)
  ·
    refine ⟨12846076548888824257995569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34256204130370198021321517 12846076548888824257995569)
    ·
      refine ⟨9634557411666618193496677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12846076548888824257995569 9634557411666618193496677)
      ·
        refine ⟨1806479514687490911280627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9634557411666618193496677 1806479514687490911280627)
        ·
          refine ⟨2709719272031236366920941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806479514687490911280627 2709719272031236366920941)
          ·
            refine ⟨1016144727011713637595353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2709719272031236366920941 1016144727011713637595353)
            ·
              refine ⟨762108545258785228196515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016144727011713637595353 762108545258785228196515)
              ·
                refine ⟨1143162817888177842294773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762108545258785228196515 1143162817888177842294773)
                ·
                  refine ⟨107171514177016672715135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1143162817888177842294773 107171514177016672715135)
                  ·
                    rfl

theorem cell22_939221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_939221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939221 prefixEnd_939221 := by exact prefixLift 939221
  have htrace : WordTrace (prefixWord ++ tailWord_939221) baseStart_939221 baseEnd_939221 := by
    simpa [prefixWord, tailWord_939221, baseEnd_939221] using wordTrace_append hprefix tailTrace_939221
  have hstable : (prefixWord ++ tailWord_939221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939221).length < 2 ^ (prefixWord ++ tailWord_939221).sum := by decide
  have hdescent : baseEnd_939221 < baseStart_939221 := by decide
  rcases family_descends (prefixWord ++ tailWord_939221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939260 : List Nat := [2, 2, 2, 1, 15]
def baseStart_939260 : Nat := 118140960795 + 939260 * 2 ^ 59
def prefixEnd_939260 : Nat := 4983230072969 + 3 ^ 40 * 939260 * 2
def baseEnd_939260 : Nat := 1323160053613444100495

theorem tailTrace_939260 : CollatzResearch.WordTrace tailWord_939260 prefixEnd_939260 1323160053613444100495 := by
  unfold tailWord_939260
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128813288614453840995617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22838417718152605121327489 17128813288614453840995617)
  ·
    refine ⟨12846609966460840380746713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17128813288614453840995617 12846609966460840380746713)
    ·
      refine ⟨9634957474845630285560035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12846609966460840380746713 9634957474845630285560035)
      ·
        refine ⟨14452436212268445428340053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634957474845630285560035 14452436212268445428340053)
        ·
          refine ⟨1323160053613444100495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 14452436212268445428340053 1323160053613444100495)
          ·
            rfl

theorem cell22_939260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 15].length) (baseStart_939260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939260 prefixEnd_939260 := by exact prefixLift 939260
  have htrace : WordTrace (prefixWord ++ tailWord_939260) baseStart_939260 baseEnd_939260 := by
    simpa [prefixWord, tailWord_939260, baseEnd_939260] using wordTrace_append hprefix tailTrace_939260
  have hstable : (prefixWord ++ tailWord_939260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939260).length < 2 ^ (prefixWord ++ tailWord_939260).sum := by decide
  have hdescent : baseEnd_939260 < baseStart_939260 := by decide
  rcases family_descends (prefixWord ++ tailWord_939260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939296 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_939296 : Nat := 118140960795 + 939296 * 2 ^ 59
def prefixEnd_939296 : Nat := 4983230072969 + 3 ^ 40 * 939296 * 2
def baseEnd_939296 : Nat := 321540216563774822520175

theorem tailTrace_939296 : CollatzResearch.WordTrace tailWord_939296 prefixEnd_939296 321540216563774822520175 := by
  unfold tailWord_939296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17129469802549242915150871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22839293070065657220201161 17129469802549242915150871)
  ·
    refine ⟨25694204703823864372726307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17129469802549242915150871 25694204703823864372726307)
    ·
      refine ⟨38541307055735796559089461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25694204703823864372726307 38541307055735796559089461)
      ·
        refine ⟨3613247536475230927414637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38541307055735796559089461 3613247536475230927414637)
        ·
          refine ⟨1354967826178211597780489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3613247536475230927414637 1354967826178211597780489)
          ·
            refine ⟨1016225869633658698335367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354967826178211597780489 1016225869633658698335367)
            ·
              refine ⟨1524338804450488047503051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016225869633658698335367 1524338804450488047503051)
              ·
                refine ⟨2286508206675732071254577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524338804450488047503051 2286508206675732071254577)
                ·
                  refine ⟨1714881155006799053440933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2286508206675732071254577 1714881155006799053440933)
                  ·
                    refine ⟨321540216563774822520175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714881155006799053440933 321540216563774822520175)
                    ·
                      rfl

theorem cell22_939296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_939296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939296 prefixEnd_939296 := by exact prefixLift 939296
  have htrace : WordTrace (prefixWord ++ tailWord_939296) baseStart_939296 baseEnd_939296 := by
    simpa [prefixWord, tailWord_939296, baseEnd_939296] using wordTrace_append hprefix tailTrace_939296
  have hstable : (prefixWord ++ tailWord_939296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939296).length < 2 ^ (prefixWord ++ tailWord_939296).sum := by decide
  have hdescent : baseEnd_939296 < baseStart_939296 := by decide
  rcases family_descends (prefixWord ++ tailWord_939296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939322 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_939322 : Nat := 118140960795 + 939322 * 2 ^ 59
def prefixEnd_939322 : Nat := 4983230072969 + 3 ^ 40 * 939322 * 2
def baseEnd_939322 : Nat := 107183038965039807123365

theorem tailTrace_939322 : CollatzResearch.WordTrace tailWord_939322 prefixEnd_939322 107183038965039807123365 := by
  unfold tailWord_939322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8564971975751073067687055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22839925268669528180498813 8564971975751073067687055)
  ·
    refine ⟨12847457963626609601530583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8564971975751073067687055 12847457963626609601530583)
    ·
      refine ⟨19271186945439914402295875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12847457963626609601530583 19271186945439914402295875)
      ·
        refine ⟨28906780418159871603443813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19271186945439914402295875 28906780418159871603443813)
        ·
          refine ⟨5420021328404975925645715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28906780418159871603443813 5420021328404975925645715)
          ·
            refine ⟨8130031992607463888468573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420021328404975925645715 8130031992607463888468573)
            ·
              refine ⟨3048761997227798958175715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8130031992607463888468573 3048761997227798958175715)
              ·
                refine ⟨4573142995841698437263573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048761997227798958175715 4573142995841698437263573)
                ·
                  refine ⟨107183038965039807123365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4573142995841698437263573 107183038965039807123365)
                  ·
                    rfl

theorem cell22_939322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_939322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939322 prefixEnd_939322 := by exact prefixLift 939322
  have htrace : WordTrace (prefixWord ++ tailWord_939322) baseStart_939322 baseEnd_939322 := by
    simpa [prefixWord, tailWord_939322, baseEnd_939322] using wordTrace_append hprefix tailTrace_939322
  have hstable : (prefixWord ++ tailWord_939322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939322).length < 2 ^ (prefixWord ++ tailWord_939322).sum := by decide
  have hdescent : baseEnd_939322 < baseStart_939322 := by decide
  rcases family_descends (prefixWord ++ tailWord_939322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939326 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_939326 : Nat := 118140960795 + 939326 * 2 ^ 59
def prefixEnd_939326 : Nat := 4983230072969 + 3 ^ 40 * 939326 * 2
def baseEnd_939326 : Nat := 321550486176864744270083

theorem tailTrace_939326 : CollatzResearch.WordTrace tailWord_939326 prefixEnd_939326 321550486176864744270083 := by
  unfold tailWord_939326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282504224373725119236729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22840022529993200635929221 4282504224373725119236729)
  ·
    refine ⟨3211878168280293839427547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4282504224373725119236729 3211878168280293839427547)
    ·
      refine ⟨4817817252420440759141321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211878168280293839427547 4817817252420440759141321)
      ·
        refine ⟨3613362939315330569355991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4817817252420440759141321 3613362939315330569355991)
        ·
          refine ⟨5420044408972995854033987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613362939315330569355991 5420044408972995854033987)
          ·
            refine ⟨8130066613459493781050981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420044408972995854033987 8130066613459493781050981)
            ·
              refine ⟨1524387490023655083947059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8130066613459493781050981 1524387490023655083947059)
              ·
                refine ⟨2286581235035482625920589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524387490023655083947059 2286581235035482625920589)
                ·
                  refine ⟨857467963138305984720221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2286581235035482625920589 857467963138305984720221)
                  ·
                    refine ⟨321550486176864744270083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857467963138305984720221 321550486176864744270083)
                    ·
                      rfl

theorem cell22_939326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_939326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939326 prefixEnd_939326 := by exact prefixLift 939326
  have htrace : WordTrace (prefixWord ++ tailWord_939326) baseStart_939326 baseEnd_939326 := by
    simpa [prefixWord, tailWord_939326, baseEnd_939326] using wordTrace_append hprefix tailTrace_939326
  have hstable : (prefixWord ++ tailWord_939326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939326).length < 2 ^ (prefixWord ++ tailWord_939326).sum := by decide
  have hdescent : baseEnd_939326 < baseStart_939326 := by decide
  rcases family_descends (prefixWord ++ tailWord_939326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939337 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_939337 : Nat := 118140960795 + 939337 * 2 ^ 59
def prefixEnd_939337 : Nat := 4983230072969 + 3 ^ 40 * 939337 * 2
def baseEnd_939337 : Nat := 321554251701664382245049

theorem tailTrace_939337 : CollatzResearch.WordTrace tailWord_939337 prefixEnd_939337 321554251701664382245049 := by
  unfold tailWord_939337
  simp only [CollatzResearch.WordTrace]
  refine ⟨34260434997949949832544265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22840289998633299888362843 34260434997949949832544265)
  ·
    refine ⟨25695326248462462374408199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34260434997949949832544265 25695326248462462374408199)
    ·
      refine ⟨38542989372693693561612299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25695326248462462374408199 38542989372693693561612299)
      ·
        refine ⟨57814484059040540342418449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38542989372693693561612299 57814484059040540342418449)
        ·
          refine ⟨43360863044280405256813837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57814484059040540342418449 43360863044280405256813837)
          ·
            refine ⟨16260323641605151971305189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43360863044280405256813837 16260323641605151971305189)
            ·
              refine ⟨3048810682800965994619723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16260323641605151971305189 3048810682800965994619723)
              ·
                refine ⟨4573216024201448991929585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048810682800965994619723 4573216024201448991929585)
                ·
                  refine ⟨3429912018151086743947189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573216024201448991929585 3429912018151086743947189)
                  ·
                    refine ⟨321554251701664382245049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3429912018151086743947189 321554251701664382245049)
                    ·
                      rfl

theorem cell22_939337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_939337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939337 prefixEnd_939337 := by exact prefixLift 939337
  have htrace : WordTrace (prefixWord ++ tailWord_939337) baseStart_939337 baseEnd_939337 := by
    simpa [prefixWord, tailWord_939337, baseEnd_939337] using wordTrace_append hprefix tailTrace_939337
  have hstable : (prefixWord ++ tailWord_939337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939337).length < 2 ^ (prefixWord ++ tailWord_939337).sum := by decide
  have hdescent : baseEnd_939337 < baseStart_939337 := by decide
  rcases family_descends (prefixWord ++ tailWord_939337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939397 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_939397 : Nat := 118140960795 + 939397 * 2 ^ 59
def prefixEnd_939397 : Nat := 4983230072969 + 3 ^ 40 * 939397 * 2
def baseEnd_939397 : Nat := 321574790927844225744865

theorem tailTrace_939397 : CollatzResearch.WordTrace tailWord_939397 prefixEnd_939397 321574790927844225744865 := by
  unfold tailWord_939397
  simp only [CollatzResearch.WordTrace]
  refine ⟨34262623377732580079728445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22841748918488386719818963 34262623377732580079728445)
  ·
    refine ⟨12848483766649717529898167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34262623377732580079728445 12848483766649717529898167)
    ·
      refine ⟨19272725649974576294847251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848483766649717529898167 19272725649974576294847251)
      ·
        refine ⟨28909088474961864442270877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19272725649974576294847251 28909088474961864442270877)
        ·
          refine ⟨10840908178110699165851579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28909088474961864442270877 10840908178110699165851579)
          ·
            refine ⟨16261362267166048748777369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840908178110699165851579 16261362267166048748777369)
            ·
              refine ⟨12196021700374536561583027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16261362267166048748777369 12196021700374536561583027)
              ·
                refine ⟨18294032550561804842374541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196021700374536561583027 18294032550561804842374541)
                ·
                  refine ⟨6860262206460676815890453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18294032550561804842374541 6860262206460676815890453)
                  ·
                    refine ⟨321574790927844225744865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6860262206460676815890453 321574790927844225744865)
                    ·
                      rfl

theorem cell22_939397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_939397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939397 prefixEnd_939397 := by exact prefixLift 939397
  have htrace : WordTrace (prefixWord ++ tailWord_939397) baseStart_939397 baseEnd_939397 := by
    simpa [prefixWord, tailWord_939397, baseEnd_939397] using wordTrace_append hprefix tailTrace_939397
  have hstable : (prefixWord ++ tailWord_939397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939397).length < 2 ^ (prefixWord ++ tailWord_939397).sum := by decide
  have hdescent : baseEnd_939397 < baseStart_939397 := by decide
  rcases family_descends (prefixWord ++ tailWord_939397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939416 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_939416 : Nat := 118140960795 + 939416 * 2 ^ 59
def prefixEnd_939416 : Nat := 4983230072969 + 3 ^ 40 * 939416 * 2
def baseEnd_939416 : Nat := 321581295016134509519807

theorem tailTrace_939416 : CollatzResearch.WordTrace tailWord_939416 prefixEnd_939416 321581295016134509519807 := by
  unfold tailWord_939416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17131658182331873162335051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22842210909775830883113401 17131658182331873162335051)
  ·
    refine ⟨25697487273497809743502577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17131658182331873162335051 25697487273497809743502577)
    ·
      refine ⟨19273115455123357307626933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25697487273497809743502577 19273115455123357307626933)
      ·
        refine ⟨1806854573917814747590025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19273115455123357307626933 1806854573917814747590025)
        ·
          refine ⟨1355140930438361060692519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806854573917814747590025 1355140930438361060692519)
          ·
            refine ⟨2032711395657541591038779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355140930438361060692519 2032711395657541591038779)
            ·
              refine ⟨3049067093486312386558169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032711395657541591038779 3049067093486312386558169)
              ·
                refine ⟨2286800320114734289918627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049067093486312386558169 2286800320114734289918627)
                ·
                  refine ⟨3430200480172101434877941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286800320114734289918627 3430200480172101434877941)
                  ·
                    refine ⟨321581295016134509519807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3430200480172101434877941 321581295016134509519807)
                    ·
                      rfl

theorem cell22_939416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_939416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939416 prefixEnd_939416 := by exact prefixLift 939416
  have htrace : WordTrace (prefixWord ++ tailWord_939416) baseStart_939416 baseEnd_939416 := by
    simpa [prefixWord, tailWord_939416, baseEnd_939416] using wordTrace_append hprefix tailTrace_939416
  have hstable : (prefixWord ++ tailWord_939416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939416).length < 2 ^ (prefixWord ++ tailWord_939416).sum := by decide
  have hdescent : baseEnd_939416 < baseStart_939416 := by decide
  rcases family_descends (prefixWord ++ tailWord_939416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939420 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_939420 : Nat := 118140960795 + 939420 * 2 ^ 59
def prefixEnd_939420 : Nat := 4983230072969 + 3 ^ 40 * 939420 * 2
def baseEnd_939420 : Nat := 321582664297879832419795

theorem tailTrace_939420 : CollatzResearch.WordTrace tailWord_939420 prefixEnd_939420 321582664297879832419795 := by
  unfold tailWord_939420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17131731128324627503907857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22842308171099503338543809 17131731128324627503907857)
  ·
    refine ⟨12848798346243470627930893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17131731128324627503907857 12848798346243470627930893)
    ·
      refine ⟨4818299379841301485474085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12848798346243470627930893 4818299379841301485474085)
      ·
        refine ⟨903431133720244028526391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4818299379841301485474085 903431133720244028526391)
        ·
          refine ⟨1355146700580366042789587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903431133720244028526391 1355146700580366042789587)
          ·
            refine ⟨2032720050870549064184381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355146700580366042789587 2032720050870549064184381)
            ·
              refine ⟨762270019076455899069143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2032720050870549064184381 762270019076455899069143)
              ·
                refine ⟨1143405028614683848603715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762270019076455899069143 1143405028614683848603715)
                ·
                  refine ⟨1715107542922025772905573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143405028614683848603715 1715107542922025772905573)
                  ·
                    refine ⟨321582664297879832419795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1715107542922025772905573 321582664297879832419795)
                    ·
                      rfl

theorem cell22_939420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_939420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939420 prefixEnd_939420 := by exact prefixLift 939420
  have htrace : WordTrace (prefixWord ++ tailWord_939420) baseStart_939420 baseEnd_939420 := by
    simpa [prefixWord, tailWord_939420, baseEnd_939420] using wordTrace_append hprefix tailTrace_939420
  have hstable : (prefixWord ++ tailWord_939420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939420).length < 2 ^ (prefixWord ++ tailWord_939420).sum := by decide
  have hdescent : baseEnd_939420 < baseStart_939420 := by decide
  rcases family_descends (prefixWord ++ tailWord_939420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939489 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_939489 : Nat := 118140960795 + 939489 * 2 ^ 59
def prefixEnd_939489 : Nat := 4983230072969 + 3 ^ 40 * 939489 * 2
def baseEnd_939489 : Nat := 321606284407986652444583

theorem tailTrace_939489 : CollatzResearch.WordTrace tailWord_939489 prefixEnd_939489 321606284407986652444583 := by
  unfold tailWord_939489
  simp only [CollatzResearch.WordTrace]
  refine ⟨34265978893399279792077521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22843985928932853194718347 34265978893399279792077521)
  ·
    refine ⟨25699484170049459844058141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34265978893399279792077521 25699484170049459844058141)
    ·
      refine ⟨9637306563768547441521803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25699484170049459844058141 9637306563768547441521803)
      ·
        refine ⟨14455959845652821162282705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9637306563768547441521803 14455959845652821162282705)
        ·
          refine ⟨10841969884239615871712029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14455959845652821162282705 10841969884239615871712029)
          ·
            refine ⟨4065738706589855951892011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10841969884239615871712029 4065738706589855951892011)
            ·
              refine ⟨6098608059884783927838017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065738706589855951892011 6098608059884783927838017)
              ·
                refine ⟨4573956044913587945878513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098608059884783927838017 4573956044913587945878513)
                ·
                  refine ⟨3430467033685190959408885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573956044913587945878513 3430467033685190959408885)
                  ·
                    refine ⟨321606284407986652444583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3430467033685190959408885 321606284407986652444583)
                    ·
                      rfl

theorem cell22_939489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_939489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939489 prefixEnd_939489 := by exact prefixLift 939489
  have htrace : WordTrace (prefixWord ++ tailWord_939489) baseStart_939489 baseEnd_939489 := by
    simpa [prefixWord, tailWord_939489, baseEnd_939489] using wordTrace_append hprefix tailTrace_939489
  have hstable : (prefixWord ++ tailWord_939489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939489).length < 2 ^ (prefixWord ++ tailWord_939489).sum := by decide
  have hdescent : baseEnd_939489 < baseStart_939489 := by decide
  rcases family_descends (prefixWord ++ tailWord_939489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939491 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 5]
def baseStart_939491 : Nat := 118140960795 + 939491 * 2 ^ 59
def prefixEnd_939491 : Nat := 4983230072969 + 3 ^ 40 * 939491 * 2
def baseEnd_939491 : Nat := 107202323016286437964859

theorem tailTrace_939491 : CollatzResearch.WordTrace tailWord_939491 prefixEnd_939491 107202323016286437964859 := by
  unfold tailWord_939491
  simp only [CollatzResearch.WordTrace]
  refine ⟨34266051839392034133650327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22844034559594689422433551 34266051839392034133650327)
  ·
    refine ⟨51399077759088051200475491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34266051839392034133650327 51399077759088051200475491)
    ·
      refine ⟨77098616638632076800713237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51399077759088051200475491 77098616638632076800713237)
      ·
        refine ⟨3613997654935878600033433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77098616638632076800713237 3613997654935878600033433)
        ·
          refine ⟨2710498241201908950025075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613997654935878600033433 2710498241201908950025075)
          ·
            refine ⟨4065747361802863425037613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710498241201908950025075 4065747361802863425037613)
            ·
              refine ⟨1524655260676073784389105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4065747361802863425037613 1524655260676073784389105)
              ·
                refine ⟨1143491445507055338291829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524655260676073784389105 1143491445507055338291829)
                ·
                  refine ⟨107202323016286437964859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1143491445507055338291829 107202323016286437964859)
                  ·
                    rfl

theorem cell22_939491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 5].length) (baseStart_939491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939491 prefixEnd_939491 := by exact prefixLift 939491
  have htrace : WordTrace (prefixWord ++ tailWord_939491) baseStart_939491 baseEnd_939491 := by
    simpa [prefixWord, tailWord_939491, baseEnd_939491] using wordTrace_append hprefix tailTrace_939491
  have hstable : (prefixWord ++ tailWord_939491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939491).length < 2 ^ (prefixWord ++ tailWord_939491).sum := by decide
  have hdescent : baseEnd_939491 < baseStart_939491 := by decide
  rcases family_descends (prefixWord ++ tailWord_939491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939506 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_939506 : Nat := 118140960795 + 939506 * 2 ^ 59
def prefixEnd_939506 : Nat := 4983230072969 + 3 ^ 40 * 939506 * 2
def baseEnd_939506 : Nat := 321612103855404274769531

theorem tailTrace_939506 : CollatzResearch.WordTrace tailWord_939506 prefixEnd_939506 321612103855404274769531 := by
  unfold tailWord_939506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566649733584422923861593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22844399289558461130297581 8566649733584422923861593)
  ·
    refine ⟨6424987300188317192896195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8566649733584422923861593 6424987300188317192896195)
    ·
      refine ⟨9637480950282475789344293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424987300188317192896195 9637480950282475789344293)
      ·
        refine ⟨1807027678177964210502055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9637480950282475789344293 1807027678177964210502055)
        ·
          refine ⟨2710541517266946315753083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807027678177964210502055 2710541517266946315753083)
          ·
            refine ⟨4065812275900419473629625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710541517266946315753083 4065812275900419473629625)
            ·
              refine ⟨3049359206925314605222219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065812275900419473629625 3049359206925314605222219)
              ·
                refine ⟨4574038810387971907833329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049359206925314605222219 4574038810387971907833329)
                ·
                  refine ⟨3430529107790978930874997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574038810387971907833329 3430529107790978930874997)
                  ·
                    refine ⟨321612103855404274769531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3430529107790978930874997 321612103855404274769531)
                    ·
                      rfl

theorem cell22_939506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_939506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939506 prefixEnd_939506 := by exact prefixLift 939506
  have htrace : WordTrace (prefixWord ++ tailWord_939506) baseStart_939506 baseEnd_939506 := by
    simpa [prefixWord, tailWord_939506, baseEnd_939506] using wordTrace_append hprefix tailTrace_939506
  have hstable : (prefixWord ++ tailWord_939506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939506).length < 2 ^ (prefixWord ++ tailWord_939506).sum := by decide
  have hdescent : baseEnd_939506 < baseStart_939506 := by decide
  rcases family_descends (prefixWord ++ tailWord_939506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939551 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 4, 3]
def baseStart_939551 : Nat := 118140960795 + 939551 * 2 ^ 59
def prefixEnd_939551 : Nat := 4983230072969 + 3 ^ 40 * 939551 * 2
def baseEnd_939551 : Nat := 321627508275039157394393

theorem tailTrace_939551 : CollatzResearch.WordTrace tailWord_939551 prefixEnd_939551 321627508275039157394393 := by
  unfold tailWord_939551
  simp only [CollatzResearch.WordTrace]
  refine ⟨34268240219174664380834507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22845493479449776253889671 34268240219174664380834507)
  ·
    refine ⟨51402360328761996571251761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34268240219174664380834507 51402360328761996571251761)
    ·
      refine ⟨38551770246571497428438821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51402360328761996571251761 38551770246571497428438821)
      ·
        refine ⟨7228456921232155767832279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38551770246571497428438821 7228456921232155767832279)
        ·
          refine ⟨10842685381848233651748419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228456921232155767832279 10842685381848233651748419)
          ·
            refine ⟨16264028072772350477622629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10842685381848233651748419 16264028072772350477622629)
            ·
              refine ⟨3049505263644815714554243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16264028072772350477622629 3049505263644815714554243)
              ·
                refine ⟨4574257895467223571831365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049505263644815714554243 4574257895467223571831365)
                ·
                  refine ⟨857673355400104419718381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4574257895467223571831365 857673355400104419718381)
                  ·
                    refine ⟨321627508275039157394393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857673355400104419718381 321627508275039157394393)
                    ·
                      rfl

theorem cell22_939551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_939551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939551 prefixEnd_939551 := by exact prefixLift 939551
  have htrace : WordTrace (prefixWord ++ tailWord_939551) baseStart_939551 baseEnd_939551 := by
    simpa [prefixWord, tailWord_939551, baseEnd_939551] using wordTrace_append hprefix tailTrace_939551
  have hstable : (prefixWord ++ tailWord_939551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939551).length < 2 ^ (prefixWord ++ tailWord_939551).sum := by decide
  have hdescent : baseEnd_939551 < baseStart_939551 := by decide
  rcases family_descends (prefixWord ++ tailWord_939551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939609 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 7]
def baseStart_939609 : Nat := 118140960795 + 939609 * 2 ^ 59
def prefixEnd_939609 : Nat := 4983230072969 + 3 ^ 40 * 939609 * 2
def baseEnd_939609 : Nat := 107215787620115446481405

theorem tailTrace_939609 : CollatzResearch.WordTrace tailWord_939609 prefixEnd_939609 107215787620115446481405 := by
  unfold tailWord_939609
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270355652964540286445881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22846903768643026857630587 34270355652964540286445881)
  ·
    refine ⟨25702766739723405214834411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34270355652964540286445881 25702766739723405214834411)
    ·
      refine ⟨38554150109585107822251617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25702766739723405214834411 38554150109585107822251617)
      ·
        refine ⟨28915612582188830866688713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38554150109585107822251617 28915612582188830866688713)
        ·
          refine ⟨21686709436641623150016535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28915612582188830866688713 21686709436641623150016535)
          ·
            refine ⟨32530064154962434725024803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21686709436641623150016535 32530064154962434725024803)
            ·
              refine ⟨48795096232443652087537205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32530064154962434725024803 48795096232443652087537205)
              ·
                refine ⟨4574540271791592383206613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48795096232443652087537205 4574540271791592383206613)
                ·
                  refine ⟨107215787620115446481405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4574540271791592383206613 107215787620115446481405)
                  ·
                    rfl

theorem cell22_939609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_939609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939609 prefixEnd_939609 := by exact prefixLift 939609
  have htrace : WordTrace (prefixWord ++ tailWord_939609) baseStart_939609 baseEnd_939609 := by
    simpa [prefixWord, tailWord_939609, baseEnd_939609] using wordTrace_append hprefix tailTrace_939609
  have hstable : (prefixWord ++ tailWord_939609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939609).length < 2 ^ (prefixWord ++ tailWord_939609).sum := by decide
  have hdescent : baseEnd_939609 < baseStart_939609 := by decide
  rcases family_descends (prefixWord ++ tailWord_939609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939630 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_939630 : Nat := 118140960795 + 939630 * 2 ^ 59
def prefixEnd_939630 : Nat := 4983230072969 + 3 ^ 40 * 939630 * 2
def baseEnd_939630 : Nat := 321654551589509284669151

theorem tailTrace_939630 : CollatzResearch.WordTrace tailWord_939630 prefixEnd_939630 321654551589509284669151 := by
  unfold tailWord_939630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283890198236057609120043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22847414390592307248640229 4283890198236057609120043)
  ·
    refine ⟨6425835297354086413680065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4283890198236057609120043 6425835297354086413680065)
    ·
      refine ⟨4819376473015564810260049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6425835297354086413680065 4819376473015564810260049)
      ·
        refine ⟨3614532354761673607695037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4819376473015564810260049 3614532354761673607695037)
        ·
          refine ⟨1355449633035627602885639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3614532354761673607695037 1355449633035627602885639)
          ·
            refine ⟨2033174449553441404328459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355449633035627602885639 2033174449553441404328459)
            ·
              refine ⟨3049761674330162106492689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033174449553441404328459 3049761674330162106492689)
              ·
                refine ⟨2287321255747621579869517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049761674330162106492689 2287321255747621579869517)
                ·
                  refine ⟨857745470905358092451069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2287321255747621579869517 857745470905358092451069)
                  ·
                    refine ⟨321654551589509284669151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857745470905358092451069 321654551589509284669151)
                    ·
                      rfl

theorem cell22_939630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_939630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939630 prefixEnd_939630 := by exact prefixLift 939630
  have htrace : WordTrace (prefixWord ++ tailWord_939630) baseStart_939630 baseEnd_939630 := by
    simpa [prefixWord, tailWord_939630, baseEnd_939630] using wordTrace_append hprefix tailTrace_939630
  have hstable : (prefixWord ++ tailWord_939630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939630).length < 2 ^ (prefixWord ++ tailWord_939630).sum := by decide
  have hdescent : baseEnd_939630 < baseStart_939630 := by decide
  rcases family_descends (prefixWord ++ tailWord_939630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939671 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 6]
def baseStart_939671 : Nat := 118140960795 + 939671 * 2 ^ 59
def prefixEnd_939671 : Nat := 4983230072969 + 3 ^ 40 * 939671 * 2
def baseEnd_939671 : Nat := 107222862242466281464675

theorem tailTrace_939671 : CollatzResearch.WordTrace tailWord_939671 prefixEnd_939671 107222862242466281464675 := by
  unfold tailWord_939671
  simp only [CollatzResearch.WordTrace]
  refine ⟨34272616978739924875202867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22848411319159949916801911 34272616978739924875202867)
  ·
    refine ⟨51408925468109887312804301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34272616978739924875202867 51408925468109887312804301)
    ·
      refine ⟨19278347050541207742301613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51408925468109887312804301 19278347050541207742301613)
      ·
        refine ⟨7229380143952952903363105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19278347050541207742301613 7229380143952952903363105)
        ·
          refine ⟨5422035107964714677522329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7229380143952952903363105 5422035107964714677522329)
          ·
            refine ⟨4066526330973536008141747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5422035107964714677522329 4066526330973536008141747)
            ·
              refine ⟨6099789496460304012212621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066526330973536008141747 6099789496460304012212621)
              ·
                refine ⟨2287421061172614004579733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6099789496460304012212621 2287421061172614004579733)
                ·
                  refine ⟨107222862242466281464675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2287421061172614004579733 107222862242466281464675)
                  ·
                    rfl

theorem cell22_939671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 6].length) (baseStart_939671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939671 prefixEnd_939671 := by exact prefixLift 939671
  have htrace : WordTrace (prefixWord ++ tailWord_939671) baseStart_939671 baseEnd_939671 := by
    simpa [prefixWord, tailWord_939671, baseEnd_939671] using wordTrace_append hprefix tailTrace_939671
  have hstable : (prefixWord ++ tailWord_939671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939671).length < 2 ^ (prefixWord ++ tailWord_939671).sum := by decide
  have hdescent : baseEnd_939671 < baseStart_939671 := by decide
  rcases family_descends (prefixWord ++ tailWord_939671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939703 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 4, 3]
def baseStart_939703 : Nat := 118140960795 + 939703 * 2 ^ 59
def prefixEnd_939703 : Nat := 4983230072969 + 3 ^ 40 * 939703 * 2
def baseEnd_939703 : Nat := 321679540981361427593927

theorem tailTrace_939703 : CollatzResearch.WordTrace tailWord_939703 prefixEnd_939703 321679540981361427593927 := by
  unfold tailWord_939703
  simp only [CollatzResearch.WordTrace]
  refine ⟨34273784114623994340367763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22849189409749329560245175 34273784114623994340367763)
  ·
    refine ⟨51410676171935991510551645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34273784114623994340367763 51410676171935991510551645)
    ·
      refine ⟨19279003564475996816456867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51410676171935991510551645 19279003564475996816456867)
      ·
        refine ⟨28918505346713995224685301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19279003564475996816456867 28918505346713995224685301)
        ·
          refine ⟨2711109876254437052314247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28918505346713995224685301 2711109876254437052314247)
          ·
            refine ⟨4066664814381655578471371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711109876254437052314247 4066664814381655578471371)
            ·
              refine ⟨6099997221572483367707057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066664814381655578471371 6099997221572483367707057)
              ·
                refine ⟨4574997916179362525780293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099997221572483367707057 4574997916179362525780293)
                ·
                  refine ⟨857812109283630473583805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4574997916179362525780293 857812109283630473583805)
                  ·
                    refine ⟨321679540981361427593927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857812109283630473583805 321679540981361427593927)
                    ·
                      rfl

theorem cell22_939703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_939703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939703 prefixEnd_939703 := by exact prefixLift 939703
  have htrace : WordTrace (prefixWord ++ tailWord_939703) baseStart_939703 baseEnd_939703 := by
    simpa [prefixWord, tailWord_939703, baseEnd_939703] using wordTrace_append hprefix tailTrace_939703
  have hstable : (prefixWord ++ tailWord_939703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939703).length < 2 ^ (prefixWord ++ tailWord_939703).sum := by decide
  have hdescent : baseEnd_939703 < baseStart_939703 := by decide
  rcases family_descends (prefixWord ++ tailWord_939703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939722 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_939722 : Nat := 118140960795 + 939722 * 2 ^ 59
def prefixEnd_939722 : Nat := 4983230072969 + 3 ^ 40 * 939722 * 2
def baseEnd_939722 : Nat := 107228681689883903789623

theorem tailTrace_939722 : CollatzResearch.WordTrace tailWord_939722 prefixEnd_939722 107228681689883903789623 := by
  unfold tailWord_939722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568619275388790146327355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22849651401036773723539613 8568619275388790146327355)
  ·
    refine ⟨12852928913083185219491033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8568619275388790146327355 12852928913083185219491033)
    ·
      refine ⟨9639696684812388914618275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12852928913083185219491033 9639696684812388914618275)
      ·
        refine ⟨14459545027218583371927413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639696684812388914618275 14459545027218583371927413)
        ·
          refine ⟨1355582346301742191118195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14459545027218583371927413 1355582346301742191118195)
          ·
            refine ⟨2033373519452613286677293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355582346301742191118195 2033373519452613286677293)
            ·
              refine ⟨762515069794729982503985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2033373519452613286677293 762515069794729982503985)
              ·
                refine ⟨571886302346047486877989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762515069794729982503985 571886302346047486877989)
                ·
                  refine ⟨107228681689883903789623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571886302346047486877989 107228681689883903789623)
                  ·
                    rfl

theorem cell22_939722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_939722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939722 prefixEnd_939722 := by exact prefixLift 939722
  have htrace : WordTrace (prefixWord ++ tailWord_939722) baseStart_939722 baseEnd_939722 := by
    simpa [prefixWord, tailWord_939722, baseEnd_939722] using wordTrace_append hprefix tailTrace_939722
  have hstable : (prefixWord ++ tailWord_939722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939722).length < 2 ^ (prefixWord ++ tailWord_939722).sum := by decide
  have hdescent : baseEnd_939722 < baseStart_939722 := by decide
  rcases family_descends (prefixWord ++ tailWord_939722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939737 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 2, 3]
def baseStart_939737 : Nat := 118140960795 + 939737 * 2 ^ 59
def prefixEnd_939737 : Nat := 4983230072969 + 3 ^ 40 * 939737 * 2
def baseEnd_939737 : Nat := 321691179876196672243823

theorem tailTrace_939737 : CollatzResearch.WordTrace tailWord_939737 prefixEnd_939737 321691179876196672243823 := by
  unfold tailWord_939737
  simp only [CollatzResearch.WordTrace]
  refine ⟨34275024196500818147105465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22850016131000545431403643 34275024196500818147105465)
  ·
    refine ⟨25706268147375613610329099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34275024196500818147105465 25706268147375613610329099)
    ·
      refine ⟨38559402221063420415493649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25706268147375613610329099 38559402221063420415493649)
      ·
        refine ⟨28919551665797565311620237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38559402221063420415493649 28919551665797565311620237)
        ·
          refine ⟨10844831874674086991857589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28919551665797565311620237 10844831874674086991857589)
          ·
            refine ⟨1016702988250695655486649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10844831874674086991857589 1016702988250695655486649)
            ·
              refine ⟨762527241188021741614987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016702988250695655486649 762527241188021741614987)
              ·
                refine ⟨1143790861782032612422481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762527241188021741614987 1143790861782032612422481)
                ·
                  refine ⟨857843146336524459316861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143790861782032612422481 857843146336524459316861)
                  ·
                    refine ⟨321691179876196672243823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857843146336524459316861 321691179876196672243823)
                    ·
                      rfl

theorem cell22_939737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_939737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939737 prefixEnd_939737 := by exact prefixLift 939737
  have htrace : WordTrace (prefixWord ++ tailWord_939737) baseStart_939737 baseEnd_939737 := by
    simpa [prefixWord, tailWord_939737, baseEnd_939737] using wordTrace_append hprefix tailTrace_939737
  have hstable : (prefixWord ++ tailWord_939737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939737).length < 2 ^ (prefixWord ++ tailWord_939737).sum := by decide
  have hdescent : baseEnd_939737 < baseStart_939737 := by decide
  rcases family_descends (prefixWord ++ tailWord_939737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939748 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_939748 : Nat := 118140960795 + 939748 * 2 ^ 59
def prefixEnd_939748 : Nat := 4983230072969 + 3 ^ 40 * 939748 * 2
def baseEnd_939748 : Nat := 321694945400996310218789

theorem tailTrace_939748 : CollatzResearch.WordTrace tailWord_939748 prefixEnd_939748 321694945400996310218789 := by
  unfold tailWord_939748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17137712699730483512877949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22850283599640644683837265 17137712699730483512877949)
  ·
    refine ⟨6426642262398931317329231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17137712699730483512877949 6426642262398931317329231)
    ·
      refine ⟨9639963393598396975993847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426642262398931317329231 9639963393598396975993847)
      ·
        refine ⟨14459945090397595463990771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639963393598396975993847 14459945090397595463990771)
        ·
          refine ⟨21689917635596393195986157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14459945090397595463990771 21689917635596393195986157)
          ·
            refine ⟨8133719113348647448494809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21689917635596393195986157 8133719113348647448494809)
            ·
              refine ⟨6100289335011485586371107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8133719113348647448494809 6100289335011485586371107)
              ·
                refine ⟨9150434002517228379556661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100289335011485586371107 9150434002517228379556661)
                ·
                  refine ⟨857853187735990160583437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9150434002517228379556661 857853187735990160583437)
                  ·
                    refine ⟨321694945400996310218789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 857853187735990160583437 321694945400996310218789)
                    ·
                      rfl

theorem cell22_939748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_939748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939748 prefixEnd_939748 := by exact prefixLift 939748
  have htrace : WordTrace (prefixWord ++ tailWord_939748) baseStart_939748 baseEnd_939748 := by
    simpa [prefixWord, tailWord_939748, baseEnd_939748] using wordTrace_append hprefix tailTrace_939748
  have hstable : (prefixWord ++ tailWord_939748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939748).length < 2 ^ (prefixWord ++ tailWord_939748).sum := by decide
  have hdescent : baseEnd_939748 < baseStart_939748 := by decide
  rcases family_descends (prefixWord ++ tailWord_939748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939776 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_939776 : Nat := 118140960795 + 939776 * 2 ^ 59
def prefixEnd_939776 : Nat := 4983230072969 + 3 ^ 40 * 939776 * 2
def baseEnd_939776 : Nat := 321704530373213570518703

theorem tailTrace_939776 : CollatzResearch.WordTrace tailWord_939776 prefixEnd_939776 321704530373213570518703 := by
  unfold tailWord_939776
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138223321679763903887591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22850964428906351871850121 17138223321679763903887591)
  ·
    refine ⟨25707334982519645855831387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17138223321679763903887591 25707334982519645855831387)
    ·
      refine ⟨38561002473779468783747081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25707334982519645855831387 38561002473779468783747081)
      ·
        refine ⟨28920751855334601587810311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38561002473779468783747081 28920751855334601587810311)
        ·
          refine ⟨43381127783001902381715467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920751855334601587810311 43381127783001902381715467)
          ·
            refine ⟨65071691674502853572573201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43381127783001902381715467 65071691674502853572573201)
            ·
              refine ⟨48803768755877140179429901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65071691674502853572573201 48803768755877140179429901)
              ·
                refine ⟨18301413283453927567286213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48803768755877140179429901 18301413283453927567286213)
                ·
                  refine ⟨3431514990647611418866165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18301413283453927567286213 3431514990647611418866165)
                  ·
                    refine ⟨321704530373213570518703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3431514990647611418866165 321704530373213570518703)
                    ·
                      rfl

theorem cell22_939776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_939776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939776 prefixEnd_939776 := by exact prefixLift 939776
  have htrace : WordTrace (prefixWord ++ tailWord_939776) baseStart_939776 baseEnd_939776 := by
    simpa [prefixWord, tailWord_939776, baseEnd_939776] using wordTrace_append hprefix tailTrace_939776
  have hstable : (prefixWord ++ tailWord_939776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939776).length < 2 ^ (prefixWord ++ tailWord_939776).sum := by decide
  have hdescent : baseEnd_939776 < baseStart_939776 := by decide
  rcases family_descends (prefixWord ++ tailWord_939776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939808 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_939808 : Nat := 118140960795 + 939808 * 2 ^ 59
def prefixEnd_939808 : Nat := 4983230072969 + 3 ^ 40 * 939808 * 2
def baseEnd_939808 : Nat := 321715484627176153718605

theorem tailTrace_939808 : CollatzResearch.WordTrace tailWord_939808 prefixEnd_939808 321715484627176153718605 := by
  unfold tailWord_939808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138806889621798636470039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22851742519495731515293385 17138806889621798636470039)
  ·
    refine ⟨25708210334432697954705059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17138806889621798636470039 25708210334432697954705059)
    ·
      refine ⟨38562315501649046932057589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25708210334432697954705059 38562315501649046932057589)
      ·
        refine ⟨3615217078279598149880399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38562315501649046932057589 3615217078279598149880399)
        ·
          refine ⟨5422825617419397224820599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615217078279598149880399 5422825617419397224820599)
          ·
            refine ⟨8134238426129095837230899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422825617419397224820599 8134238426129095837230899)
            ·
              refine ⟨12201357639193643755846349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134238426129095837230899 12201357639193643755846349)
              ·
                refine ⟨4575509114697616408442381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12201357639193643755846349 4575509114697616408442381)
                ·
                  refine ⟨1715815918011606153165893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4575509114697616408442381 1715815918011606153165893)
                  ·
                    refine ⟨321715484627176153718605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1715815918011606153165893 321715484627176153718605)
                    ·
                      rfl

theorem cell22_939808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_939808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939808 prefixEnd_939808 := by exact prefixLift 939808
  have htrace : WordTrace (prefixWord ++ tailWord_939808) baseStart_939808 baseEnd_939808 := by
    simpa [prefixWord, tailWord_939808, baseEnd_939808] using wordTrace_append hprefix tailTrace_939808
  have hstable : (prefixWord ++ tailWord_939808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939808).length < 2 ^ (prefixWord ++ tailWord_939808).sum := by decide
  have hdescent : baseEnd_939808 < baseStart_939808 := by decide
  rcases family_descends (prefixWord ++ tailWord_939808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939825 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_939825 : Nat := 118140960795 + 939825 * 2 ^ 59
def prefixEnd_939825 : Nat := 4983230072969 + 3 ^ 40 * 939825 * 2
def baseEnd_939825 : Nat := 321721304074593776043553

theorem tailTrace_939825 : CollatzResearch.WordTrace tailWord_939825 prefixEnd_939825 321721304074593776043553 := by
  unfold tailWord_939825
  simp only [CollatzResearch.WordTrace]
  refine ⟨34278233820182009176308929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22852155880121339450872619 34278233820182009176308929)
  ·
    refine ⟨25708675365136506882231697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34278233820182009176308929 25708675365136506882231697)
    ·
      refine ⟨19281506523852380161673773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25708675365136506882231697 19281506523852380161673773)
      ·
        refine ⟨7230564946444642560627665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19281506523852380161673773 7230564946444642560627665)
        ·
          refine ⟨5422923709833481920470749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7230564946444642560627665 5422923709833481920470749)
          ·
            refine ⟨2033596391187555720176531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5422923709833481920470749 2033596391187555720176531)
            ·
              refine ⟨3050394586781333580264797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033596391187555720176531 3050394586781333580264797)
              ·
                refine ⟨1143897970043000092599299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3050394586781333580264797 1143897970043000092599299)
                ·
                  refine ⟨1715846955064500138898949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143897970043000092599299 1715846955064500138898949)
                  ·
                    refine ⟨321721304074593776043553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1715846955064500138898949 321721304074593776043553)
                    ·
                      rfl

theorem cell22_939825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_939825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939825 prefixEnd_939825 := by exact prefixLift 939825
  have htrace : WordTrace (prefixWord ++ tailWord_939825) baseStart_939825 baseEnd_939825 := by
    simpa [prefixWord, tailWord_939825, baseEnd_939825] using wordTrace_append hprefix tailTrace_939825
  have hstable : (prefixWord ++ tailWord_939825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939825).length < 2 ^ (prefixWord ++ tailWord_939825).sum := by decide
  have hdescent : baseEnd_939825 < baseStart_939825 := by decide
  rcases family_descends (prefixWord ++ tailWord_939825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939874 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_939874 : Nat := 118140960795 + 939874 * 2 ^ 59
def prefixEnd_939874 : Nat := 4983230072969 + 3 ^ 40 * 939874 * 2
def baseEnd_939874 : Nat := 107246025925324660522801

theorem tailTrace_939874 : CollatzResearch.WordTrace tailWord_939874 prefixEnd_939874 107246025925324660522801 := by
  unfold tailWord_939874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8570005249251122636210669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22853347331336327029895117 8570005249251122636210669)
  ·
    refine ⟨3213751968469170988579001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8570005249251122636210669 3213751968469170988579001)
    ·
      refine ⟨2410313976351878241434251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3213751968469170988579001 2410313976351878241434251)
      ·
        refine ⟨3615470964527817362151377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410313976351878241434251 3615470964527817362151377)
        ·
          refine ⟨2711603223395863021613533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3615470964527817362151377 2711603223395863021613533)
          ·
            refine ⟨1016851208773448633105075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2711603223395863021613533 1016851208773448633105075)
            ·
              refine ⟨1525276813160172949657613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016851208773448633105075 1525276813160172949657613)
              ·
                refine ⟨571978804935064856121605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525276813160172949657613 571978804935064856121605)
                ·
                  refine ⟨107246025925324660522801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571978804935064856121605 107246025925324660522801)
                  ·
                    rfl

theorem cell22_939874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_939874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939874 prefixEnd_939874 := by exact prefixLift 939874
  have htrace : WordTrace (prefixWord ++ tailWord_939874) baseStart_939874 baseEnd_939874 := by
    simpa [prefixWord, tailWord_939874, baseEnd_939874] using wordTrace_append hprefix tailTrace_939874
  have hstable : (prefixWord ++ tailWord_939874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939874).length < 2 ^ (prefixWord ++ tailWord_939874).sum := by decide
  have hdescent : baseEnd_939874 < baseStart_939874 := by decide
  rcases family_descends (prefixWord ++ tailWord_939874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939902 : List Nat := [4, 2, 3, 1, 1, 2, 2, 7]
def baseStart_939902 : Nat := 118140960795 + 939902 * 2 ^ 59
def prefixEnd_939902 : Nat := 4983230072969 + 3 ^ 40 * 939902 * 2
def baseEnd_939902 : Nat := 35749740305354582429813

theorem tailTrace_939902 : CollatzResearch.WordTrace tailWord_939902 prefixEnd_939902 35749740305354582429813 := by
  unfold tailWord_939902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285130280112881415857745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22854028160602034217907973 4285130280112881415857745)
  ·
    refine ⟨3213847710084661061893309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4285130280112881415857745 3213847710084661061893309)
    ·
      refine ⟨1205192891281747898209991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3213847710084661061893309 1205192891281747898209991)
      ·
        refine ⟨1807789336922621847314987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205192891281747898209991 1807789336922621847314987)
        ·
          refine ⟨2711684005383932770972481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807789336922621847314987 2711684005383932770972481)
          ·
            refine ⟨2033763004037949578229361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711684005383932770972481 2033763004037949578229361)
            ·
              refine ⟨1525322253028462183672021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033763004037949578229361 1525322253028462183672021)
              ·
                refine ⟨35749740305354582429813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1525322253028462183672021 35749740305354582429813)
                ·
                  rfl

theorem cell22_939902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_939902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939902 prefixEnd_939902 := by exact prefixLift 939902
  have htrace : WordTrace (prefixWord ++ tailWord_939902) baseStart_939902 baseEnd_939902 := by
    simpa [prefixWord, tailWord_939902, baseEnd_939902] using wordTrace_append hprefix tailTrace_939902
  have hstable : (prefixWord ++ tailWord_939902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939902).length < 2 ^ (prefixWord ++ tailWord_939902).sum := by decide
  have hdescent : baseEnd_939902 < baseStart_939902 := by decide
  rcases family_descends (prefixWord ++ tailWord_939902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939992 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 4]
def baseStart_939992 : Nat := 118140960795 + 939992 * 2 ^ 59
def prefixEnd_939992 : Nat := 4983230072969 + 3 ^ 40 * 939992 * 2
def baseEnd_939992 : Nat := 107259490529153669039347

theorem tailTrace_939992 : CollatzResearch.WordTrace tailWord_939992 prefixEnd_939992 107259490529153669039347 := by
  unfold tailWord_939992
  simp only [CollatzResearch.WordTrace]
  refine ⟨17142162405288498348819115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22856216540384664465092153 17142162405288498348819115)
  ·
    refine ⟨25713243607932747523228673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17142162405288498348819115 25713243607932747523228673)
    ·
      refine ⟨19284932705949560642421505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25713243607932747523228673 19284932705949560642421505)
      ·
        refine ⟨14463699529462170481816129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19284932705949560642421505 14463699529462170481816129)
        ·
          refine ⟨10847774647096627861362097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14463699529462170481816129 10847774647096627861362097)
          ·
            refine ⟨8135830985322470896021573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10847774647096627861362097 8135830985322470896021573)
            ·
              refine ⟨1525468309747963293004045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8135830985322470896021573 1525468309747963293004045)
              ·
                refine ⟨572050616155486234876517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525468309747963293004045 572050616155486234876517)
                ·
                  refine ⟨107259490529153669039347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572050616155486234876517 107259490529153669039347)
                  ·
                    rfl

theorem cell22_939992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_939992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_939992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_939992 prefixEnd_939992 := by exact prefixLift 939992
  have htrace : WordTrace (prefixWord ++ tailWord_939992) baseStart_939992 baseEnd_939992 := by
    simpa [prefixWord, tailWord_939992, baseEnd_939992] using wordTrace_append hprefix tailTrace_939992
  have hstable : (prefixWord ++ tailWord_939992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939992).length < 2 ^ (prefixWord ++ tailWord_939992).sum := by decide
  have hdescent : baseEnd_939992 < baseStart_939992 := by decide
  rcases family_descends (prefixWord ++ tailWord_939992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940037 : List Nat := [1, 3, 1, 1, 2, 6, 2, 6]
def baseStart_940037 : Nat := 118140960795 + 940037 * 2 ^ 59
def prefixEnd_940037 : Nat := 4983230072969 + 3 ^ 40 * 940037 * 2
def baseEnd_940037 : Nat := 35754875111899543304767

theorem tailTrace_940037 : CollatzResearch.WordTrace tailWord_940037 prefixEnd_940037 35754875111899543304767 := by
  unfold tailWord_940037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34285966095413969383026365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22857310730275979588684243 34285966095413969383026365)
  ·
    refine ⟨12857237285780238518634887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34285966095413969383026365 12857237285780238518634887)
    ·
      refine ⟨19285855928670357777952331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12857237285780238518634887 19285855928670357777952331)
      ·
        refine ⟨28928783893005536666928497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19285855928670357777952331 28928783893005536666928497)
        ·
          refine ⟨21696587919754152500196373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28928783893005536666928497 21696587919754152500196373)
          ·
            refine ⟨1017027558738475898446705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21696587919754152500196373 1017027558738475898446705)
            ·
              refine ⟨762770669053856923835029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017027558738475898446705 762770669053856923835029)
              ·
                refine ⟨35754875111899543304767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 762770669053856923835029 35754875111899543304767)
                ·
                  rfl

theorem cell22_940037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 6].length) (baseStart_940037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940037 prefixEnd_940037 := by exact prefixLift 940037
  have htrace : WordTrace (prefixWord ++ tailWord_940037) baseStart_940037 baseEnd_940037 := by
    simpa [prefixWord, tailWord_940037, baseEnd_940037] using wordTrace_append hprefix tailTrace_940037
  have hstable : (prefixWord ++ tailWord_940037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940037).length < 2 ^ (prefixWord ++ tailWord_940037).sum := by decide
  have hdescent : baseEnd_940037 < baseStart_940037 := by decide
  rcases family_descends (prefixWord ++ tailWord_940037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940069 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_940069 : Nat := 118140960795 + 940069 * 2 ^ 59
def prefixEnd_940069 : Nat := 4983230072969 + 3 ^ 40 * 940069 * 2
def baseEnd_940069 : Nat := 321804830261058472942805

theorem tailTrace_940069 : CollatzResearch.WordTrace tailWord_940069 prefixEnd_940069 321804830261058472942805 := by
  unfold tailWord_940069
  simp only [CollatzResearch.WordTrace]
  refine ⟨34287133231298038848191261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22858088820865359232127507 34287133231298038848191261)
  ·
    refine ⟨12857674961736764568071723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34287133231298038848191261 12857674961736764568071723)
    ·
      refine ⟨19286512442605146852107585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12857674961736764568071723 19286512442605146852107585)
      ·
        refine ⟨14464884331953860139080689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19286512442605146852107585 14464884331953860139080689)
        ·
          refine ⟨10848663248965395104310517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14464884331953860139080689 10848663248965395104310517)
          ·
            refine ⟨1017062179590505791029111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10848663248965395104310517 1017062179590505791029111)
            ·
              refine ⟨1525593269385758686543667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017062179590505791029111 1525593269385758686543667)
              ·
                refine ⟨2288389904078638029815501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525593269385758686543667 2288389904078638029815501)
                ·
                  refine ⟨858146214029489261180813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2288389904078638029815501 858146214029489261180813)
                  ·
                    refine ⟨321804830261058472942805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858146214029489261180813 321804830261058472942805)
                    ·
                      rfl

theorem cell22_940069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_940069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940069 prefixEnd_940069 := by exact prefixLift 940069
  have htrace : WordTrace (prefixWord ++ tailWord_940069) baseStart_940069 baseEnd_940069 := by
    simpa [prefixWord, tailWord_940069, baseEnd_940069] using wordTrace_append hprefix tailTrace_940069
  have hstable : (prefixWord ++ tailWord_940069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940069).length < 2 ^ (prefixWord ++ tailWord_940069).sum := by decide
  have hdescent : baseEnd_940069 < baseStart_940069 := by decide
  rcases family_descends (prefixWord ++ tailWord_940069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940082 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_940082 : Nat := 118140960795 + 940082 * 2 ^ 59
def prefixEnd_940082 : Nat := 4983230072969 + 3 ^ 40 * 940082 * 2
def baseEnd_940082 : Nat := 107269760142243590789255

theorem tailTrace_940082 : CollatzResearch.WordTrace tailWord_940082 prefixEnd_940082 107269760142243590789255 := by
  unfold tailWord_940082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571901845062735517103625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22858404920167294712276333 8571901845062735517103625)
  ·
    refine ⟨6428926383797051637827719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8571901845062735517103625 6428926383797051637827719)
    ·
      refine ⟨9643389575695577456741579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428926383797051637827719 9643389575695577456741579)
      ·
        refine ⟨14465084363543366185112369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9643389575695577456741579 14465084363543366185112369)
        ·
          refine ⟨10848813272657524638834277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14465084363543366185112369 10848813272657524638834277)
          ·
            refine ⟨2034152488623285869781427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10848813272657524638834277 2034152488623285869781427)
            ·
              refine ⟨3051228732934928804672141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034152488623285869781427 3051228732934928804672141)
              ·
                refine ⟨1144210774850598301752053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051228732934928804672141 1144210774850598301752053)
                ·
                  refine ⟨107269760142243590789255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1144210774850598301752053 107269760142243590789255)
                  ·
                    rfl

theorem cell22_940082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_940082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940082 prefixEnd_940082 := by exact prefixLift 940082
  have htrace : WordTrace (prefixWord ++ tailWord_940082) baseStart_940082 baseEnd_940082 := by
    simpa [prefixWord, tailWord_940082, baseEnd_940082] using wordTrace_append hprefix tailTrace_940082
  have hstable : (prefixWord ++ tailWord_940082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940082).length < 2 ^ (prefixWord ++ tailWord_940082).sum := by decide
  have hdescent : baseEnd_940082 < baseStart_940082 := by decide
  rcases family_descends (prefixWord ++ tailWord_940082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940157 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_940157 : Nat := 118140960795 + 940157 * 2 ^ 59
def prefixEnd_940157 : Nat := 4983230072969 + 3 ^ 40 * 940157 * 2
def baseEnd_940157 : Nat := 321834954459455576742535

theorem tailTrace_940157 : CollatzResearch.WordTrace tailWord_940157 prefixEnd_940157 321834954459455576742535 := by
  unfold tailWord_940157
  simp only [CollatzResearch.WordTrace]
  refine ⟨34290342854979229877394725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22860228569986153251596483 34290342854979229877394725)
  ·
    refine ⟨6429439285308605602011511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34290342854979229877394725 6429439285308605602011511)
    ·
      refine ⟨9644158927962908403017267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429439285308605602011511 9644158927962908403017267)
      ·
        refine ⟨14466238391944362604525901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644158927962908403017267 14466238391944362604525901)
        ·
          refine ⟨5424839396979135976697213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14466238391944362604525901 5424839396979135976697213)
          ·
            refine ⟨2034314773867175991261455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5424839396979135976697213 2034314773867175991261455)
            ·
              refine ⟨3051472160800763986892183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034314773867175991261455 3051472160800763986892183)
              ·
                refine ⟨4577208241201145980338275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051472160800763986892183 4577208241201145980338275)
                ·
                  refine ⟨6865812361801718970507413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577208241201145980338275 6865812361801718970507413)
                  ·
                    refine ⟨321834954459455576742535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6865812361801718970507413 321834954459455576742535)
                    ·
                      rfl

theorem cell22_940157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_940157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940157 prefixEnd_940157 := by exact prefixLift 940157
  have htrace : WordTrace (prefixWord ++ tailWord_940157) baseStart_940157 baseEnd_940157 := by
    simpa [prefixWord, tailWord_940157, baseEnd_940157] using wordTrace_append hprefix tailTrace_940157
  have hstable : (prefixWord ++ tailWord_940157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940157).length < 2 ^ (prefixWord ++ tailWord_940157).sum := by decide
  have hdescent : baseEnd_940157 < baseStart_940157 := by decide
  rcases family_descends (prefixWord ++ tailWord_940157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940161 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 4]
def baseStart_940161 : Nat := 118140960795 + 940161 * 2 ^ 59
def prefixEnd_940161 : Nat := 4983230072969 + 3 ^ 40 * 940161 * 2
def baseEnd_940161 : Nat := 107278774580400299880841

theorem tailTrace_940161 : CollatzResearch.WordTrace tailWord_940161 prefixEnd_940161 107278774580400299880841 := by
  unfold tailWord_940161
  simp only [CollatzResearch.WordTrace]
  refine ⟨34290488746964738560540337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22860325831309825707026891 34290488746964738560540337)
  ·
    refine ⟨25717866560223553920405253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34290488746964738560540337 25717866560223553920405253)
    ·
      refine ⟨4822099980041916360075985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25717866560223553920405253 4822099980041916360075985)
      ·
        refine ⟨3616574985031437270056989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4822099980041916360075985 3616574985031437270056989)
        ·
          refine ⟨1356215619386788976271371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3616574985031437270056989 1356215619386788976271371)
          ·
            refine ⟨2034323429080183464407057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356215619386788976271371 2034323429080183464407057)
            ·
              refine ⟨1525742571810137598305293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034323429080183464407057 1525742571810137598305293)
              ·
                refine ⟨572153464428801599364485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525742571810137598305293 572153464428801599364485)
                ·
                  refine ⟨107278774580400299880841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572153464428801599364485 107278774580400299880841)
                  ·
                    rfl

theorem cell22_940161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_940161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940161 prefixEnd_940161 := by exact prefixLift 940161
  have htrace : WordTrace (prefixWord ++ tailWord_940161) baseStart_940161 baseEnd_940161 := by
    simpa [prefixWord, tailWord_940161, baseEnd_940161] using wordTrace_append hprefix tailTrace_940161
  have hstable : (prefixWord ++ tailWord_940161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940161).length < 2 ^ (prefixWord ++ tailWord_940161).sum := by decide
  have hdescent : baseEnd_940161 < baseStart_940161 := by decide
  rcases family_descends (prefixWord ++ tailWord_940161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940185 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_940185 : Nat := 118140960795 + 940185 * 2 ^ 59
def prefixEnd_940185 : Nat := 4983230072969 + 3 ^ 40 * 940185 * 2
def baseEnd_940185 : Nat := 321844539431672837042449

theorem tailTrace_940185 : CollatzResearch.WordTrace tailWord_940185 prefixEnd_940185 321844539431672837042449 := by
  unfold tailWord_940185
  simp only [CollatzResearch.WordTrace]
  refine ⟨34291364098877790659414009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22860909399251860439609339 34291364098877790659414009)
  ·
    refine ⟨25718523074158342994560507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34291364098877790659414009 25718523074158342994560507)
    ·
      refine ⟨38577784611237514491840761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25718523074158342994560507 38577784611237514491840761)
      ·
        refine ⟨28933338458428135868880571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38577784611237514491840761 28933338458428135868880571)
        ·
          refine ⟨43400007687642203803320857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28933338458428135868880571 43400007687642203803320857)
          ·
            refine ⟨32550005765731652852490643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43400007687642203803320857 32550005765731652852490643)
            ·
              refine ⟨48825008648597479278735965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32550005765731652852490643 48825008648597479278735965)
              ·
                refine ⟨18309378243224054729525987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48825008648597479278735965 18309378243224054729525987)
                ·
                  refine ⟨27464067364836082094288981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18309378243224054729525987 27464067364836082094288981)
                  ·
                    refine ⟨321844539431672837042449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27464067364836082094288981 321844539431672837042449)
                    ·
                      rfl

theorem cell22_940185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_940185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940185 prefixEnd_940185 := by exact prefixLift 940185
  have htrace : WordTrace (prefixWord ++ tailWord_940185) baseStart_940185 baseEnd_940185 := by
    simpa [prefixWord, tailWord_940185, baseEnd_940185] using wordTrace_append hprefix tailTrace_940185
  have hstable : (prefixWord ++ tailWord_940185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940185).length < 2 ^ (prefixWord ++ tailWord_940185).sum := by decide
  have hdescent : baseEnd_940185 < baseStart_940185 := by decide
  rcases family_descends (prefixWord ++ tailWord_940185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940206 : List Nat := [4, 1, 4, 2, 1, 1, 1, 8]
def baseStart_940206 : Nat := 118140960795 + 940206 * 2 ^ 59
def prefixEnd_940206 : Nat := 4983230072969 + 3 ^ 40 * 940206 * 2
def baseEnd_940206 : Nat := 35761303128981753585265

theorem tailTrace_940206 : CollatzResearch.WordTrace tailWord_940206 prefixEnd_940206 35761303128981753585265 := by
  unfold tailWord_940206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286516253975213905741059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22861420021201140830618981 4286516253975213905741059)
  ·
    refine ⟨6429774380962820858611589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4286516253975213905741059 6429774380962820858611589)
    ·
      refine ⟨1205582696430528910989673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6429774380962820858611589 1205582696430528910989673)
      ·
        refine ⟨904187022322896683242255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1205582696430528910989673 904187022322896683242255)
        ·
          refine ⟨1356280533484345024863383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904187022322896683242255 1356280533484345024863383)
          ·
            refine ⟨2034420800226517537295075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356280533484345024863383 2034420800226517537295075)
            ·
              refine ⟨3051631200339776305942613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034420800226517537295075 3051631200339776305942613)
              ·
                refine ⟨35761303128981753585265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3051631200339776305942613 35761303128981753585265)
                ·
                  rfl

theorem cell22_940206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_940206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940206 prefixEnd_940206 := by exact prefixLift 940206
  have htrace : WordTrace (prefixWord ++ tailWord_940206) baseStart_940206 baseEnd_940206 := by
    simpa [prefixWord, tailWord_940206, baseEnd_940206] using wordTrace_append hprefix tailTrace_940206
  have hstable : (prefixWord ++ tailWord_940206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940206).length < 2 ^ (prefixWord ++ tailWord_940206).sum := by decide
  have hdescent : baseEnd_940206 < baseStart_940206 := by decide
  rcases family_descends (prefixWord ++ tailWord_940206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940212 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 4]
def baseStart_940212 : Nat := 118140960795 + 940212 * 2 ^ 59
def prefixEnd_940212 : Nat := 4983230072969 + 3 ^ 40 * 940212 * 2
def baseEnd_940212 : Nat := 107284594027817922205789

theorem tailTrace_940212 : CollatzResearch.WordTrace tailWord_940212 prefixEnd_940212 107284594027817922205789 := by
  unfold tailWord_940212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146174434889987135323445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22861565913186649513764593 17146174434889987135323445)
  ·
    refine ⟨1607453853270936293936573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17146174434889987135323445 1607453853270936293936573)
    ·
      refine ⟨602795194976601110226215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1607453853270936293936573 602795194976601110226215)
      ·
        refine ⟨904192792464901665339323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602795194976601110226215 904192792464901665339323)
        ·
          refine ⟨1356289188697352498008985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904192792464901665339323 1356289188697352498008985)
          ·
            refine ⟨1017216891523014373506739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356289188697352498008985 1017216891523014373506739)
            ·
              refine ⟨1525825337284521560260109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017216891523014373506739 1525825337284521560260109)
              ·
                refine ⟨572184501481695585097541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525825337284521560260109 572184501481695585097541)
                ·
                  refine ⟨107284594027817922205789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572184501481695585097541 107284594027817922205789)
                  ·
                    rfl

theorem cell22_940212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_940212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940212 prefixEnd_940212 := by exact prefixLift 940212
  have htrace : WordTrace (prefixWord ++ tailWord_940212) baseStart_940212 baseEnd_940212 := by
    simpa [prefixWord, tailWord_940212, baseEnd_940212] using wordTrace_append hprefix tailTrace_940212
  have hstable : (prefixWord ++ tailWord_940212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940212).length < 2 ^ (prefixWord ++ tailWord_940212).sum := by decide
  have hdescent : baseEnd_940212 < baseStart_940212 := by decide
  rcases family_descends (prefixWord ++ tailWord_940212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940247 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 3, 4]
def baseStart_940247 : Nat := 118140960795 + 940247 * 2 ^ 59
def prefixEnd_940247 : Nat := 4983230072969 + 3 ^ 40 * 940247 * 2
def baseEnd_940247 : Nat := 321865763298725341992259

theorem tailTrace_940247 : CollatzResearch.WordTrace tailWord_940247 prefixEnd_940247 321865763298725341992259 := by
  unfold tailWord_940247
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293625424653175248170995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22862416949768783498780663 34293625424653175248170995)
  ·
    refine ⟨51440438136979762872256493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34293625424653175248170995 51440438136979762872256493)
    ·
      refine ⟨19290164301367411077096185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51440438136979762872256493 19290164301367411077096185)
      ·
        refine ⟨14467623226025558307822139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19290164301367411077096185 14467623226025558307822139)
        ·
          refine ⟨21701434839038337461733209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14467623226025558307822139 21701434839038337461733209)
          ·
            refine ⟨16276076129278753096299907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21701434839038337461733209 16276076129278753096299907)
            ·
              refine ⟨24414114193918129644449861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276076129278753096299907 24414114193918129644449861)
              ·
                refine ⟨4577646411359649308334349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24414114193918129644449861 4577646411359649308334349)
                ·
                  refine ⟨1716617404259868490625381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4577646411359649308334349 1716617404259868490625381)
                  ·
                    refine ⟨321865763298725341992259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1716617404259868490625381 321865763298725341992259)
                    ·
                      rfl

theorem cell22_940247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_940247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940247 prefixEnd_940247 := by exact prefixLift 940247
  have htrace : WordTrace (prefixWord ++ tailWord_940247) baseStart_940247 baseEnd_940247 := by
    simpa [prefixWord, tailWord_940247, baseEnd_940247] using wordTrace_append hprefix tailTrace_940247
  have hstable : (prefixWord ++ tailWord_940247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940247).length < 2 ^ (prefixWord ++ tailWord_940247).sum := by decide
  have hdescent : baseEnd_940247 < baseStart_940247 := by decide
  rcases family_descends (prefixWord ++ tailWord_940247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940264 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_940264 : Nat := 118140960795 + 940264 * 2 ^ 59
def prefixEnd_940264 : Nat := 4983230072969 + 3 ^ 40 * 940264 * 2
def baseEnd_940264 : Nat := 321871582746142964317207

theorem tailTrace_940264 : CollatzResearch.WordTrace tailWord_940264 prefixEnd_940264 321871582746142964317207 := by
  unfold tailWord_940264
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147122732795793575769923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22862830310394391434359897 17147122732795793575769923)
  ·
    refine ⟨25720684099193690363654885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17147122732795793575769923 25720684099193690363654885)
    ·
      refine ⟨4822628268598816943185291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25720684099193690363654885 4822628268598816943185291)
      ·
        refine ⟨7233942402898225414777937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822628268598816943185291 7233942402898225414777937)
        ·
          refine ⟨5425456802173669061083453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7233942402898225414777937 5425456802173669061083453)
          ·
            refine ⟨2034546300815125897906295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5425456802173669061083453 2034546300815125897906295)
            ·
              refine ⟨3051819451222688846859443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034546300815125897906295 3051819451222688846859443)
              ·
                refine ⟨4577729176834033270289165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051819451222688846859443 4577729176834033270289165)
                ·
                  refine ⟨1716648441312762476358437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4577729176834033270289165 1716648441312762476358437)
                  ·
                    refine ⟨321871582746142964317207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1716648441312762476358437 321871582746142964317207)
                    ·
                      rfl

theorem cell22_940264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_940264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940264 prefixEnd_940264 := by exact prefixLift 940264
  have htrace : WordTrace (prefixWord ++ tailWord_940264) baseStart_940264 baseEnd_940264 := by
    simpa [prefixWord, tailWord_940264, baseEnd_940264] using wordTrace_append hprefix tailTrace_940264
  have hstable : (prefixWord ++ tailWord_940264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940264).length < 2 ^ (prefixWord ++ tailWord_940264).sum := by decide
  have hdescent : baseEnd_940264 < baseStart_940264 := by decide
  rcases family_descends (prefixWord ++ tailWord_940264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940296 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 4]
def baseStart_940296 : Nat := 118140960795 + 940296 * 2 ^ 59
def prefixEnd_940296 : Nat := 4983230072969 + 3 ^ 40 * 940296 * 2
def baseEnd_940296 : Nat := 107294179000035182505703

theorem tailTrace_940296 : CollatzResearch.WordTrace tailWord_940296 prefixEnd_940296 107294179000035182505703 := by
  unfold tailWord_940296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147706300737828308352371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22863608400983771077803161 17147706300737828308352371)
  ·
    refine ⟨25721559451106742462528557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17147706300737828308352371 25721559451106742462528557)
    ·
      refine ⟨9645584794165028423448209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25721559451106742462528557 9645584794165028423448209)
      ·
        refine ⟨7234188595623771317586157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9645584794165028423448209 7234188595623771317586157)
        ·
          refine ⟨2712820723358914244094809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7234188595623771317586157 2712820723358914244094809)
          ·
            refine ⟨2034615542519185683071107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712820723358914244094809 2034615542519185683071107)
            ·
              refine ⟨3051923313778778524606661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034615542519185683071107 3051923313778778524606661)
              ·
                refine ⟨572235621333520973363749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3051923313778778524606661 572235621333520973363749)
                ·
                  refine ⟨107294179000035182505703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572235621333520973363749 107294179000035182505703)
                  ·
                    rfl

theorem cell22_940296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_940296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940296 prefixEnd_940296 := by exact prefixLift 940296
  have htrace : WordTrace (prefixWord ++ tailWord_940296) baseStart_940296 baseEnd_940296 := by
    simpa [prefixWord, tailWord_940296, baseEnd_940296] using wordTrace_append hprefix tailTrace_940296
  have hstable : (prefixWord ++ tailWord_940296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940296).length < 2 ^ (prefixWord ++ tailWord_940296).sum := by decide
  have hdescent : baseEnd_940296 < baseStart_940296 := by decide
  rcases family_descends (prefixWord ++ tailWord_940296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940311 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 2, 3]
def baseStart_940311 : Nat := 118140960795 + 940311 * 2 ^ 59
def prefixEnd_940311 : Nat := 4983230072969 + 3 ^ 40 * 940311 * 2
def baseEnd_940311 : Nat := 321887671806650508392063

theorem tailTrace_940311 : CollatzResearch.WordTrace tailWord_940311 prefixEnd_940311 321887671806650508392063 := by
  unfold tailWord_940311
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295959696421314178500787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22863973130947542785667191 34295959696421314178500787)
  ·
    refine ⟨51443939544631971267751181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34295959696421314178500787 51443939544631971267751181)
    ·
      refine ⟨19291477329236989225406693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51443939544631971267751181 19291477329236989225406693)
      ·
        refine ⟨3617151999231935479763755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19291477329236989225406693 3617151999231935479763755)
        ·
          refine ⟨5425727998847903219645633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617151999231935479763755 5425727998847903219645633)
          ·
            refine ⟨4069295999135927414734225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425727998847903219645633 4069295999135927414734225)
            ·
              refine ⟨3051971999351945561050669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4069295999135927414734225 3051971999351945561050669)
              ·
                refine ⟨1144489499756979585394001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3051971999351945561050669 1144489499756979585394001)
                ·
                  refine ⟨858367124817734689045501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144489499756979585394001 858367124817734689045501)
                  ·
                    refine ⟨321887671806650508392063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858367124817734689045501 321887671806650508392063)
                    ·
                      rfl

theorem cell22_940311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_940311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940311 prefixEnd_940311 := by exact prefixLift 940311
  have htrace : WordTrace (prefixWord ++ tailWord_940311) baseStart_940311 baseEnd_940311 := by
    simpa [prefixWord, tailWord_940311, baseEnd_940311] using wordTrace_append hprefix tailTrace_940311
  have hstable : (prefixWord ++ tailWord_940311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940311).length < 2 ^ (prefixWord ++ tailWord_940311).sum := by decide
  have hdescent : baseEnd_940311 < baseStart_940311 := by decide
  rcases family_descends (prefixWord ++ tailWord_940311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940339 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 5, 3]
def baseStart_940339 : Nat := 118140960795 + 940339 * 2 ^ 59
def prefixEnd_940339 : Nat := 4983230072969 + 3 ^ 40 * 940339 * 2
def baseEnd_940339 : Nat := 321897256778867768691977

theorem tailTrace_940339 : CollatzResearch.WordTrace tailWord_940339 prefixEnd_940339 321897256778867768691977 := by
  unfold tailWord_940339
  simp only [CollatzResearch.WordTrace]
  refine ⟨34296980940319874960520071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22864653960213249973680047 34296980940319874960520071)
  ·
    refine ⟨51445471410479812440780107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34296980940319874960520071 51445471410479812440780107)
    ·
      refine ⟨77168207115719718661170161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51445471410479812440780107 77168207115719718661170161)
      ·
        refine ⟨57876155336789788995877621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77168207115719718661170161 57876155336789788995877621)
        ·
          refine ⟨5425889562824042718363527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57876155336789788995877621 5425889562824042718363527)
          ·
            refine ⟨8138834344236064077545291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425889562824042718363527 8138834344236064077545291)
            ·
              refine ⟨12208251516354096116317937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138834344236064077545291 12208251516354096116317937)
              ·
                refine ⟨9156188637265572087238453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12208251516354096116317937 9156188637265572087238453)
                ·
                  refine ⟨858392684743647383178605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9156188637265572087238453 858392684743647383178605)
                  ·
                    refine ⟨321897256778867768691977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858392684743647383178605 321897256778867768691977)
                    ·
                      rfl

theorem cell22_940339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 3].length) (baseStart_940339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940339 prefixEnd_940339 := by exact prefixLift 940339
  have htrace : WordTrace (prefixWord ++ tailWord_940339) baseStart_940339 baseEnd_940339 := by
    simpa [prefixWord, tailWord_940339, baseEnd_940339] using wordTrace_append hprefix tailTrace_940339
  have hstable : (prefixWord ++ tailWord_940339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940339).length < 2 ^ (prefixWord ++ tailWord_940339).sum := by decide
  have hdescent : baseEnd_940339 < baseStart_940339 := by decide
  rcases family_descends (prefixWord ++ tailWord_940339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940367 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_940367 : Nat := 118140960795 + 940367 * 2 ^ 59
def prefixEnd_940367 : Nat := 4983230072969 + 3 ^ 40 * 940367 * 2
def baseEnd_940367 : Nat := 321906841751085028991891

theorem tailTrace_940367 : CollatzResearch.WordTrace tailWord_940367 prefixEnd_940367 321906841751085028991891 := by
  unfold tailWord_940367
  simp only [CollatzResearch.WordTrace]
  refine ⟨34298002184218435742539355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22865334789478957161692903 34298002184218435742539355)
  ·
    refine ⟨51447003276327653613809033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34298002184218435742539355 51447003276327653613809033)
    ·
      refine ⟨38585252457245740210356775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51447003276327653613809033 38585252457245740210356775)
      ·
        refine ⟨57877878685868610315535163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38585252457245740210356775 57877878685868610315535163)
        ·
          refine ⟨86816818028802915473302745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57877878685868610315535163 86816818028802915473302745)
          ·
            refine ⟨65112613521602186604977059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86816818028802915473302745 65112613521602186604977059)
            ·
              refine ⟨97668920282403279907465589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65112613521602186604977059 97668920282403279907465589)
              ·
                refine ⟨9156461276475307491324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97668920282403279907465589 9156461276475307491324899)
                ·
                  refine ⟨13734691914712961236987349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9156461276475307491324899 13734691914712961236987349)
                  ·
                    refine ⟨321906841751085028991891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13734691914712961236987349 321906841751085028991891)
                    ·
                      rfl

theorem cell22_940367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_940367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940367 prefixEnd_940367 := by exact prefixLift 940367
  have htrace : WordTrace (prefixWord ++ tailWord_940367) baseStart_940367 baseEnd_940367 := by
    simpa [prefixWord, tailWord_940367, baseEnd_940367] using wordTrace_append hprefix tailTrace_940367
  have hstable : (prefixWord ++ tailWord_940367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940367).length < 2 ^ (prefixWord ++ tailWord_940367).sum := by decide
  have hdescent : baseEnd_940367 < baseStart_940367 := by decide
  rcases family_descends (prefixWord ++ tailWord_940367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940458 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_940458 : Nat := 118140960795 + 940458 * 2 ^ 59
def prefixEnd_940458 : Nat := 4983230072969 + 3 ^ 40 * 940458 * 2
def baseEnd_940458 : Nat := 321937992910791124966613

theorem tailTrace_940458 : CollatzResearch.WordTrace tailWord_940458 prefixEnd_940458 321937992910791124966613 := by
  unfold tailWord_940458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8575330306722189571025507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22867547484592505522734685 8575330306722189571025507)
  ·
    refine ⟨12862995460083284356538261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8575330306722189571025507 12862995460083284356538261)
    ·
      refine ⟨602952912191403954212731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12862995460083284356538261 602952912191403954212731)
      ·
        refine ⟨904429368287105931319097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602952912191403954212731 904429368287105931319097)
        ·
          refine ⟨678322026215329448489323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904429368287105931319097 678322026215329448489323)
          ·
            refine ⟨1017483039322994172733985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678322026215329448489323 1017483039322994172733985)
            ·
              refine ⟨763112279492245629550489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017483039322994172733985 763112279492245629550489)
              ·
                refine ⟨572334209619184222162867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763112279492245629550489 572334209619184222162867)
                ·
                  refine ⟨858501314428776333244301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572334209619184222162867 858501314428776333244301)
                  ·
                    refine ⟨321937992910791124966613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858501314428776333244301 321937992910791124966613)
                    ·
                      rfl

theorem cell22_940458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_940458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940458 prefixEnd_940458 := by exact prefixLift 940458
  have htrace : WordTrace (prefixWord ++ tailWord_940458) baseStart_940458 baseEnd_940458 := by
    simpa [prefixWord, tailWord_940458, baseEnd_940458] using wordTrace_append hprefix tailTrace_940458
  have hstable : (prefixWord ++ tailWord_940458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940458).length < 2 ^ (prefixWord ++ tailWord_940458).sum := by decide
  have hdescent : baseEnd_940458 < baseStart_940458 := by decide
  rcases family_descends (prefixWord ++ tailWord_940458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940465 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 4]
def baseStart_940465 : Nat := 118140960795 + 940465 * 2 ^ 59
def prefixEnd_940465 : Nat := 4983230072969 + 3 ^ 40 * 940465 * 2
def baseEnd_940465 : Nat := 107313463051281813347197

theorem tailTrace_940465 : CollatzResearch.WordTrace tailWord_940465 prefixEnd_940465 107313463051281813347197 := by
  unfold tailWord_940465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301576537863398479606849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22867717691908932319737899 34301576537863398479606849)
  ·
    refine ⟨25726182403397548859705137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34301576537863398479606849 25726182403397548859705137)
    ·
      refine ⟨19294636802548161644778853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25726182403397548859705137 19294636802548161644778853)
      ·
        refine ⟨3617744400477780308396035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19294636802548161644778853 3617744400477780308396035)
        ·
          refine ⟨5426616600716670462594053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617744400477780308396035 5426616600716670462594053)
          ·
            refine ⟨1017490612634375711736385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5426616600716670462594053 1017490612634375711736385)
            ·
              refine ⟨763117959475781783802289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017490612634375711736385 763117959475781783802289)
              ·
                refine ⟨572338469606836337851717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763117959475781783802289 572338469606836337851717)
                ·
                  refine ⟨107313463051281813347197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572338469606836337851717 107313463051281813347197)
                  ·
                    rfl

theorem cell22_940465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_940465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940465 prefixEnd_940465 := by exact prefixLift 940465
  have htrace : WordTrace (prefixWord ++ tailWord_940465) baseStart_940465 baseEnd_940465 := by
    simpa [prefixWord, tailWord_940465, baseEnd_940465] using wordTrace_append hprefix tailTrace_940465
  have hstable : (prefixWord ++ tailWord_940465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940465).length < 2 ^ (prefixWord ++ tailWord_940465).sum := by decide
  have hdescent : baseEnd_940465 < baseStart_940465 := by decide
  rcases family_descends (prefixWord ++ tailWord_940465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940476 : List Nat := [2, 2, 2, 4, 1, 1, 3, 7]
def baseStart_940476 : Nat := 118140960795 + 940476 * 2 ^ 59
def prefixEnd_940476 : Nat := 4983230072969 + 3 ^ 40 * 940476 * 2
def baseEnd_940476 : Nat := 35771572742071675335173

theorem tailTrace_940476 : CollatzResearch.WordTrace tailWord_940476 prefixEnd_940476 35771572742071675335173 := by
  unfold tailWord_940476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17150988870411773679128641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22867985160549031572171521 17150988870411773679128641)
  ·
    refine ⟨12863241652808830259346481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17150988870411773679128641 12863241652808830259346481)
    ·
      refine ⟨9647431239606622694509861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12863241652808830259346481 9647431239606622694509861)
      ·
        refine ⟨1808893357426241755220599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9647431239606622694509861 1808893357426241755220599)
        ·
          refine ⟨2713340036139362632830899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808893357426241755220599 2713340036139362632830899)
          ·
            refine ⟨4070010054209043949246349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2713340036139362632830899 4070010054209043949246349)
            ·
              refine ⟨1526253770328391480967381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4070010054209043949246349 1526253770328391480967381)
              ·
                refine ⟨35771572742071675335173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1526253770328391480967381 35771572742071675335173)
                ·
                  rfl

theorem cell22_940476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_940476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940476 prefixEnd_940476 := by exact prefixLift 940476
  have htrace : WordTrace (prefixWord ++ tailWord_940476) baseStart_940476 baseEnd_940476 := by
    simpa [prefixWord, tailWord_940476, baseEnd_940476] using wordTrace_append hprefix tailTrace_940476
  have hstable : (prefixWord ++ tailWord_940476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940476).length < 2 ^ (prefixWord ++ tailWord_940476).sum := by decide
  have hdescent : baseEnd_940476 < baseStart_940476 := by decide
  rcases family_descends (prefixWord ++ tailWord_940476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940504 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_940504 : Nat := 118140960795 + 940504 * 2 ^ 59
def prefixEnd_940504 : Nat := 4983230072969 + 3 ^ 40 * 940504 * 2
def baseEnd_940504 : Nat := 107317913216954112772157

theorem tailTrace_940504 : CollatzResearch.WordTrace tailWord_940504 prefixEnd_940504 107317913216954112772157 := by
  unfold tailWord_940504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17151499492361054070138283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22868665989814738760184377 17151499492361054070138283)
  ·
    refine ⟨25727249238541581105207425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17151499492361054070138283 25727249238541581105207425)
    ·
      refine ⟨19295436928906185828905569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25727249238541581105207425 19295436928906185828905569)
      ·
        refine ⟨14471577696679639371679177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19295436928906185828905569 14471577696679639371679177)
        ·
          refine ⟨10853683272509729528759383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14471577696679639371679177 10853683272509729528759383)
          ·
            refine ⟨16280524908764594293139075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10853683272509729528759383 16280524908764594293139075)
            ·
              refine ⟨24420787363146891439708613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16280524908764594293139075 24420787363146891439708613)
              ·
                refine ⟨4578897630590042144945365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24420787363146891439708613 4578897630590042144945365)
                ·
                  refine ⟨107317913216954112772157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4578897630590042144945365 107317913216954112772157)
                  ·
                    rfl

theorem cell22_940504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_940504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940504 prefixEnd_940504 := by exact prefixLift 940504
  have htrace : WordTrace (prefixWord ++ tailWord_940504) baseStart_940504 baseEnd_940504 := by
    simpa [prefixWord, tailWord_940504, baseEnd_940504] using wordTrace_append hprefix tailTrace_940504
  have hstable : (prefixWord ++ tailWord_940504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940504).length < 2 ^ (prefixWord ++ tailWord_940504).sum := by decide
  have hdescent : baseEnd_940504 < baseStart_940504 := by decide
  rcases family_descends (prefixWord ++ tailWord_940504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940514 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_940514 : Nat := 118140960795 + 940514 * 2 ^ 59
def prefixEnd_940514 : Nat := 4983230072969 + 3 ^ 40 * 940514 * 2
def baseEnd_940514 : Nat := 321957162855225645566441

theorem tailTrace_940514 : CollatzResearch.WordTrace tailWord_940514 prefixEnd_940514 321957162855225645566441 := by
  unfold tailWord_940514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8575840928671469962035149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22868909143123919898760397 8575840928671469962035149)
  ·
    refine ⟨3215940348251801235763181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8575840928671469962035149 3215940348251801235763181)
    ·
      refine ⟨1205977630594425463411193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3215940348251801235763181 1205977630594425463411193)
      ·
        refine ⟨904483222945819097558395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1205977630594425463411193 904483222945819097558395)
        ·
          refine ⟨1356724834418728646337593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904483222945819097558395 1356724834418728646337593)
          ·
            refine ⟨1017543625814046484753195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356724834418728646337593 1017543625814046484753195)
            ·
              refine ⟨1526315438721069727129793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017543625814046484753195 1526315438721069727129793)
              ·
                refine ⟨1144736579040802295347345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1526315438721069727129793 1144736579040802295347345)
                ·
                  refine ⟨858552434280601721510509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144736579040802295347345 858552434280601721510509)
                  ·
                    refine ⟨321957162855225645566441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858552434280601721510509 321957162855225645566441)
                    ·
                      rfl

theorem cell22_940514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_940514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940514 prefixEnd_940514 := by exact prefixLift 940514
  have htrace : WordTrace (prefixWord ++ tailWord_940514) baseStart_940514 baseEnd_940514 := by
    simpa [prefixWord, tailWord_940514, baseEnd_940514] using wordTrace_append hprefix tailTrace_940514
  have hstable : (prefixWord ++ tailWord_940514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940514).length < 2 ^ (prefixWord ++ tailWord_940514).sum := by decide
  have hdescent : baseEnd_940514 < baseStart_940514 := by decide
  rcases family_descends (prefixWord ++ tailWord_940514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940525 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_940525 : Nat := 118140960795 + 940525 * 2 ^ 59
def prefixEnd_940525 : Nat := 4983230072969 + 3 ^ 40 * 940525 * 2
def baseEnd_940525 : Nat := 321960928380025283541407

theorem tailTrace_940525 : CollatzResearch.WordTrace tailWord_940525 prefixEnd_940525 321960928380025283541407 := by
  unfold tailWord_940525
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303764917646028726791029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22869176611764019151194019 34303764917646028726791029)
  ·
    refine ⟨3215977961029315193136659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34303764917646028726791029 3215977961029315193136659)
    ·
      refine ⟨4823966941543972789704989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215977961029315193136659 4823966941543972789704989)
      ·
        refine ⟨1808987603078989796139371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4823966941543972789704989 1808987603078989796139371)
        ·
          refine ⟨2713481404618484694209057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808987603078989796139371 2713481404618484694209057)
          ·
            refine ⟨2035111053463863520656793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2713481404618484694209057 2035111053463863520656793)
            ·
              refine ⟨1526333290097897640492595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035111053463863520656793 1526333290097897640492595)
              ·
                refine ⟨2289499935146846460738893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526333290097897640492595 2289499935146846460738893)
                ·
                  refine ⟨858562475680067422777085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2289499935146846460738893 858562475680067422777085)
                  ·
                    refine ⟨321960928380025283541407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858562475680067422777085 321960928380025283541407)
                    ·
                      rfl

theorem cell22_940525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_940525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940525 prefixEnd_940525 := by exact prefixLift 940525
  have htrace : WordTrace (prefixWord ++ tailWord_940525) baseStart_940525 baseEnd_940525 := by
    simpa [prefixWord, tailWord_940525, baseEnd_940525] using wordTrace_append hprefix tailTrace_940525
  have hstable : (prefixWord ++ tailWord_940525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940525).length < 2 ^ (prefixWord ++ tailWord_940525).sum := by decide
  have hdescent : baseEnd_940525 < baseStart_940525 := by decide
  rcases family_descends (prefixWord ++ tailWord_940525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940568 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_940568 : Nat := 118140960795 + 940568 * 2 ^ 59
def prefixEnd_940568 : Nat := 4983230072969 + 3 ^ 40 * 940568 * 2
def baseEnd_940568 : Nat := 321975648158787504716275

theorem tailTrace_940568 : CollatzResearch.WordTrace tailWord_940568 prefixEnd_940568 321975648158787504716275 := by
  unfold tailWord_940568
  simp only [CollatzResearch.WordTrace]
  refine ⟨17152666628245123535303179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22870222170993498047070905 17152666628245123535303179)
  ·
    refine ⟨25728999942367685302954769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17152666628245123535303179 25728999942367685302954769)
    ·
      refine ⟨19296749956775763977216077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25728999942367685302954769 19296749956775763977216077)
      ·
        refine ⟨7236281233790911491456029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19296749956775763977216077 7236281233790911491456029)
        ·
          refine ⟨2713605462671591809296011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7236281233790911491456029 2713605462671591809296011)
          ·
            refine ⟨4070408194007387713944017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2713605462671591809296011 4070408194007387713944017)
            ·
              refine ⟨3052806145505540785458013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4070408194007387713944017 3052806145505540785458013)
              ·
                refine ⟨1144802304564577794546755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3052806145505540785458013 1144802304564577794546755)
                ·
                  refine ⟨1717203456846866691820133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144802304564577794546755 1717203456846866691820133)
                  ·
                    refine ⟨321975648158787504716275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717203456846866691820133 321975648158787504716275)
                    ·
                      rfl

theorem cell22_940568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_940568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940568 prefixEnd_940568 := by exact prefixLift 940568
  have htrace : WordTrace (prefixWord ++ tailWord_940568) baseStart_940568 baseEnd_940568 := by
    simpa [prefixWord, tailWord_940568, baseEnd_940568] using wordTrace_append hprefix tailTrace_940568
  have hstable : (prefixWord ++ tailWord_940568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940568).length < 2 ^ (prefixWord ++ tailWord_940568).sum := by decide
  have hdescent : baseEnd_940568 < baseStart_940568 := by decide
  rcases family_descends (prefixWord ++ tailWord_940568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940613 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_940613 : Nat := 118140960795 + 940613 * 2 ^ 59
def prefixEnd_940613 : Nat := 4983230072969 + 3 ^ 40 * 940613 * 2
def baseEnd_940613 : Nat := 321991052578422387341137

theorem tailTrace_940613 : CollatzResearch.WordTrace tailWord_940613 prefixEnd_940613 321991052578422387341137 := by
  unfold tailWord_940613
  simp only [CollatzResearch.WordTrace]
  refine ⟨34306974541327219755994493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22871316360884813170662995 34306974541327219755994493)
  ·
    refine ⟨12865115452997707408497935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34306974541327219755994493 12865115452997707408497935)
    ·
      refine ⟨19297673179496561112746903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12865115452997707408497935 19297673179496561112746903)
      ·
        refine ⟨28946509769244841669120355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19297673179496561112746903 28946509769244841669120355)
        ·
          refine ⟨43419764653867262503680533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28946509769244841669120355 43419764653867262503680533)
          ·
            refine ⟨2035301468150027929860025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43419764653867262503680533 2035301468150027929860025)
            ·
              refine ⟨1526476101112520947395019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035301468150027929860025 1526476101112520947395019)
              ·
                refine ⟨2289714151668781421092529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526476101112520947395019 2289714151668781421092529)
                ·
                  refine ⟨1717285613751586065819397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2289714151668781421092529 1717285613751586065819397)
                  ·
                    refine ⟨321991052578422387341137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717285613751586065819397 321991052578422387341137)
                    ·
                      rfl

theorem cell22_940613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_940613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940613 prefixEnd_940613 := by exact prefixLift 940613
  have htrace : WordTrace (prefixWord ++ tailWord_940613) baseStart_940613 baseEnd_940613 := by
    simpa [prefixWord, tailWord_940613, baseEnd_940613] using wordTrace_append hprefix tailTrace_940613
  have hstable : (prefixWord ++ tailWord_940613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940613).length < 2 ^ (prefixWord ++ tailWord_940613).sum := by decide
  have hdescent : baseEnd_940613 < baseStart_940613 := by decide
  rcases family_descends (prefixWord ++ tailWord_940613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940641 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_940641 : Nat := 118140960795 + 940641 * 2 ^ 59
def prefixEnd_940641 : Nat := 4983230072969 + 3 ^ 40 * 940641 * 2
def baseEnd_940641 : Nat := 322000637550639647641051

theorem tailTrace_940641 : CollatzResearch.WordTrace tailWord_940641 prefixEnd_940641 322000637550639647641051 := by
  unfold tailWord_940641
  simp only [CollatzResearch.WordTrace]
  refine ⟨34307995785225780538013777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22871997190150520358675851 34307995785225780538013777)
  ·
    refine ⟨25730996838919335403510333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34307995785225780538013777 25730996838919335403510333)
    ·
      refine ⟨9649123814594750776316375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25730996838919335403510333 9649123814594750776316375)
      ·
        refine ⟨14473685721892126164474563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9649123814594750776316375 14473685721892126164474563)
        ·
          refine ⟨21710528582838189246711845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14473685721892126164474563 21710528582838189246711845)
          ·
            refine ⟨4070724109282160483758471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21710528582838189246711845 4070724109282160483758471)
            ·
              refine ⟨6106086163923240725637707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070724109282160483758471 6106086163923240725637707)
              ·
                refine ⟨9159129245884861088456561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106086163923240725637707 9159129245884861088456561)
                ·
                  refine ⟨6869346934413645816342421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9159129245884861088456561 6869346934413645816342421)
                  ·
                    refine ⟨322000637550639647641051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6869346934413645816342421 322000637550639647641051)
                    ·
                      rfl

theorem cell22_940641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_940641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940641 prefixEnd_940641 := by exact prefixLift 940641
  have htrace : WordTrace (prefixWord ++ tailWord_940641) baseStart_940641 baseEnd_940641 := by
    simpa [prefixWord, tailWord_940641, baseEnd_940641] using wordTrace_append hprefix tailTrace_940641
  have hstable : (prefixWord ++ tailWord_940641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940641).length < 2 ^ (prefixWord ++ tailWord_940641).sum := by decide
  have hdescent : baseEnd_940641 < baseStart_940641 := by decide
  rcases family_descends (prefixWord ++ tailWord_940641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940643 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 3, 3]
def baseStart_940643 : Nat := 118140960795 + 940643 * 2 ^ 59
def prefixEnd_940643 : Nat := 4983230072969 + 3 ^ 40 * 940643 * 2
def baseEnd_940643 : Nat := 322001322191512309091045

theorem tailTrace_940643 : CollatzResearch.WordTrace tailWord_940643 prefixEnd_940643 322001322191512309091045 := by
  unfold tailWord_940643
  simp only [CollatzResearch.WordTrace]
  refine ⟨34308068731218534879586583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22872045820812356586391055 34308068731218534879586583)
  ·
    refine ⟨51462103096827802319379875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34308068731218534879586583 51462103096827802319379875)
    ·
      refine ⟨77193154645241703479069813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51462103096827802319379875 77193154645241703479069813)
      ·
        refine ⟨7236858247991409701162795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77193154645241703479069813 7236858247991409701162795)
        ·
          refine ⟨10855287371987114551744193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236858247991409701162795 10855287371987114551744193)
          ·
            refine ⟨8141465528990335913808145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10855287371987114551744193 8141465528990335913808145)
            ·
              refine ⟨6106099146742751935356109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8141465528990335913808145 6106099146742751935356109)
              ·
                refine ⟨2289787180028531975758541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6106099146742751935356109 2289787180028531975758541)
                ·
                  refine ⟨858670192510699490909453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2289787180028531975758541 858670192510699490909453)
                  ·
                    refine ⟨322001322191512309091045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858670192510699490909453 322001322191512309091045)
                    ·
                      rfl

theorem cell22_940643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 3].length) (baseStart_940643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940643 prefixEnd_940643 := by exact prefixLift 940643
  have htrace : WordTrace (prefixWord ++ tailWord_940643) baseStart_940643 baseEnd_940643 := by
    simpa [prefixWord, tailWord_940643, baseEnd_940643] using wordTrace_append hprefix tailTrace_940643
  have hstable : (prefixWord ++ tailWord_940643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940643).length < 2 ^ (prefixWord ++ tailWord_940643).sum := by decide
  have hdescent : baseEnd_940643 < baseStart_940643 := by decide
  rcases family_descends (prefixWord ++ tailWord_940643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940645 : List Nat := [1, 3, 1, 3, 5, 1, 1, 7]
def baseStart_940645 : Nat := 118140960795 + 940645 * 2 ^ 59
def prefixEnd_940645 : Nat := 4983230072969 + 3 ^ 40 * 940645 * 2
def baseEnd_940645 : Nat := 35778000759153885615671

theorem tailTrace_940645 : CollatzResearch.WordTrace tailWord_940645 prefixEnd_940645 35778000759153885615671 := by
  unfold tailWord_940645
  simp only [CollatzResearch.WordTrace]
  refine ⟨34308141677211289221159389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22872094451474192814106259 34308141677211289221159389)
  ·
    refine ⟨12865553128954233457934771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34308141677211289221159389 12865553128954233457934771)
    ·
      refine ⟨19298329693431350186902157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12865553128954233457934771 19298329693431350186902157)
      ·
        refine ⟨7236873635036756320088309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19298329693431350186902157 7236873635036756320088309)
        ·
          refine ⟨678456903284695905008279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7236873635036756320088309 678456903284695905008279)
          ·
            refine ⟨1017685354927043857512419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678456903284695905008279 1017685354927043857512419)
            ·
              refine ⟨1526528032390565786268629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017685354927043857512419 1526528032390565786268629)
              ·
                refine ⟨35778000759153885615671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1526528032390565786268629 35778000759153885615671)
                ·
                  rfl

theorem cell22_940645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 7].length) (baseStart_940645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940645 prefixEnd_940645 := by exact prefixLift 940645
  have htrace : WordTrace (prefixWord ++ tailWord_940645) baseStart_940645 baseEnd_940645 := by
    simpa [prefixWord, tailWord_940645, baseEnd_940645] using wordTrace_append hprefix tailTrace_940645
  have hstable : (prefixWord ++ tailWord_940645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940645).length < 2 ^ (prefixWord ++ tailWord_940645).sum := by decide
  have hdescent : baseEnd_940645 < baseStart_940645 := by decide
  rcases family_descends (prefixWord ++ tailWord_940645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940677 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_940677 : Nat := 118140960795 + 940677 * 2 ^ 59
def prefixEnd_940677 : Nat := 4983230072969 + 3 ^ 40 * 940677 * 2
def baseEnd_940677 : Nat := 322012961086347553740941

theorem tailTrace_940677 : CollatzResearch.WordTrace tailWord_940677 prefixEnd_940677 322012961086347553740941 := by
  unfold tailWord_940677
  simp only [CollatzResearch.WordTrace]
  refine ⟨34309308813095358686324285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22872872542063572457549523 34309308813095358686324285)
  ·
    refine ⟨12865990804910759507371607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34309308813095358686324285 12865990804910759507371607)
    ·
      refine ⟨19298986207366139261057411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12865990804910759507371607 19298986207366139261057411)
      ·
        refine ⟨28948479311049208891586117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19298986207366139261057411 28948479311049208891586117)
        ·
          refine ⟨5427839870821726667172397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28948479311049208891586117 5427839870821726667172397)
          ·
            refine ⟨2035439951558147500189649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5427839870821726667172397 2035439951558147500189649)
            ·
              refine ⟨1526579963668610625142237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035439951558147500189649 1526579963668610625142237)
              ·
                refine ⟨572467486375728984428339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526579963668610625142237 572467486375728984428339)
                ·
                  refine ⟨858701229563593476642509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572467486375728984428339 858701229563593476642509)
                  ·
                    refine ⟨322012961086347553740941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858701229563593476642509 322012961086347553740941)
                    ·
                      rfl

theorem cell22_940677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_940677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940677 prefixEnd_940677 := by exact prefixLift 940677
  have htrace : WordTrace (prefixWord ++ tailWord_940677) baseStart_940677 baseEnd_940677 := by
    simpa [prefixWord, tailWord_940677, baseEnd_940677] using wordTrace_append hprefix tailTrace_940677
  have hstable : (prefixWord ++ tailWord_940677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940677).length < 2 ^ (prefixWord ++ tailWord_940677).sum := by decide
  have hdescent : baseEnd_940677 < baseStart_940677 := by decide
  rcases family_descends (prefixWord ++ tailWord_940677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940690 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_940690 : Nat := 118140960795 + 940690 * 2 ^ 59
def prefixEnd_940690 : Nat := 4983230072969 + 3 ^ 40 * 940690 * 2
def baseEnd_940690 : Nat := 107339137084006617721967

theorem tailTrace_940690 : CollatzResearch.WordTrace tailWord_940690 prefixEnd_940690 107339137084006617721967 := by
  unfold tailWord_940690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8577445740512065476636881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22873188641365507937698349 8577445740512065476636881)
  ·
    refine ⟨6433084305384049107477661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8577445740512065476636881 6433084305384049107477661)
    ·
      refine ⟨2412406614519018415304123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6433084305384049107477661 2412406614519018415304123)
      ·
        refine ⟨3618609921778527622956185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2412406614519018415304123 3618609921778527622956185)
        ·
          refine ⟨2713957441333895717217139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3618609921778527622956185 2713957441333895717217139)
          ·
            refine ⟨4070936162000843575825709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2713957441333895717217139 4070936162000843575825709)
            ·
              refine ⟨1526601060750316340934641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4070936162000843575825709 1526601060750316340934641)
              ·
                refine ⟨1144950795562737255700981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1526601060750316340934641 1144950795562737255700981)
                ·
                  refine ⟨107339137084006617721967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1144950795562737255700981 107339137084006617721967)
                  ·
                    rfl

theorem cell22_940690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_940690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940690 prefixEnd_940690 := by exact prefixLift 940690
  have htrace : WordTrace (prefixWord ++ tailWord_940690) baseStart_940690 baseEnd_940690 := by
    simpa [prefixWord, tailWord_940690, baseEnd_940690] using wordTrace_append hprefix tailTrace_940690
  have hstable : (prefixWord ++ tailWord_940690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940690).length < 2 ^ (prefixWord ++ tailWord_940690).sum := by decide
  have hdescent : baseEnd_940690 < baseStart_940690 := by decide
  rcases family_descends (prefixWord ++ tailWord_940690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940735 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 4]
def baseStart_940735 : Nat := 118140960795 + 940735 * 2 ^ 59
def prefixEnd_940735 : Nat := 4983230072969 + 3 ^ 40 * 940735 * 2
def baseEnd_940735 : Nat := 107344271890551578596921

theorem tailTrace_940735 : CollatzResearch.WordTrace tailWord_940735 prefixEnd_940735 107344271890551578596921 := by
  unfold tailWord_940735
  simp only [CollatzResearch.WordTrace]
  refine ⟨34311424246885234591935659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22874282831256823061290439 34311424246885234591935659)
  ·
    refine ⟨51467136370327851887903489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34311424246885234591935659 51467136370327851887903489)
    ·
      refine ⟨38600352277745888915927617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51467136370327851887903489 38600352277745888915927617)
      ·
        refine ⟨28950264208309416686945713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38600352277745888915927617 28950264208309416686945713)
        ·
          refine ⟨21712698156232062515209285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28950264208309416686945713 21712698156232062515209285)
          ·
            refine ⟨4071130904293511721601741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21712698156232062515209285 4071130904293511721601741)
            ·
              refine ⟨1526674089110066895600653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4071130904293511721601741 1526674089110066895600653)
              ·
                refine ⟨572502783416275085850245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526674089110066895600653 572502783416275085850245)
                ·
                  refine ⟨107344271890551578596921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572502783416275085850245 107344271890551578596921)
                  ·
                    rfl

theorem cell22_940735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 4].length) (baseStart_940735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940735 prefixEnd_940735 := by exact prefixLift 940735
  have htrace : WordTrace (prefixWord ++ tailWord_940735) baseStart_940735 baseEnd_940735 := by
    simpa [prefixWord, tailWord_940735, baseEnd_940735] using wordTrace_append hprefix tailTrace_940735
  have hstable : (prefixWord ++ tailWord_940735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940735).length < 2 ^ (prefixWord ++ tailWord_940735).sum := by decide
  have hdescent : baseEnd_940735 < baseStart_940735 := by decide
  rcases family_descends (prefixWord ++ tailWord_940735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940750 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_940750 : Nat := 118140960795 + 940750 * 2 ^ 59
def prefixEnd_940750 : Nat := 4983230072969 + 3 ^ 40 * 940750 * 2
def baseEnd_940750 : Nat := 322037950478199696665717

theorem tailTrace_940750 : CollatzResearch.WordTrace tailWord_940750 prefixEnd_940750 322037950478199696665717 := by
  unfold tailWord_940750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288996417728861519216463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22874647561220594769154469 4288996417728861519216463)
  ·
    refine ⟨6433494626593292278824695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288996417728861519216463 6433494626593292278824695)
    ·
      refine ⟨9650241939889938418237043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433494626593292278824695 9650241939889938418237043)
      ·
        refine ⟨14475362909834907627355565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650241939889938418237043 14475362909834907627355565)
        ·
          refine ⟨5428261091188090360258337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14475362909834907627355565 5428261091188090360258337)
          ·
            refine ⟨4071195818391067770193753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5428261091188090360258337 4071195818391067770193753)
            ·
              refine ⟨3053396863793300827645315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071195818391067770193753 3053396863793300827645315)
              ·
                refine ⟨4580095295689951241467973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053396863793300827645315 4580095295689951241467973)
                ·
                  refine ⟨858767867941865857775245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4580095295689951241467973 858767867941865857775245)
                  ·
                    refine ⟨322037950478199696665717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858767867941865857775245 322037950478199696665717)
                    ·
                      rfl

theorem cell22_940750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_940750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940750 prefixEnd_940750 := by exact prefixLift 940750
  have htrace : WordTrace (prefixWord ++ tailWord_940750) baseStart_940750 baseEnd_940750 := by
    simpa [prefixWord, tailWord_940750, baseEnd_940750] using wordTrace_append hprefix tailTrace_940750
  have hstable : (prefixWord ++ tailWord_940750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940750).length < 2 ^ (prefixWord ++ tailWord_940750).sum := by decide
  have hdescent : baseEnd_940750 < baseStart_940750 := by decide
  rcases family_descends (prefixWord ++ tailWord_940750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940767 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 2, 3]
def baseStart_940767 : Nat := 118140960795 + 940767 * 2 ^ 59
def prefixEnd_940767 : Nat := 4983230072969 + 3 ^ 40 * 940767 * 2
def baseEnd_940767 : Nat := 322043769925617318990665

theorem tailTrace_940767 : CollatzResearch.WordTrace tailWord_940767 prefixEnd_940767 322043769925617318990665 := by
  unfold tailWord_940767
  simp only [CollatzResearch.WordTrace]
  refine ⟨34312591382769304057100555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22875060921846202704733703 34312591382769304057100555)
  ·
    refine ⟨51468887074153956085650833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34312591382769304057100555 51468887074153956085650833)
    ·
      refine ⟨38601665305615467064238125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51468887074153956085650833 38601665305615467064238125)
      ·
        refine ⟨14475624489605800149089297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38601665305615467064238125 14475624489605800149089297)
        ·
          refine ⟨10856718367204350111816973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14475624489605800149089297 10856718367204350111816973)
          ·
            refine ⟨4071269387701631291931365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10856718367204350111816973 4071269387701631291931365)
            ·
              refine ⟨763363010194055867237131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4071269387701631291931365 763363010194055867237131)
              ·
                refine ⟨1145044515291083800855697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763363010194055867237131 1145044515291083800855697)
                ·
                  refine ⟨858783386468312850641773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145044515291083800855697 858783386468312850641773)
                  ·
                    refine ⟨322043769925617318990665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858783386468312850641773 322043769925617318990665)
                    ·
                      rfl

theorem cell22_940767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_940767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940767 prefixEnd_940767 := by exact prefixLift 940767
  have htrace : WordTrace (prefixWord ++ tailWord_940767) baseStart_940767 baseEnd_940767 := by
    simpa [prefixWord, tailWord_940767, baseEnd_940767] using wordTrace_append hprefix tailTrace_940767
  have hstable : (prefixWord ++ tailWord_940767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940767).length < 2 ^ (prefixWord ++ tailWord_940767).sum := by decide
  have hdescent : baseEnd_940767 < baseStart_940767 := by decide
  rcases family_descends (prefixWord ++ tailWord_940767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940829 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_940829 : Nat := 118140960795 + 940829 * 2 ^ 59
def prefixEnd_940829 : Nat := 4983230072969 + 3 ^ 40 * 940829 * 2
def baseEnd_940829 : Nat := 322064993792669823940475

theorem tailTrace_940829 : CollatzResearch.WordTrace tailWord_940829 prefixEnd_940829 322064993792669823940475 := by
  unfold tailWord_940829
  simp only [CollatzResearch.WordTrace]
  refine ⟨34314852708544688645857541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22876568472363125763905027 34314852708544688645857541)
  ·
    refine ⟨6434034882852129121098289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34314852708544688645857541 6434034882852129121098289)
    ·
      refine ⟨4825526162139096840823717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6434034882852129121098289 4825526162139096840823717)
      ·
        refine ⟨904786155401080657654447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4825526162139096840823717 904786155401080657654447)
        ·
          refine ⟨1357179233101620986481671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904786155401080657654447 1357179233101620986481671)
          ·
            refine ⟨2035768849652431479722507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357179233101620986481671 2035768849652431479722507)
            ·
              refine ⟨3053653274478647219583761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035768849652431479722507 3053653274478647219583761)
              ·
                refine ⟨2290239955858985414687821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053653274478647219583761 2290239955858985414687821)
                ·
                  refine ⟨858839983447119530507933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2290239955858985414687821 858839983447119530507933)
                  ·
                    refine ⟨322064993792669823940475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858839983447119530507933 322064993792669823940475)
                    ·
                      rfl

theorem cell22_940829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_940829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940829 prefixEnd_940829 := by exact prefixLift 940829
  have htrace : WordTrace (prefixWord ++ tailWord_940829) baseStart_940829 baseEnd_940829 := by
    simpa [prefixWord, tailWord_940829, baseEnd_940829] using wordTrace_append hprefix tailTrace_940829
  have hstable : (prefixWord ++ tailWord_940829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940829).length < 2 ^ (prefixWord ++ tailWord_940829).sum := by decide
  have hdescent : baseEnd_940829 < baseStart_940829 := by decide
  rcases family_descends (prefixWord ++ tailWord_940829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940846 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_940846 : Nat := 118140960795 + 940846 * 2 ^ 59
def prefixEnd_940846 : Nat := 4983230072969 + 3 ^ 40 * 940846 * 2
def baseEnd_940846 : Nat := 322070813240087446265423

theorem tailTrace_940846 : CollatzResearch.WordTrace tailWord_940846 prefixEnd_940846 322070813240087446265423 := by
  unfold tailWord_940846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289434093685387568653299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22876981832988733699484261 4289434093685387568653299)
  ·
    refine ⟨6434151140528081352979949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4289434093685387568653299 6434151140528081352979949)
    ·
      refine ⟨2412806677698030507367481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6434151140528081352979949 2412806677698030507367481)
      ·
        refine ⟨1809605008273522880525611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2412806677698030507367481 1809605008273522880525611)
        ·
          refine ⟨2714407512410284320788417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809605008273522880525611 2714407512410284320788417)
          ·
            refine ⟨2035805634307713240591313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2714407512410284320788417 2035805634307713240591313)
            ·
              refine ⟨1526854225730784930443485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035805634307713240591313 1526854225730784930443485)
              ·
                refine ⟨572570334649044348916307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526854225730784930443485 572570334649044348916307)
                ·
                  refine ⟨858855501973566523374461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572570334649044348916307 858855501973566523374461)
                  ·
                    refine ⟨322070813240087446265423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858855501973566523374461 322070813240087446265423)
                    ·
                      rfl

theorem cell22_940846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_940846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940846 prefixEnd_940846 := by exact prefixLift 940846
  have htrace : WordTrace (prefixWord ++ tailWord_940846) baseStart_940846 baseEnd_940846 := by
    simpa [prefixWord, tailWord_940846, baseEnd_940846] using wordTrace_append hprefix tailTrace_940846
  have hstable : (prefixWord ++ tailWord_940846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940846).length < 2 ^ (prefixWord ++ tailWord_940846).sum := by decide
  have hdescent : baseEnd_940846 < baseStart_940846 := by decide
  rcases family_descends (prefixWord ++ tailWord_940846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940855 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 1, 4]
def baseStart_940855 : Nat := 118140960795 + 940855 * 2 ^ 59
def prefixEnd_940855 : Nat := 4983230072969 + 3 ^ 40 * 940855 * 2
def baseEnd_940855 : Nat := 322073894124014422790395

theorem tailTrace_940855 : CollatzResearch.WordTrace tailWord_940855 prefixEnd_940855 322073894124014422790395 := by
  unfold tailWord_940855
  simp only [CollatzResearch.WordTrace]
  refine ⟨34315801006450495086304019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22877200670966996724202679 34315801006450495086304019)
  ·
    refine ⟨51473701509675742629456029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34315801006450495086304019 51473701509675742629456029)
    ·
      refine ⟨19302638066128403486046011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51473701509675742629456029 19302638066128403486046011)
      ·
        refine ⟨28953957099192605229069017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19302638066128403486046011 28953957099192605229069017)
        ·
          refine ⟨21715467824394453921801763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28953957099192605229069017 21715467824394453921801763)
          ·
            refine ⟨32573201736591680882702645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21715467824394453921801763 32573201736591680882702645)
            ·
              refine ⟨3053737662805470082753373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32573201736591680882702645 3053737662805470082753373)
              ·
                refine ⟨1145151623552051281032515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3053737662805470082753373 1145151623552051281032515)
                ·
                  refine ⟨1717727435328076921548773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145151623552051281032515 1717727435328076921548773)
                  ·
                    refine ⟨322073894124014422790395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717727435328076921548773 322073894124014422790395)
                    ·
                      rfl

theorem cell22_940855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_940855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940855 prefixEnd_940855 := by exact prefixLift 940855
  have htrace : WordTrace (prefixWord ++ tailWord_940855) baseStart_940855 baseEnd_940855 := by
    simpa [prefixWord, tailWord_940855, baseEnd_940855] using wordTrace_append hprefix tailTrace_940855
  have hstable : (prefixWord ++ tailWord_940855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940855).length < 2 ^ (prefixWord ++ tailWord_940855).sum := by decide
  have hdescent : baseEnd_940855 < baseStart_940855 := by decide
  rcases family_descends (prefixWord ++ tailWord_940855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940900 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_940900 : Nat := 118140960795 + 940900 * 2 ^ 59
def prefixEnd_940900 : Nat := 4983230072969 + 3 ^ 40 * 940900 * 2
def baseEnd_940900 : Nat := 322089298543649305415257

theorem tailTrace_940900 : CollatzResearch.WordTrace tailWord_940900 prefixEnd_940900 322089298543649305415257 := by
  unfold tailWord_940900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158721145643733885846077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22878294860858311847794769 17158721145643733885846077)
  ·
    refine ⟨6434520429616400207192279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17158721145643733885846077 6434520429616400207192279)
    ·
      refine ⟨9651780644424600310788419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434520429616400207192279 9651780644424600310788419)
      ·
        refine ⟨14477670966636900466182629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9651780644424600310788419 14477670966636900466182629)
        ·
          refine ⟨2714563306244418837409243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14477670966636900466182629 2714563306244418837409243)
          ·
            refine ⟨4071844959366628256113865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714563306244418837409243 4071844959366628256113865)
            ·
              refine ⟨3053883719524971192085399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071844959366628256113865 3053883719524971192085399)
              ·
                refine ⟨4580825579287456788128099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053883719524971192085399 4580825579287456788128099)
                ·
                  refine ⟨6871238368931185182192149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580825579287456788128099 6871238368931185182192149)
                  ·
                    refine ⟨322089298543649305415257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6871238368931185182192149 322089298543649305415257)
                    ·
                      rfl

theorem cell22_940900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_940900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940900 prefixEnd_940900 := by exact prefixLift 940900
  have htrace : WordTrace (prefixWord ++ tailWord_940900) baseStart_940900 baseEnd_940900 := by
    simpa [prefixWord, tailWord_940900, baseEnd_940900] using wordTrace_append hprefix tailTrace_940900
  have hstable : (prefixWord ++ tailWord_940900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940900).length < 2 ^ (prefixWord ++ tailWord_940900).sum := by decide
  have hdescent : baseEnd_940900 < baseStart_940900 := by decide
  rcases family_descends (prefixWord ++ tailWord_940900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940904 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 4]
def baseStart_940904 : Nat := 118140960795 + 940904 * 2 ^ 59
def prefixEnd_940904 : Nat := 4983230072969 + 3 ^ 40 * 940904 * 2
def baseEnd_940904 : Nat := 107363555941798209438415

theorem tailTrace_940904 : CollatzResearch.WordTrace tailWord_940904 prefixEnd_940904 107363555941798209438415 := by
  unfold tailWord_940904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158794091636488227418883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22878392122181984303225177 17158794091636488227418883)
  ·
    refine ⟨25738191137454732341128325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17158794091636488227418883 25738191137454732341128325)
    ·
      refine ⟨4825910838272762313961561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25738191137454732341128325 4825910838272762313961561)
      ·
        refine ⟨3619433128704571735471171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4825910838272762313961561 3619433128704571735471171)
        ·
          refine ⟨5429149693056857603206757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619433128704571735471171 5429149693056857603206757)
          ·
            refine ⟨1017965567448160800601267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5429149693056857603206757 1017965567448160800601267)
            ·
              refine ⟨1526948351172241200901901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017965567448160800601267 1526948351172241200901901)
              ·
                refine ⟨572605631689590450338213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526948351172241200901901 572605631689590450338213)
                ·
                  refine ⟨107363555941798209438415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 572605631689590450338213 107363555941798209438415)
                  ·
                    rfl

theorem cell22_940904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_940904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940904 prefixEnd_940904 := by exact prefixLift 940904
  have htrace : WordTrace (prefixWord ++ tailWord_940904) baseStart_940904 baseEnd_940904 := by
    simpa [prefixWord, tailWord_940904, baseEnd_940904] using wordTrace_append hprefix tailTrace_940904
  have hstable : (prefixWord ++ tailWord_940904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940904).length < 2 ^ (prefixWord ++ tailWord_940904).sum := by decide
  have hdescent : baseEnd_940904 < baseStart_940904 := by decide
  rcases family_descends (prefixWord ++ tailWord_940904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940917 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_940917 : Nat := 118140960795 + 940917 * 2 ^ 59
def prefixEnd_940917 : Nat := 4983230072969 + 3 ^ 40 * 940917 * 2
def baseEnd_940917 : Nat := 322095117991066927740205

theorem tailTrace_940917 : CollatzResearch.WordTrace tailWord_940917 prefixEnd_940917 322095117991066927740205 := by
  unfold tailWord_940917
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318062332225879675061005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22878708221483919783374003 34318062332225879675061005)
  ·
    refine ⟨12869273374584704878147877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34318062332225879675061005 12869273374584704878147877)
    ·
      refine ⟨2412988757734632164652727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12869273374584704878147877 2412988757734632164652727)
      ·
        refine ⟨3619483136601948246979091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2412988757734632164652727 3619483136601948246979091)
        ·
          refine ⟨5429224704902922370468637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619483136601948246979091 5429224704902922370468637)
          ·
            refine ⟨2035959264338595888925739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5429224704902922370468637 2035959264338595888925739)
            ·
              refine ⟨3053938896507893833388609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035959264338595888925739 3053938896507893833388609)
              ·
                refine ⟨2290454172380920375041457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053938896507893833388609 2290454172380920375041457)
                ·
                  refine ⟨1717840629285690281281093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2290454172380920375041457 1717840629285690281281093)
                  ·
                    refine ⟨322095117991066927740205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1717840629285690281281093 322095117991066927740205)
                    ·
                      rfl

theorem cell22_940917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_940917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940917 prefixEnd_940917 := by exact prefixLift 940917
  have htrace : WordTrace (prefixWord ++ tailWord_940917) baseStart_940917 baseEnd_940917 := by
    simpa [prefixWord, tailWord_940917, baseEnd_940917] using wordTrace_append hprefix tailTrace_940917
  have hstable : (prefixWord ++ tailWord_940917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940917).length < 2 ^ (prefixWord ++ tailWord_940917).sum := by decide
  have hdescent : baseEnd_940917 < baseStart_940917 := by decide
  rcases family_descends (prefixWord ++ tailWord_940917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940936 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 2, 3]
def baseStart_940936 : Nat := 118140960795 + 940936 * 2 ^ 59
def prefixEnd_940936 : Nat := 4983230072969 + 3 ^ 40 * 940936 * 2
def baseEnd_940936 : Nat := 322101622079357211515147

theorem tailTrace_940936 : CollatzResearch.WordTrace tailWord_940936 prefixEnd_940936 322101622079357211515147 := by
  unfold tailWord_940936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159377659578522960001331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22879170212771363946668441 17159377659578522960001331)
  ·
    refine ⟨25739066489367784440001997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17159377659578522960001331 25739066489367784440001997)
    ·
      refine ⟨9652149933512919165000749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25739066489367784440001997 9652149933512919165000749)
      ·
        refine ⟨3619556225067344686875281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9652149933512919165000749 3619556225067344686875281)
        ·
          refine ⟨2714667168800508515156461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3619556225067344686875281 2714667168800508515156461)
          ·
            refine ⟨1018000188300190693183673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2714667168800508515156461 1018000188300190693183673)
            ·
              refine ⟨763500141225143019887755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018000188300190693183673 763500141225143019887755)
              ·
                refine ⟨1145250211837714529831633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763500141225143019887755 1145250211837714529831633)
                ·
                  refine ⟨858937658878285897373725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1145250211837714529831633 858937658878285897373725)
                  ·
                    refine ⟨322101622079357211515147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858937658878285897373725 322101622079357211515147)
                    ·
                      rfl

theorem cell22_940936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_940936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940936 prefixEnd_940936 := by exact prefixLift 940936
  have htrace : WordTrace (prefixWord ++ tailWord_940936) baseStart_940936 baseEnd_940936 := by
    simpa [prefixWord, tailWord_940936, baseEnd_940936] using wordTrace_append hprefix tailTrace_940936
  have hstable : (prefixWord ++ tailWord_940936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940936).length < 2 ^ (prefixWord ++ tailWord_940936).sum := by decide
  have hdescent : baseEnd_940936 < baseStart_940936 := by decide
  rcases family_descends (prefixWord ++ tailWord_940936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940964 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_940964 : Nat := 118140960795 + 940964 * 2 ^ 59
def prefixEnd_940964 : Nat := 4983230072969 + 3 ^ 40 * 940964 * 2
def baseEnd_940964 : Nat := 322111207051574471815061

theorem tailTrace_940964 : CollatzResearch.WordTrace tailWord_940964 prefixEnd_940964 322111207051574471815061 := by
  unfold tailWord_940964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159888281527803351010973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22879851042037071134681297 17159888281527803351010973)
  ·
    refine ⟨6434958105572926256629115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17159888281527803351010973 6434958105572926256629115)
    ·
      refine ⟨9652437158359389384943673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434958105572926256629115 9652437158359389384943673)
      ·
        refine ⟨7239327868769542038707755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9652437158359389384943673 7239327868769542038707755)
        ·
          refine ⟨10858991803154313058061633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239327868769542038707755 10858991803154313058061633)
          ·
            refine ⟨8144243852365734793546225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10858991803154313058061633 8144243852365734793546225)
            ·
              refine ⟨6108182889274301095159669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8144243852365734793546225 6108182889274301095159669)
              ·
                refine ⟨572642145869465727671219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6108182889274301095159669 572642145869465727671219)
                ·
                  refine ⟨858963218804198591506829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572642145869465727671219 858963218804198591506829)
                  ·
                    refine ⟨322111207051574471815061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858963218804198591506829 322111207051574471815061)
                    ·
                      rfl

theorem cell22_940964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_940964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_940964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_940964 prefixEnd_940964 := by exact prefixLift 940964
  have htrace : WordTrace (prefixWord ++ tailWord_940964) baseStart_940964 baseEnd_940964 := by
    simpa [prefixWord, tailWord_940964, baseEnd_940964] using wordTrace_append hprefix tailTrace_940964
  have hstable : (prefixWord ++ tailWord_940964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940964).length < 2 ^ (prefixWord ++ tailWord_940964).sum := by decide
  have hdescent : baseEnd_940964 < baseStart_940964 := by decide
  rcases family_descends (prefixWord ++ tailWord_940964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941058 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_941058 : Nat := 118140960795 + 941058 * 2 ^ 59
def prefixEnd_941058 : Nat := 4983230072969 + 3 ^ 40 * 941058 * 2
def baseEnd_941058 : Nat := 322143385172589559964773

theorem tailTrace_941058 : CollatzResearch.WordTrace tailWord_941058 prefixEnd_941058 322143385172589559964773 := by
  unfold tailWord_941058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8580801256178765188985957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22882136683143373837295885 8580801256178765188985957)
  ·
    refine ⟨1608900235533518472934867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8580801256178765188985957 1608900235533518472934867)
    ·
      refine ⟨2413350353300277709402301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1608900235533518472934867 2413350353300277709402301)
      ·
        refine ⟨905006382487604141025863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2413350353300277709402301 905006382487604141025863)
        ·
          refine ⟨1357509573731406211538795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905006382487604141025863 1357509573731406211538795)
          ·
            refine ⟨2036264360597109317308193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357509573731406211538795 2036264360597109317308193)
            ·
              refine ⟨1527198270447831987981145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036264360597109317308193 1527198270447831987981145)
              ·
                refine ⟨1145398702835873990985859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527198270447831987981145 1145398702835873990985859)
                ·
                  refine ⟨1718098054253810986478789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145398702835873990985859 1718098054253810986478789)
                  ·
                    refine ⟨322143385172589559964773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1718098054253810986478789 322143385172589559964773)
                    ·
                      rfl

theorem cell22_941058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_941058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941058 prefixEnd_941058 := by exact prefixLift 941058
  have htrace : WordTrace (prefixWord ++ tailWord_941058) baseStart_941058 baseEnd_941058 := by
    simpa [prefixWord, tailWord_941058, baseEnd_941058] using wordTrace_append hprefix tailTrace_941058
  have hstable : (prefixWord ++ tailWord_941058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941058).length < 2 ^ (prefixWord ++ tailWord_941058).sum := by decide
  have hdescent : baseEnd_941058 < baseStart_941058 := by decide
  rcases family_descends (prefixWord ++ tailWord_941058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941067 : List Nat := [1, 1, 1, 1, 6, 2, 4, 6]
def baseStart_941067 : Nat := 118140960795 + 941067 * 2 ^ 59
def prefixEnd_941067 : Nat := 4983230072969 + 3 ^ 40 * 941067 * 2
def baseEnd_941067 : Nat := 35794051784057392943305

theorem tailTrace_941067 : CollatzResearch.WordTrace tailWord_941067 prefixEnd_941067 35794051784057392943305 := by
  unfold tailWord_941067
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323533281682455293021455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22882355521121636862014303 34323533281682455293021455)
  ·
    refine ⟨51485299922523682939532183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34323533281682455293021455 51485299922523682939532183)
    ·
      refine ⟨77227949883785524409298275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51485299922523682939532183 77227949883785524409298275)
      ·
        refine ⟨115841924825678286613947413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77227949883785524409298275 115841924825678286613947413)
        ·
          refine ⟨5430090226203669685028785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115841924825678286613947413 5430090226203669685028785)
          ·
            refine ⟨4072567669652752263771589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5430090226203669685028785 4072567669652752263771589)
            ·
              refine ⟨763606438059891049457173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4072567669652752263771589 763606438059891049457173)
              ·
                refine ⟨35794051784057392943305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 763606438059891049457173 35794051784057392943305)
                ·
                  rfl

theorem cell22_941067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 6].length) (baseStart_941067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941067 prefixEnd_941067 := by exact prefixLift 941067
  have htrace : WordTrace (prefixWord ++ tailWord_941067) baseStart_941067 baseEnd_941067 := by
    simpa [prefixWord, tailWord_941067, baseEnd_941067] using wordTrace_append hprefix tailTrace_941067
  have hstable : (prefixWord ++ tailWord_941067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941067).length < 2 ^ (prefixWord ++ tailWord_941067).sum := by decide
  have hdescent : baseEnd_941067 < baseStart_941067 := by decide
  rcases family_descends (prefixWord ++ tailWord_941067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941084 : List Nat := [2, 2, 3, 1, 5, 1, 8]
def baseStart_941084 : Nat := 118140960795 + 941084 * 2 ^ 59
def prefixEnd_941084 : Nat := 4983230072969 + 3 ^ 40 * 941084 * 2
def baseEnd_941084 : Nat := 11931566129775339215359

theorem tailTrace_941084 : CollatzResearch.WordTrace tailWord_941084 prefixEnd_941084 11931566129775339215359 := by
  unfold tailWord_941084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162076661310433598195153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22882768881747244797593537 17162076661310433598195153)
  ·
    refine ⟨12871557495982825198646365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17162076661310433598195153 12871557495982825198646365)
    ·
      refine ⟨4826834060993559449492387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12871557495982825198646365 4826834060993559449492387)
      ·
        refine ⟨7240251091490339174238581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826834060993559449492387 7240251091490339174238581)
        ·
          refine ⟨678773539827219297584867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7240251091490339174238581 678773539827219297584867)
          ·
            refine ⟨1018160309740828946377301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678773539827219297584867 1018160309740828946377301)
            ·
              refine ⟨11931566129775339215359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1018160309740828946377301 11931566129775339215359)
              ·
                rfl

theorem cell22_941084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 8].length) (baseStart_941084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941084 prefixEnd_941084 := by exact prefixLift 941084
  have htrace : WordTrace (prefixWord ++ tailWord_941084) baseStart_941084 baseEnd_941084 := by
    simpa [prefixWord, tailWord_941084, baseEnd_941084] using wordTrace_append hprefix tailTrace_941084
  have hstable : (prefixWord ++ tailWord_941084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941084).length < 2 ^ (prefixWord ++ tailWord_941084).sum := by decide
  have hdescent : baseEnd_941084 < baseStart_941084 := by decide
  rcases family_descends (prefixWord ++ tailWord_941084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941157 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 6]
def baseStart_941157 : Nat := 118140960795 + 941157 * 2 ^ 59
def prefixEnd_941157 : Nat := 4983230072969 + 3 ^ 40 * 941157 * 2
def baseEnd_941157 : Nat := 107392424965262100579823

theorem tailTrace_941157 : CollatzResearch.WordTrace tailWord_941157 prefixEnd_941157 107392424965262100579823 := by
  unfold tailWord_941157
  simp only [CollatzResearch.WordTrace]
  refine ⟨34326815851356400663797725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22884543900904267109198483 34326815851356400663797725)
  ·
    refine ⟨12872555944258650248924147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34326815851356400663797725 12872555944258650248924147)
    ·
      refine ⟨19308833916387975373386221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12872555944258650248924147 19308833916387975373386221)
      ·
        refine ⟨7240812718645490765019833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19308833916387975373386221 7240812718645490765019833)
        ·
          refine ⟨5430609538984118073764875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7240812718645490765019833 5430609538984118073764875)
          ·
            refine ⟨8145914308476177110647313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430609538984118073764875 8145914308476177110647313)
            ·
              refine ⟨6109435731357132832985485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145914308476177110647313 6109435731357132832985485)
              ·
                refine ⟨2291038399258924812369557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6109435731357132832985485 2291038399258924812369557)
                ·
                  refine ⟨107392424965262100579823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2291038399258924812369557 107392424965262100579823)
                  ·
                    rfl

theorem cell22_941157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_941157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941157 prefixEnd_941157 := by exact prefixLift 941157
  have htrace : WordTrace (prefixWord ++ tailWord_941157) baseStart_941157 baseEnd_941157 := by
    simpa [prefixWord, tailWord_941157, baseEnd_941157] using wordTrace_append hprefix tailTrace_941157
  have hstable : (prefixWord ++ tailWord_941157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941157).length < 2 ^ (prefixWord ++ tailWord_941157).sum := by decide
  have hdescent : baseEnd_941157 < baseStart_941157 := by decide
  rcases family_descends (prefixWord ++ tailWord_941157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941174 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_941174 : Nat := 118140960795 + 941174 * 2 ^ 59
def prefixEnd_941174 : Nat := 4983230072969 + 3 ^ 40 * 941174 * 2
def baseEnd_941174 : Nat := 107394364781067974688139

theorem tailTrace_941174 : CollatzResearch.WordTrace tailWord_941174 prefixEnd_941174 107394364781067974688139 := by
  unfold tailWord_941174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2145464743268425785447911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22884957261529875044777717 2145464743268425785447911)
  ·
    refine ⟨3218197114902638678171867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2145464743268425785447911 3218197114902638678171867)
    ·
      refine ⟨4827295672353958017257801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218197114902638678171867 4827295672353958017257801)
      ·
        refine ⟨3620471754265468512943351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827295672353958017257801 3620471754265468512943351)
        ·
          refine ⟨5430707631398202769415027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620471754265468512943351 5430707631398202769415027)
          ·
            refine ⟨8146061447097304154122541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430707631398202769415027 8146061447097304154122541)
            ·
              refine ⟨3054773042661489057795953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8146061447097304154122541 3054773042661489057795953)
              ·
                refine ⟨2291079781996116793346965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054773042661489057795953 2291079781996116793346965)
                ·
                  refine ⟨107394364781067974688139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2291079781996116793346965 107394364781067974688139)
                  ·
                    rfl

theorem cell22_941174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_941174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941174 prefixEnd_941174 := by exact prefixLift 941174
  have htrace : WordTrace (prefixWord ++ tailWord_941174) baseStart_941174 baseEnd_941174 := by
    simpa [prefixWord, tailWord_941174, baseEnd_941174] using wordTrace_append hprefix tailTrace_941174
  have hstable : (prefixWord ++ tailWord_941174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941174).length < 2 ^ (prefixWord ++ tailWord_941174).sum := by decide
  have hdescent : baseEnd_941174 < baseStart_941174 := by decide
  rcases family_descends (prefixWord ++ tailWord_941174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941187 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 1, 6]
def baseStart_941187 : Nat := 118140960795 + 941187 * 2 ^ 59
def prefixEnd_941187 : Nat := 4983230072969 + 3 ^ 40 * 941187 * 2
def baseEnd_941187 : Nat := 322187544508876223489377

theorem tailTrace_941187 : CollatzResearch.WordTrace tailWord_941187 prefixEnd_941187 322187544508876223489377 := by
  unfold tailWord_941187
  simp only [CollatzResearch.WordTrace]
  refine ⟨34327910041247715787389815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22885273360831810524926543 34327910041247715787389815)
  ·
    refine ⟨51491865061871573681084723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34327910041247715787389815 51491865061871573681084723)
    ·
      refine ⟨77237797592807360521627085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51491865061871573681084723 77237797592807360521627085)
      ·
        refine ⟨28964174097302760195610157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77237797592807360521627085 28964174097302760195610157)
        ·
          refine ⟨10861565286488535073353809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28964174097302760195610157 10861565286488535073353809)
          ·
            refine ⟨8146173964866401305015357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10861565286488535073353809 8146173964866401305015357)
            ·
              refine ⟨3054815236824900489380759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8146173964866401305015357 3054815236824900489380759)
              ·
                refine ⟨4582222855237350734071139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054815236824900489380759 4582222855237350734071139)
                ·
                  refine ⟨6873334282856026101106709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582222855237350734071139 6873334282856026101106709)
                  ·
                    refine ⟨322187544508876223489377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6873334282856026101106709 322187544508876223489377)
                    ·
                      rfl

theorem cell22_941187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_941187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941187 prefixEnd_941187 := by exact prefixLift 941187
  have htrace : WordTrace (prefixWord ++ tailWord_941187) baseStart_941187 baseEnd_941187 := by
    simpa [prefixWord, tailWord_941187, baseEnd_941187] using wordTrace_append hprefix tailTrace_941187
  have hstable : (prefixWord ++ tailWord_941187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941187).length < 2 ^ (prefixWord ++ tailWord_941187).sum := by decide
  have hdescent : baseEnd_941187 < baseStart_941187 := by decide
  rcases family_descends (prefixWord ++ tailWord_941187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941247 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 7]
def baseStart_941247 : Nat := 118140960795 + 941247 * 2 ^ 59
def prefixEnd_941247 : Nat := 4983230072969 + 3 ^ 40 * 941247 * 2
def baseEnd_941247 : Nat := 107402694578352022329731

theorem tailTrace_941247 : CollatzResearch.WordTrace tailWord_941247 prefixEnd_941247 107402694578352022329731 := by
  unfold tailWord_941247
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330098421030346034573995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22886732280686897356382663 34330098421030346034573995)
  ·
    refine ⟨51495147631545519051860993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34330098421030346034573995 51495147631545519051860993)
    ·
      refine ⟨38621360723659139288895745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51495147631545519051860993 38621360723659139288895745)
      ·
        refine ⟨28966020542744354466671809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38621360723659139288895745 28966020542744354466671809)
        ·
          refine ⟨21724515407058265850003857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28966020542744354466671809 21724515407058265850003857)
          ·
            refine ⟨16293386555293699387502893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21724515407058265850003857 16293386555293699387502893)
            ·
              refine ⟨6110019958235137270313585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16293386555293699387502893 6110019958235137270313585)
              ·
                refine ⟨4582514968676352952735189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110019958235137270313585 4582514968676352952735189)
                ·
                  refine ⟨107402694578352022329731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4582514968676352952735189 107402694578352022329731)
                  ·
                    rfl

theorem cell22_941247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_941247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941247 prefixEnd_941247 := by exact prefixLift 941247
  have htrace : WordTrace (prefixWord ++ tailWord_941247) baseStart_941247 baseEnd_941247 := by
    simpa [prefixWord, tailWord_941247, baseEnd_941247] using wordTrace_append hprefix tailTrace_941247
  have hstable : (prefixWord ++ tailWord_941247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941247).length < 2 ^ (prefixWord ++ tailWord_941247).sum := by decide
  have hdescent : baseEnd_941247 < baseStart_941247 := by decide
  rcases family_descends (prefixWord ++ tailWord_941247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941251 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 1, 3]
def baseStart_941251 : Nat := 118140960795 + 941251 * 2 ^ 59
def prefixEnd_941251 : Nat := 4983230072969 + 3 ^ 40 * 941251 * 2
def baseEnd_941251 : Nat := 322209453016801389889181

theorem tailTrace_941251 : CollatzResearch.WordTrace tailWord_941251 prefixEnd_941251 322209453016801389889181 := by
  unfold tailWord_941251
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330244313015854717719607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22886829542010569811813071 34330244313015854717719607)
  ·
    refine ⟨51495366469523782076579411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34330244313015854717719607 51495366469523782076579411)
    ·
      refine ⟨77243049704285673114869117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51495366469523782076579411 77243049704285673114869117)
      ·
        refine ⟨28966143639107127418075919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77243049704285673114869117 28966143639107127418075919)
        ·
          refine ⟨43449215458660691127113879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28966143639107127418075919 43449215458660691127113879)
          ·
            refine ⟨65173823187991036690670819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43449215458660691127113879 65173823187991036690670819)
            ·
              refine ⟨97760734781986555036006229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65173823187991036690670819 97760734781986555036006229)
              ·
                refine ⟨572816805363202470914099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 97760734781986555036006229 572816805363202470914099)
                ·
                  refine ⟨859225208044803706371149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572816805363202470914099 859225208044803706371149)
                  ·
                    refine ⟨322209453016801389889181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859225208044803706371149 322209453016801389889181)
                    ·
                      rfl

theorem cell22_941251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 3].length) (baseStart_941251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941251 prefixEnd_941251 := by exact prefixLift 941251
  have htrace : WordTrace (prefixWord ++ tailWord_941251) baseStart_941251 baseEnd_941251 := by
    simpa [prefixWord, tailWord_941251, baseEnd_941251] using wordTrace_append hprefix tailTrace_941251
  have hstable : (prefixWord ++ tailWord_941251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941251).length < 2 ^ (prefixWord ++ tailWord_941251).sum := by decide
  have hdescent : baseEnd_941251 < baseStart_941251 := by decide
  rcases family_descends (prefixWord ++ tailWord_941251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941281 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 5]
def baseStart_941281 : Nat := 118140960795 + 941281 * 2 ^ 59
def prefixEnd_941281 : Nat := 4983230072969 + 3 ^ 40 * 941281 * 2
def baseEnd_941281 : Nat := 107406574209963770546363

theorem tailTrace_941281 : CollatzResearch.WordTrace tailWord_941281 prefixEnd_941281 107406574209963770546363 := by
  unfold tailWord_941281
  simp only [CollatzResearch.WordTrace]
  refine ⟨34331338502907169841311697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22887559001938113227541131 34331338502907169841311697)
  ·
    refine ⟨25748503877180377380983773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34331338502907169841311697 25748503877180377380983773)
    ·
      refine ⟨9655688953942641517868915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25748503877180377380983773 9655688953942641517868915)
      ·
        refine ⟨14483533430913962276803373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9655688953942641517868915 14483533430913962276803373)
        ·
          refine ⟨5431325036592735853801265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14483533430913962276803373 5431325036592735853801265)
          ·
            refine ⟨4073493777444551890350949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5431325036592735853801265 4073493777444551890350949)
            ·
              refine ⟨763780083270853479440803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4073493777444551890350949 763780083270853479440803)
              ·
                refine ⟨1145670124906280219161205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763780083270853479440803 1145670124906280219161205)
                ·
                  refine ⟨107406574209963770546363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1145670124906280219161205 107406574209963770546363)
                  ·
                    rfl

theorem cell22_941281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_941281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941281 prefixEnd_941281 := by exact prefixLift 941281
  have htrace : WordTrace (prefixWord ++ tailWord_941281) baseStart_941281 baseEnd_941281 := by
    simpa [prefixWord, tailWord_941281, baseEnd_941281] using wordTrace_append hprefix tailTrace_941281
  have hstable : (prefixWord ++ tailWord_941281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941281).length < 2 ^ (prefixWord ++ tailWord_941281).sum := by decide
  have hdescent : baseEnd_941281 < baseStart_941281 := by decide
  rcases family_descends (prefixWord ++ tailWord_941281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941341 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_941341 : Nat := 118140960795 + 941341 * 2 ^ 59
def prefixEnd_941341 : Nat := 4983230072969 + 3 ^ 40 * 941341 * 2
def baseEnd_941341 : Nat := 322240261856071155138905

theorem tailTrace_941341 : CollatzResearch.WordTrace tailWord_941341 prefixEnd_941341 322240261856071155138905 := by
  unfold tailWord_941341
  simp only [CollatzResearch.WordTrace]
  refine ⟨34333526882689800088495877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22889017921793200058997251 34333526882689800088495877)
  ·
    refine ⟨6437536290504337516592977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34333526882689800088495877 6437536290504337516592977)
    ·
      refine ⟨4828152217878253137444733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6437536290504337516592977 4828152217878253137444733)
      ·
        refine ⟨1810557081704344926541775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4828152217878253137444733 1810557081704344926541775)
        ·
          refine ⟨2715835622556517389812663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810557081704344926541775 2715835622556517389812663)
          ·
            refine ⟨4073753433834776084718995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715835622556517389812663 4073753433834776084718995)
            ·
              refine ⟨6110630150752164127078493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073753433834776084718995 6110630150752164127078493)
              ·
                refine ⟨2291486306532061547654435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6110630150752164127078493 2291486306532061547654435)
                ·
                  refine ⟨3437229459798092321481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291486306532061547654435 3437229459798092321481653)
                  ·
                    refine ⟨322240261856071155138905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3437229459798092321481653 322240261856071155138905)
                    ·
                      rfl

theorem cell22_941341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_941341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941341 prefixEnd_941341 := by exact prefixLift 941341
  have htrace : WordTrace (prefixWord ++ tailWord_941341) baseStart_941341 baseEnd_941341 := by
    simpa [prefixWord, tailWord_941341, baseEnd_941341] using wordTrace_append hprefix tailTrace_941341
  have hstable : (prefixWord ++ tailWord_941341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941341).length < 2 ^ (prefixWord ++ tailWord_941341).sum := by decide
  have hdescent : baseEnd_941341 < baseStart_941341 := by decide
  rcases family_descends (prefixWord ++ tailWord_941341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941405 : List Nat := [1, 4, 5, 1, 1, 1, 1, 8]
def baseStart_941405 : Nat := 118140960795 + 941405 * 2 ^ 59
def prefixEnd_941405 : Nat := 4983230072969 + 3 ^ 40 * 941405 * 2
def baseEnd_941405 : Nat := 35806907818221813504301

theorem tailTrace_941405 : CollatzResearch.WordTrace tailWord_941405 prefixEnd_941405 35806907818221813504301 := by
  unfold tailWord_941405
  simp only [CollatzResearch.WordTrace]
  refine ⟨34335861154457939018825669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22890574102971959345883779 34335861154457939018825669)
  ·
    refine ⟨6437973966460863566029813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34335861154457939018825669 6437973966460863566029813)
    ·
      refine ⟨603560059355705959315295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6437973966460863566029813 603560059355705959315295)
      ·
        refine ⟨905340089033558938972943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603560059355705959315295 905340089033558938972943)
        ·
          refine ⟨1358010133550338408459415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905340089033558938972943 1358010133550338408459415)
          ·
            refine ⟨2037015200325507612689123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358010133550338408459415 2037015200325507612689123)
            ·
              refine ⟨3055522800488261419033685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037015200325507612689123 3055522800488261419033685)
              ·
                refine ⟨35806907818221813504301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3055522800488261419033685 35806907818221813504301)
                ·
                  rfl

theorem cell22_941405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 8].length) (baseStart_941405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941405 prefixEnd_941405 := by exact prefixLift 941405
  have htrace : WordTrace (prefixWord ++ tailWord_941405) baseStart_941405 baseEnd_941405 := by
    simpa [prefixWord, tailWord_941405, baseEnd_941405] using wordTrace_append hprefix tailTrace_941405
  have hstable : (prefixWord ++ tailWord_941405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941405).length < 2 ^ (prefixWord ++ tailWord_941405).sum := by decide
  have hdescent : baseEnd_941405 < baseStart_941405 := by decide
  rcases family_descends (prefixWord ++ tailWord_941405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941420 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_941420 : Nat := 118140960795 + 941420 * 2 ^ 59
def prefixEnd_941420 : Nat := 4983230072969 + 3 ^ 40 * 941420 * 2
def baseEnd_941420 : Nat := 322267305170541282413663

theorem tailTrace_941420 : CollatzResearch.WordTrace tailWord_941420 prefixEnd_941420 322267305170541282413663 := by
  unfold tailWord_941420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17168204124701798290310857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22890938832935731053747809 17168204124701798290310857)
  ·
    refine ⟨12876153093526348717733143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17168204124701798290310857 12876153093526348717733143)
    ·
      refine ⟨19314229640289523076599715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12876153093526348717733143 19314229640289523076599715)
      ·
        refine ⟨28971344460434284614899573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19314229640289523076599715 28971344460434284614899573)
        ·
          refine ⟨2716063543165714182646835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28971344460434284614899573 2716063543165714182646835)
          ·
            refine ⟨4074095314748571273970253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716063543165714182646835 4074095314748571273970253)
            ·
              refine ⟨1527785743030714227738845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4074095314748571273970253 1527785743030714227738845)
              ·
                refine ⟨572919653636517835402067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1527785743030714227738845 572919653636517835402067)
                ·
                  refine ⟨859379480454776753103101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572919653636517835402067 859379480454776753103101)
                  ·
                    refine ⟨322267305170541282413663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859379480454776753103101 322267305170541282413663)
                    ·
                      rfl

theorem cell22_941420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_941420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941420 prefixEnd_941420 := by exact prefixLift 941420
  have htrace : WordTrace (prefixWord ++ tailWord_941420) baseStart_941420 baseEnd_941420 := by
    simpa [prefixWord, tailWord_941420, baseEnd_941420] using wordTrace_append hprefix tailTrace_941420
  have hstable : (prefixWord ++ tailWord_941420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941420).length < 2 ^ (prefixWord ++ tailWord_941420).sum := by decide
  have hdescent : baseEnd_941420 < baseStart_941420 := by decide
  rcases family_descends (prefixWord ++ tailWord_941420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941459 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_941459 : Nat := 118140960795 + 941459 * 2 ^ 59
def prefixEnd_941459 : Nat := 4983230072969 + 3 ^ 40 * 941459 * 2
def baseEnd_941459 : Nat := 322280655667558180688543

theorem tailTrace_941459 : CollatzResearch.WordTrace tailWord_941459 prefixEnd_941459 322280655667558180688543 := by
  unfold tailWord_941459
  simp only [CollatzResearch.WordTrace]
  refine ⟨34337830696262306241291431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22891887130841537494194287 34337830696262306241291431)
  ·
    refine ⟨51506746044393459361937147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34337830696262306241291431 51506746044393459361937147)
    ·
      refine ⟨77260119066590189042905721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51506746044393459361937147 77260119066590189042905721)
      ·
        refine ⟨57945089299942641782179291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77260119066590189042905721 57945089299942641782179291)
        ·
          refine ⟨86917633949913962673268937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57945089299942641782179291 86917633949913962673268937)
          ·
            refine ⟨65188225462435472004951703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86917633949913962673268937 65188225462435472004951703)
            ·
              refine ⟨97782338193653208007427555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65188225462435472004951703 97782338193653208007427555)
              ·
                refine ⟨146673507290479812011141333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97782338193653208007427555 146673507290479812011141333)
                ·
                  refine ⟨3437660327120620594011125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 146673507290479812011141333 3437660327120620594011125)
                  ·
                    refine ⟨322280655667558180688543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3437660327120620594011125 322280655667558180688543)
                    ·
                      rfl

theorem cell22_941459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_941459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941459 prefixEnd_941459 := by exact prefixLift 941459
  have htrace : WordTrace (prefixWord ++ tailWord_941459) baseStart_941459 baseEnd_941459 := by
    simpa [prefixWord, tailWord_941459, baseEnd_941459] using wordTrace_append hprefix tailTrace_941459
  have hstable : (prefixWord ++ tailWord_941459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941459).length < 2 ^ (prefixWord ++ tailWord_941459).sum := by decide
  have hdescent : baseEnd_941459 < baseStart_941459 := by decide
  rcases family_descends (prefixWord ++ tailWord_941459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941660 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_941660 : Nat := 118140960795 + 941660 * 2 ^ 59
def prefixEnd_941660 : Nat := 4983230072969 + 3 ^ 40 * 941660 * 2
def baseEnd_941660 : Nat := 322349462075260656412927

theorem tailTrace_941660 : CollatzResearch.WordTrace tailWord_941660 prefixEnd_941660 322349462075260656412927 := by
  unfold tailWord_941660
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172580884267058784679217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22896774512356078379572289 17172580884267058784679217)
  ·
    refine ⟨12879435663200294088509413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17172580884267058784679217 12879435663200294088509413)
    ·
      refine ⟨2414894186850055141595515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12879435663200294088509413 2414894186850055141595515)
      ·
        refine ⟨3622341280275082712393273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414894186850055141595515 3622341280275082712393273)
        ·
          refine ⟨2716755960206312034294955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3622341280275082712393273 2716755960206312034294955)
          ·
            refine ⟨4075133940309468051442433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716755960206312034294955 4075133940309468051442433)
            ·
              refine ⟨3056350455232101038581825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075133940309468051442433 3056350455232101038581825)
              ·
                refine ⟨2292262841424075778936369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056350455232101038581825 2292262841424075778936369)
                ·
                  refine ⟨1719197131068056834202277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292262841424075778936369 1719197131068056834202277)
                  ·
                    refine ⟨322349462075260656412927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1719197131068056834202277 322349462075260656412927)
                    ·
                      rfl

theorem cell22_941660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_941660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941660 prefixEnd_941660 := by exact prefixLift 941660
  have htrace : WordTrace (prefixWord ++ tailWord_941660) baseStart_941660 baseEnd_941660 := by
    simpa [prefixWord, tailWord_941660, baseEnd_941660] using wordTrace_append hprefix tailTrace_941660
  have hstable : (prefixWord ++ tailWord_941660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941660).length < 2 ^ (prefixWord ++ tailWord_941660).sum := by decide
  have hdescent : baseEnd_941660 < baseStart_941660 := by decide
  rcases family_descends (prefixWord ++ tailWord_941660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941707 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 1, 3]
def baseStart_941707 : Nat := 118140960795 + 941707 * 2 ^ 59
def prefixEnd_941707 : Nat := 4983230072969 + 3 ^ 40 * 941707 * 2
def baseEnd_941707 : Nat := 322365551135768200487783

theorem tailTrace_941707 : CollatzResearch.WordTrace tailWord_941707 prefixEnd_941707 322365551135768200487783 := by
  unfold tailWord_941707
  simp only [CollatzResearch.WordTrace]
  refine ⟨34346875999363844596319375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22897917332909229730879583 34346875999363844596319375)
  ·
    refine ⟨51520313999045766894479063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34346875999363844596319375 51520313999045766894479063)
    ·
      refine ⟨77280470998568650341718595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51520313999045766894479063 77280470998568650341718595)
      ·
        refine ⟨115920706497852975512577893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77280470998568650341718595 115920706497852975512577893)
        ·
          refine ⟨21735132468347432908608355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115920706497852975512577893 21735132468347432908608355)
          ·
            refine ⟨32602698702521149362912533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21735132468347432908608355 32602698702521149362912533)
            ·
              refine ⟨1528251501680678876386525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32602698702521149362912533 1528251501680678876386525)
              ·
                refine ⟨573094313130254578644947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1528251501680678876386525 573094313130254578644947)
                ·
                  refine ⟨859641469695381867967421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573094313130254578644947 859641469695381867967421)
                  ·
                    refine ⟨322365551135768200487783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859641469695381867967421 322365551135768200487783)
                    ·
                      rfl

theorem cell22_941707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 3].length) (baseStart_941707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941707 prefixEnd_941707 := by exact prefixLift 941707
  have htrace : WordTrace (prefixWord ++ tailWord_941707) baseStart_941707 baseEnd_941707 := by
    simpa [prefixWord, tailWord_941707, baseEnd_941707] using wordTrace_append hprefix tailTrace_941707
  have hstable : (prefixWord ++ tailWord_941707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941707).length < 2 ^ (prefixWord ++ tailWord_941707).sum := by decide
  have hdescent : baseEnd_941707 < baseStart_941707 := by decide
  rcases family_descends (prefixWord ++ tailWord_941707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941720 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_941720 : Nat := 118140960795 + 941720 * 2 ^ 59
def prefixEnd_941720 : Nat := 4983230072969 + 3 ^ 40 * 941720 * 2
def baseEnd_941720 : Nat := 107456667100480166637581

theorem tailTrace_941720 : CollatzResearch.WordTrace tailWord_941720 prefixEnd_941720 107456667100480166637581 := by
  unfold tailWord_941720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173675074158373908271307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22898233432211165211028409 17173675074158373908271307)
  ·
    refine ⟨25760512611237560862406961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17173675074158373908271307 25760512611237560862406961)
    ·
      refine ⟨19320384458428170646805221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25760512611237560862406961 19320384458428170646805221)
      ·
        refine ⟨3622572085955281996275979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19320384458428170646805221 3622572085955281996275979)
        ·
          refine ⟨5433858128932922994413969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622572085955281996275979 5433858128932922994413969)
          ·
            refine ⟨4075393596699692245810477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433858128932922994413969 4075393596699692245810477)
            ·
              refine ⟨1528272598762384592178929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4075393596699692245810477 1528272598762384592178929)
              ·
                refine ⟨1146204449071788444134197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528272598762384592178929 1146204449071788444134197)
                ·
                  refine ⟨107456667100480166637581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1146204449071788444134197 107456667100480166637581)
                  ·
                    rfl

theorem cell22_941720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_941720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941720 prefixEnd_941720 := by exact prefixLift 941720
  have htrace : WordTrace (prefixWord ++ tailWord_941720) baseStart_941720 baseEnd_941720 := by
    simpa [prefixWord, tailWord_941720, baseEnd_941720] using wordTrace_append hprefix tailTrace_941720
  have hstable : (prefixWord ++ tailWord_941720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941720).length < 2 ^ (prefixWord ++ tailWord_941720).sum := by decide
  have hdescent : baseEnd_941720 < baseStart_941720 := by decide
  rcases family_descends (prefixWord ++ tailWord_941720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941733 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_941733 : Nat := 118140960795 + 941733 * 2 ^ 59
def prefixEnd_941733 : Nat := 4983230072969 + 3 ^ 40 * 941733 * 2
def baseEnd_941733 : Nat := 322374451467112799337703

theorem tailTrace_941733 : CollatzResearch.WordTrace tailWord_941733 prefixEnd_941733 322374451467112799337703 := by
  unfold tailWord_941733
  simp only [CollatzResearch.WordTrace]
  refine ⟨34347824297269651036765853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22898549531513100691177235 34347824297269651036765853)
  ·
    refine ⟨12880434111476119138787195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34347824297269651036765853 12880434111476119138787195)
    ·
      refine ⟨19320651167214178708180793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12880434111476119138787195 19320651167214178708180793)
      ·
        refine ⟨14490488375410634031135595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19320651167214178708180793 14490488375410634031135595)
        ·
          refine ⟨21735732563115951046703393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14490488375410634031135595 21735732563115951046703393)
          ·
            refine ⟨16301799422336963285027545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21735732563115951046703393 16301799422336963285027545)
            ·
              refine ⟨12226349566752722463770659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16301799422336963285027545 12226349566752722463770659)
              ·
                refine ⟨18339524350129083695655989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12226349566752722463770659 18339524350129083695655989)
                ·
                  refine ⟨1719330407824601596467749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18339524350129083695655989 1719330407824601596467749)
                  ·
                    refine ⟨322374451467112799337703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1719330407824601596467749 322374451467112799337703)
                    ·
                      rfl

theorem cell22_941733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_941733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941733 prefixEnd_941733 := by exact prefixLift 941733
  have htrace : WordTrace (prefixWord ++ tailWord_941733) baseStart_941733 baseEnd_941733 := by
    simpa [prefixWord, tailWord_941733, baseEnd_941733] using wordTrace_append hprefix tailTrace_941733
  have hstable : (prefixWord ++ tailWord_941733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941733).length < 2 ^ (prefixWord ++ tailWord_941733).sum := by decide
  have hdescent : baseEnd_941733 < baseStart_941733 := by decide
  rcases family_descends (prefixWord ++ tailWord_941733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941797 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_941797 : Nat := 118140960795 + 941797 * 2 ^ 59
def prefixEnd_941797 : Nat := 4983230072969 + 3 ^ 40 * 941797 * 2
def baseEnd_941797 : Nat := 322396359975037965737507

theorem tailTrace_941797 : CollatzResearch.WordTrace tailWord_941797 prefixEnd_941797 322396359975037965737507 := by
  unfold tailWord_941797
  simp only [CollatzResearch.WordTrace]
  refine ⟨34350158569037789967095645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22900105712691859978063763 34350158569037789967095645)
  ·
    refine ⟨12881309463389171237660867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34350158569037789967095645 12881309463389171237660867)
    ·
      refine ⟨19321964195083756856491301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12881309463389171237660867 19321964195083756856491301)
      ·
        refine ⟨3622868286578204410592119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19321964195083756856491301 3622868286578204410592119)
        ·
          refine ⟨5434302429867306615888179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622868286578204410592119 5434302429867306615888179)
          ·
            refine ⟨8151453644800959923832269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434302429867306615888179 8151453644800959923832269)
            ·
              refine ⟨3056795116800359971437101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8151453644800959923832269 3056795116800359971437101)
              ·
                refine ⟨1146298168800134989288913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3056795116800359971437101 1146298168800134989288913)
                ·
                  refine ⟨859723626600101241966685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1146298168800134989288913 859723626600101241966685)
                  ·
                    refine ⟨322396359975037965737507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859723626600101241966685 322396359975037965737507)
                    ·
                      rfl

theorem cell22_941797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_941797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941797 prefixEnd_941797 := by exact prefixLift 941797
  have htrace : WordTrace (prefixWord ++ tailWord_941797) baseStart_941797 baseEnd_941797 := by
    simpa [prefixWord, tailWord_941797, baseEnd_941797] using wordTrace_append hprefix tailTrace_941797
  have hstable : (prefixWord ++ tailWord_941797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941797).length < 2 ^ (prefixWord ++ tailWord_941797).sum := by decide
  have hdescent : baseEnd_941797 < baseStart_941797 := by decide
  rcases family_descends (prefixWord ++ tailWord_941797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941855 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 5]
def baseStart_941855 : Nat := 118140960795 + 941855 * 2 ^ 59
def prefixEnd_941855 : Nat := 4983230072969 + 3 ^ 40 * 941855 * 2
def baseEnd_941855 : Nat := 107472071520115049262443

theorem tailTrace_941855 : CollatzResearch.WordTrace tailWord_941855 prefixEnd_941855 107472071520115049262443 := by
  unfold tailWord_941855
  simp only [CollatzResearch.WordTrace]
  refine ⟨34352274002827665872707019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22901516001885110581804679 34352274002827665872707019)
  ·
    refine ⟨51528411004241498809060529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34352274002827665872707019 51528411004241498809060529)
    ·
      refine ⟨38646308253181124106795397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51528411004241498809060529 38646308253181124106795397)
      ·
        refine ⟨7246182797471460770024137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38646308253181124106795397 7246182797471460770024137)
        ·
          refine ⟨5434637098103595577518103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7246182797471460770024137 5434637098103595577518103)
          ·
            refine ⟨8151955647155393366277155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434637098103595577518103 8151955647155393366277155)
            ·
              refine ⟨12227933470733090049415733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151955647155393366277155 12227933470733090049415733)
              ·
                refine ⟨1146368762881227192132725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12227933470733090049415733 1146368762881227192132725)
                ·
                  refine ⟨107472071520115049262443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1146368762881227192132725 107472071520115049262443)
                  ·
                    rfl

theorem cell22_941855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 5].length) (baseStart_941855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941855 prefixEnd_941855 := by exact prefixLift 941855
  have htrace : WordTrace (prefixWord ++ tailWord_941855) baseStart_941855 baseEnd_941855 := by
    simpa [prefixWord, tailWord_941855, baseEnd_941855] using wordTrace_append hprefix tailTrace_941855
  have hstable : (prefixWord ++ tailWord_941855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941855).length < 2 ^ (prefixWord ++ tailWord_941855).sum := by decide
  have hdescent : baseEnd_941855 < baseStart_941855 := by decide
  rcases family_descends (prefixWord ++ tailWord_941855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941876 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_941876 : Nat := 118140960795 + 941876 * 2 ^ 59
def prefixEnd_941876 : Nat := 4983230072969 + 3 ^ 40 * 941876 * 2
def baseEnd_941876 : Nat := 322423403289508093012265

theorem tailTrace_941876 : CollatzResearch.WordTrace tailWord_941876 prefixEnd_941876 322423403289508093012265 := by
  unfold tailWord_941876
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176519967875793229610741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22902026623834390972814321 17176519967875793229610741)
  ·
    refine ⟨1610298746988355615276007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17176519967875793229610741 1610298746988355615276007)
    ·
      refine ⟨2415448120482533422914011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610298746988355615276007 2415448120482533422914011)
      ·
        refine ⟨3623172180723800134371017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415448120482533422914011 3623172180723800134371017)
        ·
          refine ⟨2717379135542850100778263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623172180723800134371017 2717379135542850100778263)
          ·
            refine ⟨4076068703314275151167395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717379135542850100778263 4076068703314275151167395)
            ·
              refine ⟨6114103054971412726751093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076068703314275151167395 6114103054971412726751093)
              ·
                refine ⟨573197161403569943132915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6114103054971412726751093 573197161403569943132915)
                ·
                  refine ⟨859795742105354914699373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573197161403569943132915 859795742105354914699373)
                  ·
                    refine ⟨322423403289508093012265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859795742105354914699373 322423403289508093012265)
                    ·
                      rfl

theorem cell22_941876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_941876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941876 prefixEnd_941876 := by exact prefixLift 941876
  have htrace : WordTrace (prefixWord ++ tailWord_941876) baseStart_941876 baseEnd_941876 := by
    simpa [prefixWord, tailWord_941876, baseEnd_941876] using wordTrace_append hprefix tailTrace_941876
  have hstable : (prefixWord ++ tailWord_941876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941876).length < 2 ^ (prefixWord ++ tailWord_941876).sum := by decide
  have hdescent : baseEnd_941876 < baseStart_941876 := by decide
  rcases family_descends (prefixWord ++ tailWord_941876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941932 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_941932 : Nat := 118140960795 + 941932 * 2 ^ 59
def prefixEnd_941932 : Nat := 4983230072969 + 3 ^ 40 * 941932 * 2
def baseEnd_941932 : Nat := 322442573233942613612093

theorem tailTrace_941932 : CollatzResearch.WordTrace tailWord_941932 prefixEnd_941932 322442573233942613612093 := by
  unfold tailWord_941932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177541211774354011630025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22903388282365805348840033 17177541211774354011630025)
  ·
    refine ⟨12883155908830765508722519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17177541211774354011630025 12883155908830765508722519)
    ·
      refine ⟨19324733863246148263083779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12883155908830765508722519 19324733863246148263083779)
      ·
        refine ⟨28987100794869222394625669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19324733863246148263083779 28987100794869222394625669)
        ·
          refine ⟨5435081399037979198992313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28987100794869222394625669 5435081399037979198992313)
          ·
            refine ⟨4076311049278484399244235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435081399037979198992313 4076311049278484399244235)
            ·
              refine ⟨6114466573917726598866353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076311049278484399244235 6114466573917726598866353)
              ·
                refine ⟨4585849930438294949149765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6114466573917726598866353 4585849930438294949149765)
                ·
                  refine ⟨859846861957180302965581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4585849930438294949149765 859846861957180302965581)
                  ·
                    refine ⟨322442573233942613612093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859846861957180302965581 322442573233942613612093)
                    ·
                      rfl

theorem cell22_941932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_941932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941932 prefixEnd_941932 := by exact prefixLift 941932
  have htrace : WordTrace (prefixWord ++ tailWord_941932) baseStart_941932 baseEnd_941932 := by
    simpa [prefixWord, tailWord_941932, baseEnd_941932] using wordTrace_append hprefix tailTrace_941932
  have hstable : (prefixWord ++ tailWord_941932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941932).length < 2 ^ (prefixWord ++ tailWord_941932).sum := by decide
  have hdescent : baseEnd_941932 < baseStart_941932 := by decide
  rcases family_descends (prefixWord ++ tailWord_941932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941977 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_941977 : Nat := 118140960795 + 941977 * 2 ^ 59
def prefixEnd_941977 : Nat := 4983230072969 + 3 ^ 40 * 941977 * 2
def baseEnd_941977 : Nat := 322457977653577496236955

theorem tailTrace_941977 : CollatzResearch.WordTrace tailWord_941977 prefixEnd_941977 322457977653577496236955 := by
  unfold tailWord_941977
  simp only [CollatzResearch.WordTrace]
  refine ⟨34356723708385680708648185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22904482472257120472432123 34356723708385680708648185)
  ·
    refine ⟨25767542781289260531486139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34356723708385680708648185 25767542781289260531486139)
    ·
      refine ⟨38651314171933890797229209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25767542781289260531486139 38651314171933890797229209)
      ·
        refine ⟨28988485628950418097921907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38651314171933890797229209 28988485628950418097921907)
        ·
          refine ⟨43482728443425627146882861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28988485628950418097921907 43482728443425627146882861)
          ·
            refine ⟨16306023166284610180081073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43482728443425627146882861 16306023166284610180081073)
            ·
              refine ⟨12229517374713457635060805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306023166284610180081073 12229517374713457635060805)
              ·
                refine ⟨2293034507758773306573901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12229517374713457635060805 2293034507758773306573901)
                ·
                  refine ⟨859887940409539989965213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2293034507758773306573901 859887940409539989965213)
                  ·
                    refine ⟨322457977653577496236955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 859887940409539989965213 322457977653577496236955)
                    ·
                      rfl

theorem cell22_941977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_941977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_941977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_941977 prefixEnd_941977 := by exact prefixLift 941977
  have htrace : WordTrace (prefixWord ++ tailWord_941977) baseStart_941977 baseEnd_941977 := by
    simpa [prefixWord, tailWord_941977, baseEnd_941977] using wordTrace_append hprefix tailTrace_941977
  have hstable : (prefixWord ++ tailWord_941977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941977).length < 2 ^ (prefixWord ++ tailWord_941977).sum := by decide
  have hdescent : baseEnd_941977 < baseStart_941977 := by decide
  rcases family_descends (prefixWord ++ tailWord_941977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942103 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 4]
def baseStart_942103 : Nat := 118140960795 + 942103 * 2 ^ 59
def prefixEnd_942103 : Nat := 4983230072969 + 3 ^ 40 * 942103 * 2
def baseEnd_942103 : Nat := 107500370009518389195523

theorem tailTrace_942103 : CollatzResearch.WordTrace tailWord_942103 prefixEnd_942103 107500370009518389195523 := by
  unfold tailWord_942103
  simp only [CollatzResearch.WordTrace]
  refine ⟨34361319305929204227734963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22907546203952802818489975 34361319305929204227734963)
  ·
    refine ⟨51541978958893806341602445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34361319305929204227734963 51541978958893806341602445)
    ·
      refine ⟨19328242109585177378100917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51541978958893806341602445 19328242109585177378100917)
      ·
        refine ⟨1812022697773610379196961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19328242109585177378100917 1812022697773610379196961)
        ·
          refine ⟨1359017023330207784397721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812022697773610379196961 1359017023330207784397721)
          ·
            refine ⟨1019262767497655838298291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359017023330207784397721 1019262767497655838298291)
            ·
              refine ⟨1528894151246483757447437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019262767497655838298291 1528894151246483757447437)
              ·
                refine ⟨573335306717431409042789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1528894151246483757447437 573335306717431409042789)
                ·
                  refine ⟨107500370009518389195523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573335306717431409042789 107500370009518389195523)
                  ·
                    rfl

theorem cell22_942103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 4].length) (baseStart_942103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942103 prefixEnd_942103 := by exact prefixLift 942103
  have htrace : WordTrace (prefixWord ++ tailWord_942103) baseStart_942103 baseEnd_942103 := by
    simpa [prefixWord, tailWord_942103, baseEnd_942103] using wordTrace_append hprefix tailTrace_942103
  have hstable : (prefixWord ++ tailWord_942103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942103).length < 2 ^ (prefixWord ++ tailWord_942103).sum := by decide
  have hdescent : baseEnd_942103 < baseStart_942103 := by decide
  rcases family_descends (prefixWord ++ tailWord_942103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942116 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_942116 : Nat := 118140960795 + 942116 * 2 ^ 59
def prefixEnd_942116 : Nat := 4983230072969 + 3 ^ 40 * 942116 * 2
def baseEnd_942116 : Nat := 322505560194227467011529

theorem tailTrace_942116 : CollatzResearch.WordTrace tailWord_942116 prefixEnd_942116 322505560194227467011529 := by
  unfold tailWord_942116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17180896727441053723979101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22907862303254738298638801 17180896727441053723979101)
  ·
    refine ⟨6442836272790395146492163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17180896727441053723979101 6442836272790395146492163)
    ·
      refine ⟨9664254409185592719738245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442836272790395146492163 9664254409185592719738245)
      ·
        refine ⟨1812047701722298634950921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9664254409185592719738245 1812047701722298634950921)
        ·
          refine ⟨1359035776291723976213191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812047701722298634950921 1359035776291723976213191)
          ·
            refine ⟨2038553664437585964319787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359035776291723976213191 2038553664437585964319787)
            ·
              refine ⟨3057830496656378946479681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038553664437585964319787 3057830496656378946479681)
              ·
                refine ⟨2293372872492284209859761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057830496656378946479681 2293372872492284209859761)
                ·
                  refine ⟨1720029654369213157394821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2293372872492284209859761 1720029654369213157394821)
                  ·
                    refine ⟨322505560194227467011529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1720029654369213157394821 322505560194227467011529)
                    ·
                      rfl

theorem cell22_942116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_942116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942116 prefixEnd_942116 := by exact prefixLift 942116
  have htrace : WordTrace (prefixWord ++ tailWord_942116) baseStart_942116 baseEnd_942116 := by
    simpa [prefixWord, tailWord_942116, baseEnd_942116] using wordTrace_append hprefix tailTrace_942116
  have hstable : (prefixWord ++ tailWord_942116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942116).length < 2 ^ (prefixWord ++ tailWord_942116).sum := by decide
  have hdescent : baseEnd_942116 < baseStart_942116 := by decide
  rcases family_descends (prefixWord ++ tailWord_942116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942120 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 4]
def baseStart_942120 : Nat := 118140960795 + 942120 * 2 ^ 59
def prefixEnd_942120 : Nat := 4983230072969 + 3 ^ 40 * 942120 * 2
def baseEnd_942120 : Nat := 107502309825324263303839

theorem tailTrace_942120 : CollatzResearch.WordTrace tailWord_942120 prefixEnd_942120 107502309825324263303839 := by
  unfold tailWord_942120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17180969673433808065551907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22907959564578410754069209 17180969673433808065551907)
  ·
    refine ⟨25771454510150712098327861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17180969673433808065551907 25771454510150712098327861)
    ·
      refine ⟨2416073860326629259218237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25771454510150712098327861 2416073860326629259218237)
      ·
        refine ⟨906027697622485972206839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2416073860326629259218237 906027697622485972206839)
        ·
          refine ⟨1359041546433728958310259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906027697622485972206839 1359041546433728958310259)
          ·
            refine ⟨2038562319650593437465389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359041546433728958310259 2038562319650593437465389)
            ·
              refine ⟨764460869868972539049521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2038562319650593437465389 764460869868972539049521)
              ·
                refine ⟨573345652401729404287141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764460869868972539049521 573345652401729404287141)
                ·
                  refine ⟨107502309825324263303839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573345652401729404287141 107502309825324263303839)
                  ·
                    rfl

theorem cell22_942120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_942120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942120 prefixEnd_942120 := by exact prefixLift 942120
  have htrace : WordTrace (prefixWord ++ tailWord_942120) baseStart_942120 baseEnd_942120 := by
    simpa [prefixWord, tailWord_942120, baseEnd_942120] using wordTrace_append hprefix tailTrace_942120
  have hstable : (prefixWord ++ tailWord_942120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942120).length < 2 ^ (prefixWord ++ tailWord_942120).sum := by decide
  have hdescent : baseEnd_942120 < baseStart_942120 := by decide
  rcases family_descends (prefixWord ++ tailWord_942120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942189 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_942189 : Nat := 118140960795 + 942189 * 2 ^ 59
def prefixEnd_942189 : Nat := 4983230072969 + 3 ^ 40 * 942189 * 2
def baseEnd_942189 : Nat := 322530549586079609936305

theorem tailTrace_942189 : CollatzResearch.WordTrace tailWord_942189 prefixEnd_942189 322530549586079609936305 := by
  unfold tailWord_942189
  simp only [CollatzResearch.WordTrace]
  refine ⟨34364455983617640915365621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22909637322411760610243747 34364455983617640915365621)
  ·
    refine ⟨3221667748464153835815527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34364455983617640915365621 3221667748464153835815527)
    ·
      refine ⟨4832501622696230753723291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3221667748464153835815527 4832501622696230753723291)
      ·
        refine ⟨7248752434044346130584937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832501622696230753723291 7248752434044346130584937)
        ·
          refine ⟨5436564325533259597938703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248752434044346130584937 5436564325533259597938703)
          ·
            refine ⟨8154846488299889396908055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436564325533259597938703 8154846488299889396908055)
            ·
              refine ⟨12232269732449834095362083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8154846488299889396908055 12232269732449834095362083)
              ·
                refine ⟨18348404598674751143043125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12232269732449834095362083 18348404598674751143043125)
                ·
                  refine ⟨1720162931125757919660293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18348404598674751143043125 1720162931125757919660293)
                  ·
                    refine ⟨322530549586079609936305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1720162931125757919660293 322530549586079609936305)
                    ·
                      rfl

theorem cell22_942189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_942189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942189 prefixEnd_942189 := by exact prefixLift 942189
  have htrace : WordTrace (prefixWord ++ tailWord_942189) baseStart_942189 baseEnd_942189 := by
    simpa [prefixWord, tailWord_942189, baseEnd_942189] using wordTrace_append hprefix tailTrace_942189
  have hstable : (prefixWord ++ tailWord_942189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942189).length < 2 ^ (prefixWord ++ tailWord_942189).sum := by decide
  have hdescent : baseEnd_942189 < baseStart_942189 := by decide
  rcases family_descends (prefixWord ++ tailWord_942189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942204 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_942204 : Nat := 118140960795 + 942204 * 2 ^ 59
def prefixEnd_942204 : Nat := 4983230072969 + 3 ^ 40 * 942204 * 2
def baseEnd_942204 : Nat := 107511894797541523603753

theorem tailTrace_942204 : CollatzResearch.WordTrace tailWord_942204 prefixEnd_942204 107511894797541523603753 := by
  unfold tailWord_942204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182501539281649238580833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22910002052375532318107777 17182501539281649238580833)
  ·
    refine ⟨12886876154461236928935625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17182501539281649238580833 12886876154461236928935625)
    ·
      refine ⟨9665157115845927696701719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12886876154461236928935625 9665157115845927696701719)
      ·
        refine ⟨14497735673768891545052579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665157115845927696701719 14497735673768891545052579)
        ·
          refine ⟨21746603510653337317578869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14497735673768891545052579 21746603510653337317578869)
          ·
            refine ⟨2038744079123750373523019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21746603510653337317578869 2038744079123750373523019)
            ·
              refine ⟨3058116118685625560284529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038744079123750373523019 3058116118685625560284529)
              ·
                refine ⟨2293587089014219170213397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058116118685625560284529 2293587089014219170213397)
                ·
                  refine ⟨107511894797541523603753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2293587089014219170213397 107511894797541523603753)
                  ·
                    rfl

theorem cell22_942204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_942204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942204 prefixEnd_942204 := by exact prefixLift 942204
  have htrace : WordTrace (prefixWord ++ tailWord_942204) baseStart_942204 baseEnd_942204 := by
    simpa [prefixWord, tailWord_942204, baseEnd_942204] using wordTrace_append hprefix tailTrace_942204
  have hstable : (prefixWord ++ tailWord_942204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942204).length < 2 ^ (prefixWord ++ tailWord_942204).sum := by decide
  have hdescent : baseEnd_942204 < baseStart_942204 := by decide
  rcases family_descends (prefixWord ++ tailWord_942204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942236 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_942236 : Nat := 118140960795 + 942236 * 2 ^ 59
def prefixEnd_942236 : Nat := 4983230072969 + 3 ^ 40 * 942236 * 2
def baseEnd_942236 : Nat := 322546638646587154011161

theorem tailTrace_942236 : CollatzResearch.WordTrace tailWord_942236 prefixEnd_942236 322546638646587154011161 := by
  unfold tailWord_942236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17183085107223683971163281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22910780142964911961551041 17183085107223683971163281)
  ·
    refine ⟨12887313830417762978372461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17183085107223683971163281 12887313830417762978372461)
    ·
      refine ⟨4832742686406661116889673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12887313830417762978372461 4832742686406661116889673)
      ·
        refine ⟨3624557014804995837667255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4832742686406661116889673 3624557014804995837667255)
        ·
          refine ⟨5436835522207493756500883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624557014804995837667255 5436835522207493756500883)
          ·
            refine ⟨8155253283311240634751325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436835522207493756500883 8155253283311240634751325)
            ·
              refine ⟨3058219981241715238031747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8155253283311240634751325 3058219981241715238031747)
              ·
                refine ⟨4587329971862572857047621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058219981241715238031747 4587329971862572857047621)
                ·
                  refine ⟨860124369724232410696429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4587329971862572857047621 860124369724232410696429)
                  ·
                    refine ⟨322546638646587154011161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860124369724232410696429 322546638646587154011161)
                    ·
                      rfl

theorem cell22_942236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_942236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942236 prefixEnd_942236 := by exact prefixLift 942236
  have htrace : WordTrace (prefixWord ++ tailWord_942236) baseStart_942236 baseEnd_942236 := by
    simpa [prefixWord, tailWord_942236, baseEnd_942236] using wordTrace_append hprefix tailTrace_942236
  have hstable : (prefixWord ++ tailWord_942236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942236).length < 2 ^ (prefixWord ++ tailWord_942236).sum := by decide
  have hdescent : baseEnd_942236 < baseStart_942236 := by decide
  rcases family_descends (prefixWord ++ tailWord_942236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942238 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_942238 : Nat := 118140960795 + 942238 * 2 ^ 59
def prefixEnd_942238 : Nat := 4983230072969 + 3 ^ 40 * 942238 * 2
def baseEnd_942238 : Nat := 107515774429153271820385

theorem tailTrace_942238 : CollatzResearch.WordTrace tailWord_942238 prefixEnd_942238 107515774429153271820385 := by
  unfold tailWord_942238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295780395055015285487421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22910828773626748189266245 4295780395055015285487421)
  ·
    refine ⟨1610917648145630732057783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4295780395055015285487421 1610917648145630732057783)
    ·
      refine ⟨2416376472218446098086675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610917648145630732057783 2416376472218446098086675)
      ·
        refine ⟨3624564708327669147130013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416376472218446098086675 3624564708327669147130013)
        ·
          refine ⟨1359211765622875930173755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3624564708327669147130013 1359211765622875930173755)
          ·
            refine ⟨2038817648434313895260633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359211765622875930173755 2038817648434313895260633)
            ·
              refine ⟨1529113236325735421445475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2038817648434313895260633 1529113236325735421445475)
              ·
                refine ⟨2293669854488603132168213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529113236325735421445475 2293669854488603132168213)
                ·
                  refine ⟨107515774429153271820385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2293669854488603132168213 107515774429153271820385)
                  ·
                    rfl

theorem cell22_942238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_942238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942238 prefixEnd_942238 := by exact prefixLift 942238
  have htrace : WordTrace (prefixWord ++ tailWord_942238) baseStart_942238 baseEnd_942238 := by
    simpa [prefixWord, tailWord_942238, baseEnd_942238] using wordTrace_append hprefix tailTrace_942238
  have hstable : (prefixWord ++ tailWord_942238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942238).length < 2 ^ (prefixWord ++ tailWord_942238).sum := by decide
  have hdescent : baseEnd_942238 < baseStart_942238 := by decide
  rcases family_descends (prefixWord ++ tailWord_942238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942253 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_942253 : Nat := 118140960795 + 942253 * 2 ^ 59
def prefixEnd_942253 : Nat := 4983230072969 + 3 ^ 40 * 942253 * 2
def baseEnd_942253 : Nat := 322552458094004776336109

theorem tailTrace_942253 : CollatzResearch.WordTrace tailWord_942253 prefixEnd_942253 322552458094004776336109 := by
  unfold tailWord_942253
  simp only [CollatzResearch.WordTrace]
  refine ⟨34366790255385779845695413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22911193503590519897130275 34366790255385779845695413)
  ·
    refine ⟨3221886586442416860533945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34366790255385779845695413 3221886586442416860533945)
    ·
      refine ⟨2416414939831812645400459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3221886586442416860533945 2416414939831812645400459)
      ·
        refine ⟨3624622409747718968100689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416414939831812645400459 3624622409747718968100689)
        ·
          refine ⟨2718466807310789226075517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624622409747718968100689 2718466807310789226075517)
          ·
            refine ⟨1019425052741545959778319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2718466807310789226075517 1019425052741545959778319)
            ·
              refine ⟨1529137579112318939667479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019425052741545959778319 1529137579112318939667479)
              ·
                refine ⟨2293706368668478409501219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529137579112318939667479 2293706368668478409501219)
                ·
                  refine ⟨3440559553002717614251829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293706368668478409501219 3440559553002717614251829)
                  ·
                    refine ⟨322552458094004776336109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3440559553002717614251829 322552458094004776336109)
                    ·
                      rfl

theorem cell22_942253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_942253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942253 prefixEnd_942253 := by exact prefixLift 942253
  have htrace : WordTrace (prefixWord ++ tailWord_942253) baseStart_942253 baseEnd_942253 := by
    simpa [prefixWord, tailWord_942253, baseEnd_942253] using wordTrace_append hprefix tailTrace_942253
  have hstable : (prefixWord ++ tailWord_942253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942253).length < 2 ^ (prefixWord ++ tailWord_942253).sum := by decide
  have hdescent : baseEnd_942253 < baseStart_942253 := by decide
  rcases family_descends (prefixWord ++ tailWord_942253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942298 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_942298 : Nat := 118140960795 + 942298 * 2 ^ 59
def prefixEnd_942298 : Nat := 4983230072969 + 3 ^ 40 * 942298 * 2
def baseEnd_942298 : Nat := 322567862513639658960971

theorem tailTrace_942298 : CollatzResearch.WordTrace tailWord_942298 prefixEnd_942298 322567862513639658960971 := by
  unfold tailWord_942298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8592107885055688132770887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22912287693481835020722365 8592107885055688132770887)
  ·
    refine ⟨12888161827583532199156331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8592107885055688132770887 12888161827583532199156331)
    ·
      refine ⟨19332242741375298298734497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12888161827583532199156331 19332242741375298298734497)
      ·
        refine ⟨14499182056031473724050873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19332242741375298298734497 14499182056031473724050873)
        ·
          refine ⟨10874386542023605293038155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14499182056031473724050873 10874386542023605293038155)
          ·
            refine ⟨16311579813035407939557233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874386542023605293038155 16311579813035407939557233)
            ·
              refine ⟨12233684859776555954667925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16311579813035407939557233 12233684859776555954667925)
              ·
                refine ⟨573453977802026060375059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12233684859776555954667925 573453977802026060375059)
                ·
                  refine ⟨860180966703039090562589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573453977802026060375059 860180966703039090562589)
                  ·
                    refine ⟨322567862513639658960971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860180966703039090562589 322567862513639658960971)
                    ·
                      rfl

theorem cell22_942298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_942298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942298 prefixEnd_942298 := by exact prefixLift 942298
  have htrace : WordTrace (prefixWord ++ tailWord_942298) baseStart_942298 baseEnd_942298 := by
    simpa [prefixWord, tailWord_942298, baseEnd_942298] using wordTrace_append hprefix tailTrace_942298
  have hstable : (prefixWord ++ tailWord_942298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942298).length < 2 ^ (prefixWord ++ tailWord_942298).sum := by decide
  have hdescent : baseEnd_942298 < baseStart_942298 := by decide
  rcases family_descends (prefixWord ++ tailWord_942298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942371 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 1, 5]
def baseStart_942371 : Nat := 118140960795 + 942371 * 2 ^ 59
def prefixEnd_942371 : Nat := 4983230072969 + 3 ^ 40 * 942371 * 2
def baseEnd_942371 : Nat := 322592851905491801885747

theorem tailTrace_942371 : CollatzResearch.WordTrace tailWord_942371 prefixEnd_942371 322592851905491801885747 := by
  unfold tailWord_942371
  simp only [CollatzResearch.WordTrace]
  refine ⟨34371094068958285998490967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22914062712638857332327311 34371094068958285998490967)
  ·
    refine ⟨51556641103437428997736451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34371094068958285998490967 51556641103437428997736451)
    ·
      refine ⟨77334961655156143496604677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51556641103437428997736451 77334961655156143496604677)
      ·
        refine ⟨14500305310341776905613377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77334961655156143496604677 14500305310341776905613377)
        ·
          refine ⟨10875228982756332679210033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14500305310341776905613377 10875228982756332679210033)
          ·
            refine ⟨8156421737067249509407525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10875228982756332679210033 8156421737067249509407525)
            ·
              refine ⟨1529329075700109283013911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8156421737067249509407525 1529329075700109283013911)
              ·
                refine ⟨2293993613550163924520867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529329075700109283013911 2293993613550163924520867)
                ·
                  refine ⟨3440990420325245886781301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293993613550163924520867 3440990420325245886781301)
                  ·
                    refine ⟨322592851905491801885747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3440990420325245886781301 322592851905491801885747)
                    ·
                      rfl

theorem cell22_942371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 5].length) (baseStart_942371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942371 prefixEnd_942371 := by exact prefixLift 942371
  have htrace : WordTrace (prefixWord ++ tailWord_942371) baseStart_942371 baseEnd_942371 := by
    simpa [prefixWord, tailWord_942371, baseEnd_942371] using wordTrace_append hprefix tailTrace_942371
  have hstable : (prefixWord ++ tailWord_942371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942371).length < 2 ^ (prefixWord ++ tailWord_942371).sum := by decide
  have hdescent : baseEnd_942371 < baseStart_942371 := by decide
  rcases family_descends (prefixWord ++ tailWord_942371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942388 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_942388 : Nat := 118140960795 + 942388 * 2 ^ 59
def prefixEnd_942388 : Nat := 4983230072969 + 3 ^ 40 * 942388 * 2
def baseEnd_942388 : Nat := 322598671352909424210695

theorem tailTrace_942388 : CollatzResearch.WordTrace tailWord_942388 prefixEnd_942388 322598671352909424210695 := by
  unfold tailWord_942388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17185857054948348950929909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22914476073264465267906545 17185857054948348950929909)
  ·
    refine ⟨1611174098901407714149679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17185857054948348950929909 1611174098901407714149679)
    ·
      refine ⟨2416761148352111571224519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611174098901407714149679 2416761148352111571224519)
      ·
        refine ⟨3625141722528167356836779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416761148352111571224519 3625141722528167356836779)
        ·
          refine ⟨5437712583792251035255169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625141722528167356836779 5437712583792251035255169)
          ·
            refine ⟨4078284437844188276441377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5437712583792251035255169 4078284437844188276441377)
            ·
              refine ⟨3058713328383141207331033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4078284437844188276441377 3058713328383141207331033)
              ·
                refine ⟨2294034996287355905498275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058713328383141207331033 2294034996287355905498275)
                ·
                  refine ⟨3441052494431033858247413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294034996287355905498275 3441052494431033858247413)
                  ·
                    refine ⟨322598671352909424210695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3441052494431033858247413 322598671352909424210695)
                    ·
                      rfl

theorem cell22_942388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_942388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942388 prefixEnd_942388 := by exact prefixLift 942388
  have htrace : WordTrace (prefixWord ++ tailWord_942388) baseStart_942388 baseEnd_942388 := by
    simpa [prefixWord, tailWord_942388, baseEnd_942388] using wordTrace_append hprefix tailTrace_942388
  have hstable : (prefixWord ++ tailWord_942388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942388).length < 2 ^ (prefixWord ++ tailWord_942388).sum := by decide
  have hdescent : baseEnd_942388 < baseStart_942388 := by decide
  rcases family_descends (prefixWord ++ tailWord_942388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942467 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 3, 3]
def baseStart_942467 : Nat := 118140960795 + 942467 * 2 ^ 59
def prefixEnd_942467 : Nat := 4983230072969 + 3 ^ 40 * 942467 * 2
def baseEnd_942467 : Nat := 322625714667379551485453

theorem tailTrace_942467 : CollatzResearch.WordTrace tailWord_942467 prefixEnd_942467 322625714667379551485453 := by
  unfold tailWord_942467
  simp only [CollatzResearch.WordTrace]
  refine ⟨34374595476610494393985655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22916396984406996262657103 34374595476610494393985655)
  ·
    refine ⟨51561893214915741590978483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34374595476610494393985655 51561893214915741590978483)
    ·
      refine ⟨77342839822373612386467725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51561893214915741590978483 77342839822373612386467725)
      ·
        refine ⟨29003564933390104644925397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77342839822373612386467725 29003564933390104644925397)
        ·
          refine ⟨679771053126330577615439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29003564933390104644925397 679771053126330577615439)
          ·
            refine ⟨1019656579689495866423159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679771053126330577615439 1019656579689495866423159)
            ·
              refine ⟨1529484869534243799634739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019656579689495866423159 1529484869534243799634739)
              ·
                refine ⟨2294227304301365699452109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529484869534243799634739 2294227304301365699452109)
                ·
                  refine ⟨860335239113012137294541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2294227304301365699452109 860335239113012137294541)
                  ·
                    refine ⟨322625714667379551485453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860335239113012137294541 322625714667379551485453)
                    ·
                      rfl

theorem cell22_942467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 3].length) (baseStart_942467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942467 prefixEnd_942467 := by exact prefixLift 942467
  have htrace : WordTrace (prefixWord ++ tailWord_942467) baseStart_942467 baseEnd_942467 := by
    simpa [prefixWord, tailWord_942467, baseEnd_942467] using wordTrace_append hprefix tailTrace_942467
  have hstable : (prefixWord ++ tailWord_942467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942467).length < 2 ^ (prefixWord ++ tailWord_942467).sum := by decide
  have hdescent : baseEnd_942467 < baseStart_942467 := by decide
  rcases family_descends (prefixWord ++ tailWord_942467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942508 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 4]
def baseStart_942508 : Nat := 118140960795 + 942508 * 2 ^ 59
def prefixEnd_942508 : Nat := 4983230072969 + 3 ^ 40 * 942508 * 2
def baseEnd_942508 : Nat := 107546583268423037070109

theorem tailTrace_942508 : CollatzResearch.WordTrace tailWord_942508 prefixEnd_942508 107546583268423037070109 := by
  unfold tailWord_942508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188045434730979198114089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22917393912974638930818785 17188045434730979198114089)
  ·
    refine ⟨12891034076048234398585567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17188045434730979198114089 12891034076048234398585567)
    ·
      refine ⟨19336551114072351597878351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12891034076048234398585567 19336551114072351597878351)
      ·
        refine ⟨29004826671108527396817527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19336551114072351597878351 29004826671108527396817527)
        ·
          refine ⟨43507240006662791095226291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29004826671108527396817527 43507240006662791095226291)
          ·
            refine ⟨65260860009994186642839437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43507240006662791095226291 65260860009994186642839437)
            ·
              refine ⟨24472822503747819991064789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65260860009994186642839437 24472822503747819991064789)
              ·
                refine ⟨573581777431589531040581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24472822503747819991064789 573581777431589531040581)
                ·
                  refine ⟨107546583268423037070109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573581777431589531040581 107546583268423037070109)
                  ·
                    rfl

theorem cell22_942508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_942508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942508 prefixEnd_942508 := by exact prefixLift 942508
  have htrace : WordTrace (prefixWord ++ tailWord_942508) baseStart_942508 baseEnd_942508 := by
    simpa [prefixWord, tailWord_942508, baseEnd_942508] using wordTrace_append hprefix tailTrace_942508
  have hstable : (prefixWord ++ tailWord_942508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942508).length < 2 ^ (prefixWord ++ tailWord_942508).sum := by decide
  have hdescent : baseEnd_942508 < baseStart_942508 := by decide
  rcases family_descends (prefixWord ++ tailWord_942508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942525 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 4]
def baseStart_942525 : Nat := 118140960795 + 942525 * 2 ^ 59
def prefixEnd_942525 : Nat := 4983230072969 + 3 ^ 40 * 942525 * 2
def baseEnd_942525 : Nat := 107548523084228911178425

theorem tailTrace_942525 : CollatzResearch.WordTrace tailWord_942525 prefixEnd_942525 107548523084228911178425 := by
  unfold tailWord_942525
  simp only [CollatzResearch.WordTrace]
  refine ⟨34376710910400370299597029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22917807273600246866398019 34376710910400370299597029)
  ·
    refine ⟨6445633295700069431174443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34376710910400370299597029 6445633295700069431174443)
    ·
      refine ⟨9668449943550104146761665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445633295700069431174443 9668449943550104146761665)
      ·
        refine ⟨7251337457662578110071249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9668449943550104146761665 7251337457662578110071249)
        ·
          refine ⟨5438503093246933582553437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7251337457662578110071249 5438503093246933582553437)
          ·
            refine ⟨2039438659967600093457539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5438503093246933582553437 2039438659967600093457539)
            ·
              refine ⟨3059157989951400140186309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039438659967600093457539 3059157989951400140186309)
              ·
                refine ⟨573592123115887526284933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3059157989951400140186309 573592123115887526284933)
                ·
                  refine ⟨107548523084228911178425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573592123115887526284933 107548523084228911178425)
                  ·
                    rfl

theorem cell22_942525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_942525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942525 prefixEnd_942525 := by exact prefixLift 942525
  have htrace : WordTrace (prefixWord ++ tailWord_942525) baseStart_942525 baseEnd_942525 := by
    simpa [prefixWord, tailWord_942525, baseEnd_942525] using wordTrace_append hprefix tailTrace_942525
  have hstable : (prefixWord ++ tailWord_942525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942525).length < 2 ^ (prefixWord ++ tailWord_942525).sum := by decide
  have hdescent : baseEnd_942525 < baseStart_942525 := by decide
  rcases family_descends (prefixWord ++ tailWord_942525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942540 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_942540 : Nat := 118140960795 + 942540 * 2 ^ 59
def prefixEnd_942540 : Nat := 4983230072969 + 3 ^ 40 * 942540 * 2
def baseEnd_942540 : Nat := 322650704059231694410229

theorem tailTrace_942540 : CollatzResearch.WordTrace tailWord_942540 prefixEnd_942540 322650704059231694410229 := by
  unfold tailWord_942540
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188629002673013930696537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22918172003564018574262049 17188629002673013930696537)
  ·
    refine ⟨12891471752004760448022403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17188629002673013930696537 12891471752004760448022403)
    ·
      refine ⟨19337207628007140672033605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12891471752004760448022403 19337207628007140672033605)
      ·
        refine ⟨3625726430251338876006301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19337207628007140672033605 3625726430251338876006301)
        ·
          refine ⟨1359647411344252078502363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3625726430251338876006301 1359647411344252078502363)
          ·
            refine ⟨2039471117016378117753545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359647411344252078502363 2039471117016378117753545)
            ·
              refine ⟨1529603337762283588315159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039471117016378117753545 1529603337762283588315159)
              ·
                refine ⟨2294405006643425382472739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529603337762283588315159 2294405006643425382472739)
                ·
                  refine ⟨3441607509965138073709109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294405006643425382472739 3441607509965138073709109)
                  ·
                    refine ⟨322650704059231694410229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3441607509965138073709109 322650704059231694410229)
                    ·
                      rfl

theorem cell22_942540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_942540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942540 prefixEnd_942540 := by exact prefixLift 942540
  have htrace : WordTrace (prefixWord ++ tailWord_942540) baseStart_942540 baseEnd_942540 := by
    simpa [prefixWord, tailWord_942540, baseEnd_942540] using wordTrace_append hprefix tailTrace_942540
  have hstable : (prefixWord ++ tailWord_942540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942540).length < 2 ^ (prefixWord ++ tailWord_942540).sum := by decide
  have hdescent : baseEnd_942540 < baseStart_942540 := by decide
  rcases family_descends (prefixWord ++ tailWord_942540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942553 : List Nat := [1, 2, 1, 2, 4, 1, 5, 6]
def baseStart_942553 : Nat := 118140960795 + 942553 * 2 ^ 59
def prefixEnd_942553 : Nat := 4983230072969 + 3 ^ 40 * 942553 * 2
def baseEnd_942553 : Nat := 35850572691655999315021

theorem tailTrace_942553 : CollatzResearch.WordTrace tailWord_942553 prefixEnd_942553 35850572691655999315021 := by
  unfold tailWord_942553
  simp only [CollatzResearch.WordTrace]
  refine ⟨34377732154298931081616313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22918488102865954054410875 34377732154298931081616313)
  ·
    refine ⟨25783299115724198311212235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34377732154298931081616313 25783299115724198311212235)
    ·
      refine ⟨38674948673586297466818353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25783299115724198311212235 38674948673586297466818353)
      ·
        refine ⟨29006211505189723100113765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38674948673586297466818353 29006211505189723100113765)
        ·
          refine ⟨5438664657223073081271331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29006211505189723100113765 5438664657223073081271331)
          ·
            refine ⟨8157996985834609621906997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438664657223073081271331 8157996985834609621906997)
            ·
              refine ⟨764812217421994652053781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8157996985834609621906997 764812217421994652053781)
              ·
                refine ⟨35850572691655999315021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 764812217421994652053781 35850572691655999315021)
                ·
                  rfl

theorem cell22_942553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 6].length) (baseStart_942553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942553 prefixEnd_942553 := by exact prefixLift 942553
  have htrace : WordTrace (prefixWord ++ tailWord_942553) baseStart_942553 baseEnd_942553 := by
    simpa [prefixWord, tailWord_942553, baseEnd_942553] using wordTrace_append hprefix tailTrace_942553
  have hstable : (prefixWord ++ tailWord_942553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942553).length < 2 ^ (prefixWord ++ tailWord_942553).sum := by decide
  have hdescent : baseEnd_942553 < baseStart_942553 := by decide
  rcases family_descends (prefixWord ++ tailWord_942553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942692 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_942692 : Nat := 118140960795 + 942692 * 2 ^ 59
def prefixEnd_942692 : Nat := 4983230072969 + 3 ^ 40 * 942692 * 2
def baseEnd_942692 : Nat := 322702736765553964609763

theorem tailTrace_942692 : CollatzResearch.WordTrace tailWord_942692 prefixEnd_942692 322702736765553964609763 := by
  unfold tailWord_942692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191400950397678910463165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22921867933863571880617553 17191400950397678910463165)
  ·
    refine ⟨6446775356399129591423687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17191400950397678910463165 6446775356399129591423687)
    ·
      refine ⟨9670163034598694387135531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446775356399129591423687 9670163034598694387135531)
      ·
        refine ⟨14505244551898041580703297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670163034598694387135531 14505244551898041580703297)
        ·
          refine ⟨10878933413923531185527473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14505244551898041580703297 10878933413923531185527473)
          ·
            refine ⟨8159200060442648389145605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878933413923531185527473 8159200060442648389145605)
            ·
              refine ⟨1529850011332996572964801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8159200060442648389145605 1529850011332996572964801)
              ·
                refine ⟨1147387508499747429723601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529850011332996572964801 1147387508499747429723601)
                ·
                  refine ⟨860540631374810572292701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147387508499747429723601 860540631374810572292701)
                  ·
                    refine ⟨322702736765553964609763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860540631374810572292701 322702736765553964609763)
                    ·
                      rfl

theorem cell22_942692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_942692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942692 prefixEnd_942692 := by exact prefixLift 942692
  have htrace : WordTrace (prefixWord ++ tailWord_942692) baseStart_942692 baseEnd_942692 := by
    simpa [prefixWord, tailWord_942692, baseEnd_942692] using wordTrace_append hprefix tailTrace_942692
  have hstable : (prefixWord ++ tailWord_942692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942692).length < 2 ^ (prefixWord ++ tailWord_942692).sum := by decide
  have hdescent : baseEnd_942692 < baseStart_942692 := by decide
  rcases family_descends (prefixWord ++ tailWord_942692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942720 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_942720 : Nat := 118140960795 + 942720 * 2 ^ 59
def prefixEnd_942720 : Nat := 4983230072969 + 3 ^ 40 * 942720 * 2
def baseEnd_942720 : Nat := 322712321737771224909677

theorem tailTrace_942720 : CollatzResearch.WordTrace tailWord_942720 prefixEnd_942720 322712321737771224909677 := by
  unfold tailWord_942720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191911572346959301472807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22922548763129279068630409 17191911572346959301472807)
  ·
    refine ⟨25787867358520438952209211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17191911572346959301472807 25787867358520438952209211)
    ·
      refine ⟨38681801037780658428313817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25787867358520438952209211 38681801037780658428313817)
      ·
        refine ⟨29011350778335493821235363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38681801037780658428313817 29011350778335493821235363)
        ·
          refine ⟨43517026167503240731853045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29011350778335493821235363 43517026167503240731853045)
          ·
            refine ⟨4079721203203428818611223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43517026167503240731853045 4079721203203428818611223)
            ·
              refine ⟨6119581804805143227916835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079721203203428818611223 6119581804805143227916835)
              ·
                refine ⟨9179372707207714841875253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6119581804805143227916835 9179372707207714841875253)
                ·
                  refine ⟨860566191300723266425805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9179372707207714841875253 860566191300723266425805)
                  ·
                    refine ⟨322712321737771224909677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860566191300723266425805 322712321737771224909677)
                    ·
                      rfl

theorem cell22_942720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_942720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942720 prefixEnd_942720 := by exact prefixLift 942720
  have htrace : WordTrace (prefixWord ++ tailWord_942720) baseStart_942720 baseEnd_942720 := by
    simpa [prefixWord, tailWord_942720, baseEnd_942720] using wordTrace_append hprefix tailTrace_942720
  have hstable : (prefixWord ++ tailWord_942720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942720).length < 2 ^ (prefixWord ++ tailWord_942720).sum := by decide
  have hdescent : baseEnd_942720 < baseStart_942720 := by decide
  rcases family_descends (prefixWord ++ tailWord_942720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942767 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 5]
def baseStart_942767 : Nat := 118140960795 + 942767 * 2 ^ 59
def prefixEnd_942767 : Nat := 4983230072969 + 3 ^ 40 * 942767 * 2
def baseEnd_942767 : Nat := 107576136932759589661511

theorem tailTrace_942767 : CollatzResearch.WordTrace tailWord_942767 prefixEnd_942767 107576136932759589661511 := by
  unfold tailWord_942767
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385537375523645629906555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22923691583682430419937703 34385537375523645629906555)
  ·
    refine ⟨51578306063285468444859833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34385537375523645629906555 51578306063285468444859833)
    ·
      refine ⟨38683729547464101333644875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51578306063285468444859833 38683729547464101333644875)
      ·
        refine ⟨58025594321196152000467313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38683729547464101333644875 58025594321196152000467313)
        ·
          refine ⟨43519195740897114000350485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58025594321196152000467313 43519195740897114000350485)
          ·
            refine ⟨2039962300354552218766429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43519195740897114000350485 2039962300354552218766429)
            ·
              refine ⟨764985862632957082037411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2039962300354552218766429 764985862632957082037411)
              ·
                refine ⟨1147478793949435623056117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764985862632957082037411 1147478793949435623056117)
                ·
                  refine ⟨107576136932759589661511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147478793949435623056117 107576136932759589661511)
                  ·
                    rfl

theorem cell22_942767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 5].length) (baseStart_942767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942767 prefixEnd_942767 := by exact prefixLift 942767
  have htrace : WordTrace (prefixWord ++ tailWord_942767) baseStart_942767 baseEnd_942767 := by
    simpa [prefixWord, tailWord_942767, baseEnd_942767] using wordTrace_append hprefix tailTrace_942767
  have hstable : (prefixWord ++ tailWord_942767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942767).length < 2 ^ (prefixWord ++ tailWord_942767).sum := by decide
  have hdescent : baseEnd_942767 < baseStart_942767 := by decide
  rcases family_descends (prefixWord ++ tailWord_942767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942872 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_942872 : Nat := 118140960795 + 942872 * 2 ^ 59
def prefixEnd_942872 : Nat := 4983230072969 + 3 ^ 40 * 942872 * 2
def baseEnd_942872 : Nat := 322764354444093495109211

theorem tailTrace_942872 : CollatzResearch.WordTrace tailWord_942872 prefixEnd_942872 322764354444093495109211 := by
  unfold tailWord_942872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17194683520071624281239435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22926244693428832374985913 17194683520071624281239435)
  ·
    refine ⟨25792025280107436421859153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17194683520071624281239435 25792025280107436421859153)
    ·
      refine ⟨19344018960080577316394365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25792025280107436421859153 19344018960080577316394365)
      ·
        refine ⟨7254007110030216493647887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19344018960080577316394365 7254007110030216493647887)
        ·
          refine ⟨10881010665045324740471831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254007110030216493647887 10881010665045324740471831)
          ·
            refine ⟨16321515997567987110707747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10881010665045324740471831 16321515997567987110707747)
            ·
              refine ⟨24482273996351980666061621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16321515997567987110707747 24482273996351980666061621)
              ·
                refine ⟨2295213187157998187443277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24482273996351980666061621 2295213187157998187443277)
                ·
                  refine ⟨860704945184249320291229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2295213187157998187443277 860704945184249320291229)
                  ·
                    refine ⟨322764354444093495109211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860704945184249320291229 322764354444093495109211)
                    ·
                      rfl

theorem cell22_942872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_942872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942872 prefixEnd_942872 := by exact prefixLift 942872
  have htrace : WordTrace (prefixWord ++ tailWord_942872) baseStart_942872 baseEnd_942872 := by
    simpa [prefixWord, tailWord_942872, baseEnd_942872] using wordTrace_append hprefix tailTrace_942872
  have hstable : (prefixWord ++ tailWord_942872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942872).length < 2 ^ (prefixWord ++ tailWord_942872).sum := by decide
  have hdescent : baseEnd_942872 < baseStart_942872 := by decide
  rcases family_descends (prefixWord ++ tailWord_942872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942893 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_942893 : Nat := 118140960795 + 942893 * 2 ^ 59
def prefixEnd_942893 : Nat := 4983230072969 + 3 ^ 40 * 942893 * 2
def baseEnd_942893 : Nat := 322771543173256440334147

theorem tailTrace_942893 : CollatzResearch.WordTrace tailWord_942893 prefixEnd_942893 322771543173256440334147 := by
  unfold tailWord_942893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34390132973067169148993333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22926755315378112765995555 34390132973067169148993333)
  ·
    refine ⟨3224074966225047107718125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34390132973067169148993333 3224074966225047107718125)
    ·
      refine ⟨1209028112334392665394297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3224074966225047107718125 1209028112334392665394297)
      ·
        refine ⟨906771084250794499045723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1209028112334392665394297 906771084250794499045723)
        ·
          refine ⟨1360156626376191748568585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906771084250794499045723 1360156626376191748568585)
          ·
            refine ⟨1020117469782143811426439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360156626376191748568585 1020117469782143811426439)
            ·
              refine ⟨1530176204673215717139659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020117469782143811426439 1530176204673215717139659)
              ·
                refine ⟨2295264307009823575709489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530176204673215717139659 2295264307009823575709489)
                ·
                  refine ⟨1721448230257367681782117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2295264307009823575709489 1721448230257367681782117)
                  ·
                    refine ⟨322771543173256440334147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1721448230257367681782117 322771543173256440334147)
                    ·
                      rfl

theorem cell22_942893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_942893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942893 prefixEnd_942893 := by exact prefixLift 942893
  have htrace : WordTrace (prefixWord ++ tailWord_942893) baseStart_942893 baseEnd_942893 := by
    simpa [prefixWord, tailWord_942893, baseEnd_942893] using wordTrace_append hprefix tailTrace_942893
  have hstable : (prefixWord ++ tailWord_942893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942893).length < 2 ^ (prefixWord ++ tailWord_942893).sum := by decide
  have hdescent : baseEnd_942893 < baseStart_942893 := by decide
  rcases family_descends (prefixWord ++ tailWord_942893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942947 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 6]
def baseStart_942947 : Nat := 118140960795 + 942947 * 2 ^ 59
def prefixEnd_942947 : Nat := 4983230072969 + 3 ^ 40 * 942947 * 2
def baseEnd_942947 : Nat := 107596676158939433161327

theorem tailTrace_942947 : CollatzResearch.WordTrace tailWord_942947 prefixEnd_942947 107596676158939433161327 := by
  unfold tailWord_942947
  simp only [CollatzResearch.WordTrace]
  refine ⟨34392102514871536371459095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22928068343247690914306063 34392102514871536371459095)
  ·
    refine ⟨51588153772307304557188643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34392102514871536371459095 51588153772307304557188643)
    ·
      refine ⟨77382230658460956835782965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51588153772307304557188643 77382230658460956835782965)
      ·
        refine ⟨7254584124230714703354653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77382230658460956835782965 7254584124230714703354653)
        ·
          refine ⟨2720469046586518013757995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7254584124230714703354653 2720469046586518013757995)
          ·
            refine ⟨4080703569879777020636993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720469046586518013757995 4080703569879777020636993)
            ·
              refine ⟨3060527677409832765477745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4080703569879777020636993 3060527677409832765477745)
              ·
                refine ⟨2295395758057374574108309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060527677409832765477745 2295395758057374574108309)
                ·
                  refine ⟨107596676158939433161327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2295395758057374574108309 107596676158939433161327)
                  ·
                    rfl

theorem cell22_942947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_942947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942947 prefixEnd_942947 := by exact prefixLift 942947
  have htrace : WordTrace (prefixWord ++ tailWord_942947) baseStart_942947 baseEnd_942947 := by
    simpa [prefixWord, tailWord_942947, baseEnd_942947] using wordTrace_append hprefix tailTrace_942947
  have hstable : (prefixWord ++ tailWord_942947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942947).length < 2 ^ (prefixWord ++ tailWord_942947).sum := by decide
  have hdescent : baseEnd_942947 < baseStart_942947 := by decide
  rcases family_descends (prefixWord ++ tailWord_942947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942962 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_942962 : Nat := 118140960795 + 942962 * 2 ^ 59
def prefixEnd_942962 : Nat := 4983230072969 + 3 ^ 40 * 942962 * 2
def baseEnd_942962 : Nat := 322795163283363260358935

theorem tailTrace_942962 : CollatzResearch.WordTrace tailWord_942962 prefixEnd_942962 322795163283363260358935 := by
  unfold tailWord_942962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598162402454298483313785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22928433073211462622170093 8598162402454298483313785)
  ·
    refine ⟨6448621801840723862485339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8598162402454298483313785 6448621801840723862485339)
    ·
      refine ⟨9672932702761085793728009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6448621801840723862485339 9672932702761085793728009)
      ·
        refine ⟨7254699527070814345296007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9672932702761085793728009 7254699527070814345296007)
        ·
          refine ⟨10882049290606221517944011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254699527070814345296007 10882049290606221517944011)
          ·
            refine ⟨16323073935909332276916017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10882049290606221517944011 16323073935909332276916017)
            ·
              refine ⟨12242305451931999207687013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16323073935909332276916017 12242305451931999207687013)
              ·
                refine ⟨2295432272237249851441315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12242305451931999207687013 2295432272237249851441315)
                ·
                  refine ⟨3443148408355874777161973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295432272237249851441315 3443148408355874777161973)
                  ·
                    refine ⟨322795163283363260358935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3443148408355874777161973 322795163283363260358935)
                    ·
                      rfl

theorem cell22_942962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_942962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942962 prefixEnd_942962 := by exact prefixLift 942962
  have htrace : WordTrace (prefixWord ++ tailWord_942962) baseStart_942962 baseEnd_942962 := by
    simpa [prefixWord, tailWord_942962, baseEnd_942962] using wordTrace_append hprefix tailTrace_942962
  have hstable : (prefixWord ++ tailWord_942962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942962).length < 2 ^ (prefixWord ++ tailWord_942962).sum := by decide
  have hdescent : baseEnd_942962 < baseStart_942962 := by decide
  rcases family_descends (prefixWord ++ tailWord_942962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942966 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_942966 : Nat := 118140960795 + 942966 * 2 ^ 59
def prefixEnd_942966 : Nat := 4983230072969 + 3 ^ 40 * 942966 * 2
def baseEnd_942966 : Nat := 322796532565108583258923

theorem tailTrace_942966 : CollatzResearch.WordTrace tailWord_942966 prefixEnd_942966 322796532565108583258923 := by
  unfold tailWord_942966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149549718862668913525047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22928530334535135077600501 2149549718862668913525047)
  ·
    refine ⟨3224324578294003370287571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149549718862668913525047 3224324578294003370287571)
    ·
      refine ⟨4836486867441005055431357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224324578294003370287571 4836486867441005055431357)
      ·
        refine ⟨1813682575290376895786759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4836486867441005055431357 1813682575290376895786759)
        ·
          refine ⟨2720523862935565343680139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813682575290376895786759 2720523862935565343680139)
          ·
            refine ⟨4080785794403348015520209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720523862935565343680139 4080785794403348015520209)
            ·
              refine ⟨3060589345802511011640157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4080785794403348015520209 3060589345802511011640157)
              ·
                refine ⟨1147721004675941629365059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060589345802511011640157 1147721004675941629365059)
                ·
                  refine ⟨1721581507013912444047589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147721004675941629365059 1721581507013912444047589)
                  ·
                    refine ⟨322796532565108583258923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1721581507013912444047589 322796532565108583258923)
                    ·
                      rfl

theorem cell22_942966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_942966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942966 prefixEnd_942966 := by exact prefixLift 942966
  have htrace : WordTrace (prefixWord ++ tailWord_942966) baseStart_942966 baseEnd_942966 := by
    simpa [prefixWord, tailWord_942966, baseEnd_942966] using wordTrace_append hprefix tailTrace_942966
  have hstable : (prefixWord ++ tailWord_942966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942966).length < 2 ^ (prefixWord ++ tailWord_942966).sum := by decide
  have hdescent : baseEnd_942966 < baseStart_942966 := by decide
  rcases family_descends (prefixWord ++ tailWord_942966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942975 : List Nat := [1, 1, 2, 2, 1, 1, 14]
def baseStart_942975 : Nat := 118140960795 + 942975 * 2 ^ 59
def prefixEnd_942975 : Nat := 4983230072969 + 3 ^ 40 * 942975 * 2
def baseEnd_942975 : Nat := 11955541238853168880885

theorem tailTrace_942975 : CollatzResearch.WordTrace tailWord_942975 prefixEnd_942975 11955541238853168880885 := by
  unfold tailWord_942975
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393123758770097153478379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22928749172513398102318919 34393123758770097153478379)
  ·
    refine ⟨51589685638155145730217569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34393123758770097153478379 51589685638155145730217569)
    ·
      refine ⟨38692264228616359297663177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51589685638155145730217569 38692264228616359297663177)
      ·
        refine ⟨29019198171462269473247383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38692264228616359297663177 29019198171462269473247383)
        ·
          refine ⟨43528797257193404209871075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29019198171462269473247383 43528797257193404209871075)
          ·
            refine ⟨65293195885790106314806613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43528797257193404209871075 65293195885790106314806613)
            ·
              refine ⟨11955541238853168880885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 65293195885790106314806613 11955541238853168880885)
              ·
                rfl

theorem cell22_942975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 14].length) (baseStart_942975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942975 prefixEnd_942975 := by exact prefixLift 942975
  have htrace : WordTrace (prefixWord ++ tailWord_942975) baseStart_942975 baseEnd_942975 := by
    simpa [prefixWord, tailWord_942975, baseEnd_942975] using wordTrace_append hprefix tailTrace_942975
  have hstable : (prefixWord ++ tailWord_942975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942975).length < 2 ^ (prefixWord ++ tailWord_942975).sum := by decide
  have hdescent : baseEnd_942975 < baseStart_942975 := by decide
  rcases family_descends (prefixWord ++ tailWord_942975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942979 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 2, 3]
def baseStart_942979 : Nat := 118140960795 + 942979 * 2 ^ 59
def prefixEnd_942979 : Nat := 4983230072969 + 3 ^ 40 * 942979 * 2
def baseEnd_942979 : Nat := 322800982730780882683883

theorem tailTrace_942979 : CollatzResearch.WordTrace tailWord_942979 prefixEnd_942979 322800982730780882683883 := by
  unfold tailWord_942979
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393269650755605836623991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22928846433837070557749327 34393269650755605836623991)
  ·
    refine ⟨51589904476133408754935987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34393269650755605836623991 51589904476133408754935987)
    ·
      refine ⟨77384856714200113132403981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51589904476133408754935987 77384856714200113132403981)
      ·
        refine ⟨29019321267825042424651493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77384856714200113132403981 29019321267825042424651493)
        ·
          refine ⟨5441122737717195454622155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29019321267825042424651493 5441122737717195454622155)
          ·
            refine ⟨8161684106575793181933233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441122737717195454622155 8161684106575793181933233)
            ·
              refine ⟨6121263079931844886449925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8161684106575793181933233 6121263079931844886449925)
              ·
                refine ⟨1147736827487220916209361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6121263079931844886449925 1147736827487220916209361)
                ·
                  refine ⟨860802620615415687157021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147736827487220916209361 860802620615415687157021)
                  ·
                    refine ⟨322800982730780882683883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860802620615415687157021 322800982730780882683883)
                    ·
                      rfl

theorem cell22_942979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 3].length) (baseStart_942979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942979 prefixEnd_942979 := by exact prefixLift 942979
  have htrace : WordTrace (prefixWord ++ tailWord_942979) baseStart_942979 baseEnd_942979 := by
    simpa [prefixWord, tailWord_942979, baseEnd_942979] using wordTrace_append hprefix tailTrace_942979
  have hstable : (prefixWord ++ tailWord_942979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942979).length < 2 ^ (prefixWord ++ tailWord_942979).sum := by decide
  have hdescent : baseEnd_942979 < baseStart_942979 := by decide
  rcases family_descends (prefixWord ++ tailWord_942979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942981 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 4]
def baseStart_942981 : Nat := 118140960795 + 942981 * 2 ^ 59
def prefixEnd_942981 : Nat := 4983230072969 + 3 ^ 40 * 942981 * 2
def baseEnd_942981 : Nat := 107600555790551181377959

theorem tailTrace_942981 : CollatzResearch.WordTrace tailWord_942981 prefixEnd_942981 107600555790551181377959 := by
  unfold tailWord_942981
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393342596748360178196797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22928895064498906785464531 34393342596748360178196797)
  ·
    refine ⟨12897503473780635066823799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34393342596748360178196797 12897503473780635066823799)
    ·
      refine ⟨19346255210670952600235699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12897503473780635066823799 19346255210670952600235699)
      ·
        refine ⟨29019382816006428900353549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19346255210670952600235699 29019382816006428900353549)
        ·
          refine ⟨10882268556002410837632581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29019382816006428900353549 10882268556002410837632581)
          ·
            refine ⟨2040425354250452032056109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10882268556002410837632581 2040425354250452032056109)
            ·
              refine ⟨765159507843919512021041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040425354250452032056109 765159507843919512021041)
              ·
                refine ⟨573869630882939634015781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765159507843919512021041 573869630882939634015781)
                ·
                  refine ⟨107600555790551181377959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573869630882939634015781 107600555790551181377959)
                  ·
                    rfl

theorem cell22_942981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_942981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942981 prefixEnd_942981 := by exact prefixLift 942981
  have htrace : WordTrace (prefixWord ++ tailWord_942981) baseStart_942981 baseEnd_942981 := by
    simpa [prefixWord, tailWord_942981, baseEnd_942981] using wordTrace_append hprefix tailTrace_942981
  have hstable : (prefixWord ++ tailWord_942981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942981).length < 2 ^ (prefixWord ++ tailWord_942981).sum := by decide
  have hdescent : baseEnd_942981 < baseStart_942981 := by decide
  rcases family_descends (prefixWord ++ tailWord_942981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942996 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_942996 : Nat := 118140960795 + 942996 * 2 ^ 59
def prefixEnd_942996 : Nat := 4983230072969 + 3 ^ 40 * 942996 * 2
def baseEnd_942996 : Nat := 322806802178198505008831

theorem tailTrace_942996 : CollatzResearch.WordTrace tailWord_942996 prefixEnd_942996 322806802178198505008831 := by
  unfold tailWord_942996
  simp only [CollatzResearch.WordTrace]
  refine ⟨17196944845847008869996421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22929259794462678493328561 17196944845847008869996421)
  ·
    refine ⟨3224427158596314163124329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17196944845847008869996421 3224427158596314163124329)
    ·
      refine ⟨2418320368947235622343247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3224427158596314163124329 2418320368947235622343247)
      ·
        refine ⟨3627480553420853433514871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418320368947235622343247 3627480553420853433514871)
        ·
          refine ⟨5441220830131280150272307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627480553420853433514871 5441220830131280150272307)
          ·
            refine ⟨8161831245196920225408461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441220830131280150272307 8161831245196920225408461)
            ·
              refine ⟨3060686716948845084528173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8161831245196920225408461 3060686716948845084528173)
              ·
                refine ⟨1147757518855816906698065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060686716948845084528173 1147757518855816906698065)
                ·
                  refine ⟨860818139141862680023549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147757518855816906698065 860818139141862680023549)
                  ·
                    refine ⟨322806802178198505008831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860818139141862680023549 322806802178198505008831)
                    ·
                      rfl

theorem cell22_942996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_942996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_942996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_942996 prefixEnd_942996 := by exact prefixLift 942996
  have htrace : WordTrace (prefixWord ++ tailWord_942996) baseStart_942996 baseEnd_942996 := by
    simpa [prefixWord, tailWord_942996, baseEnd_942996] using wordTrace_append hprefix tailTrace_942996
  have hstable : (prefixWord ++ tailWord_942996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942996).length < 2 ^ (prefixWord ++ tailWord_942996).sum := by decide
  have hdescent : baseEnd_942996 < baseStart_942996 := by decide
  rcases family_descends (prefixWord ++ tailWord_942996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
