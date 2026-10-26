import V185TrunkScan23Chunk1077

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6382162 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6382162 : Nat := 118140960795 + 6382162 * 2 ^ 59
def prefixEnd_6382162 : Nat := 4983230072969 + 3 ^ 40 * 6382162 * 2
def baseEnd_6382162 : Nat := 3277116720860163995523977

theorem tailTrace_6382162 : CollatzResearch.WordTrace tailWord_6382162 prefixEnd_6382162 3277116720860163995523977 := by
  unfold tailWord_6382162
  simp only [CollatzResearch.WordTrace]
  refine ⟨58194142876131133834113185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155184381003016356890968493 58194142876131133834113185)
  ·
    refine ⟨43645607157098350375584889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58194142876131133834113185 43645607157098350375584889)
    ·
      refine ⟨32734205367823762781688667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43645607157098350375584889 32734205367823762781688667)
      ·
        refine ⟨49101308051735644172533001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32734205367823762781688667 49101308051735644172533001)
        ·
          refine ⟨36825981038801733129399751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49101308051735644172533001 36825981038801733129399751)
          ·
            refine ⟨55238971558202599694099627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36825981038801733129399751 55238971558202599694099627)
            ·
              refine ⟨82858457337303899541149441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55238971558202599694099627 82858457337303899541149441)
              ·
                refine ⟨62143843002977924655862081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82858457337303899541149441 62143843002977924655862081)
                ·
                  refine ⟨46607882252233443491896561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62143843002977924655862081 46607882252233443491896561)
                  ·
                    refine ⟨34955911689175082618922421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46607882252233443491896561 34955911689175082618922421)
                    ·
                      refine ⟨3277116720860163995523977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34955911689175082618922421 3277116720860163995523977)
                      ·
                        rfl

theorem cell23_6382162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6382162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382162 prefixEnd_6382162 := by exact prefixLift 6382162
  have htrace : WordTrace (prefixWord ++ tailWord_6382162) baseStart_6382162 baseEnd_6382162 := by
    simpa [prefixWord, tailWord_6382162, baseEnd_6382162] using wordTrace_append hprefix tailTrace_6382162
  have hstable : (prefixWord ++ tailWord_6382162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382162).length < 2 ^ (prefixWord ++ tailWord_6382162).sum := by decide
  have hdescent : baseEnd_6382162 < baseStart_6382162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382259 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 2, 5]
def baseStart_6382259 : Nat := 118140960795 + 6382259 * 2 ^ 59
def prefixEnd_6382259 : Nat := 4983230072969 + 3 ^ 40 * 6382259 * 2
def baseEnd_6382259 : Nat := 1092388842827883372003677

theorem tailTrace_6382259 : CollatzResearch.WordTrace tailWord_6382259 prefixEnd_6382259 1092388842827883372003677 := by
  unfold tailWord_6382259
  simp only [CollatzResearch.WordTrace]
  refine ⟨232780109385173120902733831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155186739590115413935155887 232780109385173120902733831)
  ·
    refine ⟨349170164077759681354100747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232780109385173120902733831 349170164077759681354100747)
    ·
      refine ⟨523755246116639522031151121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349170164077759681354100747 523755246116639522031151121)
      ·
        refine ⟨392816434587479641523363341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523755246116639522031151121 392816434587479641523363341)
        ·
          refine ⟨147306162970304865571261253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392816434587479641523363341 147306162970304865571261253)
          ·
            refine ⟨27619905556932162294611485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147306162970304865571261253 27619905556932162294611485)
            ·
              refine ⟨10357464583849560860479307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27619905556932162294611485 10357464583849560860479307)
              ·
                refine ⟨15536196875774341290718961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10357464583849560860479307 15536196875774341290718961)
                ·
                  refine ⟨11652147656830755968039221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15536196875774341290718961 11652147656830755968039221)
                  ·
                    refine ⟨1092388842827883372003677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11652147656830755968039221 1092388842827883372003677)
                    ·
                      rfl

theorem cell23_6382259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 5].length) (baseStart_6382259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382259 prefixEnd_6382259 := by exact prefixLift 6382259
  have htrace : WordTrace (prefixWord ++ tailWord_6382259) baseStart_6382259 baseEnd_6382259 := by
    simpa [prefixWord, tailWord_6382259, baseEnd_6382259] using wordTrace_append hprefix tailTrace_6382259
  have hstable : (prefixWord ++ tailWord_6382259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382259).length < 2 ^ (prefixWord ++ tailWord_6382259).sum := by decide
  have hdescent : baseEnd_6382259 < baseStart_6382259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382296 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 2, 4, 2]
def baseStart_6382296 : Nat := 118140960795 + 6382296 * 2 ^ 59
def prefixEnd_6382296 : Nat := 4983230072969 + 3 ^ 40 * 6382296 * 2
def baseEnd_6382296 : Nat := 3277185527267866471248361

theorem tailTrace_6382296 : CollatzResearch.WordTrace tailWord_6382296 prefixEnd_6382296 3277185527267866471248361 := by
  unfold tailWord_6382296
  simp only [CollatzResearch.WordTrace]
  refine ⟨116390729443019538110915371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155187639257359384147887161 116390729443019538110915371)
  ·
    refine ⟨174586094164529307166373057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116390729443019538110915371 174586094164529307166373057)
    ·
      refine ⟨130939570623396980374779793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174586094164529307166373057 130939570623396980374779793)
      ·
        refine ⟨98204677967547735281084845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130939570623396980374779793 98204677967547735281084845)
        ·
          refine ⟨36826754237830400730406817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98204677967547735281084845 36826754237830400730406817)
          ·
            refine ⟨27620065678372800547805113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36826754237830400730406817 27620065678372800547805113)
            ·
              refine ⟨20715049258779600410853835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27620065678372800547805113 20715049258779600410853835)
              ·
                refine ⟨31072573888169400616280753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20715049258779600410853835 31072573888169400616280753)
                ·
                  refine ⟨23304430416127050462210565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31072573888169400616280753 23304430416127050462210565)
                  ·
                    refine ⟨4369580703023821961664481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23304430416127050462210565 4369580703023821961664481)
                    ·
                      refine ⟨3277185527267866471248361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369580703023821961664481 3277185527267866471248361)
                      ·
                        rfl

theorem cell23_6382296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_6382296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382296 prefixEnd_6382296 := by exact prefixLift 6382296
  have htrace : WordTrace (prefixWord ++ tailWord_6382296) baseStart_6382296 baseEnd_6382296 := by
    simpa [prefixWord, tailWord_6382296, baseEnd_6382296] using wordTrace_append hprefix tailTrace_6382296
  have hstable : (prefixWord ++ tailWord_6382296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382296).length < 2 ^ (prefixWord ++ tailWord_6382296).sum := by decide
  have hdescent : baseEnd_6382296 < baseStart_6382296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382340 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_6382340 : Nat := 118140960795 + 6382340 * 2 ^ 59
def prefixEnd_6382340 : Nat := 4983230072969 + 3 ^ 40 * 6382340 * 2
def baseEnd_6382340 : Nat := 1092402706805554766366053

theorem tailTrace_6382340 : CollatzResearch.WordTrace tailWord_6382340 prefixEnd_6382340 1092402706805554766366053 := by
  unfold tailWord_6382340
  simp only [CollatzResearch.WordTrace]
  refine ⟨116391531848939835868216237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155188709131919781157621649 116391531848939835868216237)
  ·
    refine ⟨43646824443352438450581089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116391531848939835868216237 43646824443352438450581089)
    ·
      refine ⟨32735118332514328837935817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43646824443352438450581089 32735118332514328837935817)
      ·
        refine ⟨24551338749385746628451863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32735118332514328837935817 24551338749385746628451863)
        ·
          refine ⟨36827008124078619942677795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24551338749385746628451863 36827008124078619942677795)
          ·
            refine ⟨55240512186117929914016693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36827008124078619942677795 55240512186117929914016693)
            ·
              refine ⟨5178798017448555929439065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55240512186117929914016693 5178798017448555929439065)
              ·
                refine ⟨3884098513086416947079299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5178798017448555929439065 3884098513086416947079299)
                ·
                  refine ⟨5826147769629625420618949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884098513086416947079299 5826147769629625420618949)
                  ·
                    refine ⟨1092402706805554766366053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826147769629625420618949 1092402706805554766366053)
                    ·
                      rfl

theorem cell23_6382340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_6382340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382340 prefixEnd_6382340 := by exact prefixLift 6382340
  have htrace : WordTrace (prefixWord ++ tailWord_6382340) baseStart_6382340 baseEnd_6382340 := by
    simpa [prefixWord, tailWord_6382340, baseEnd_6382340] using wordTrace_append hprefix tailTrace_6382340
  have hstable : (prefixWord ++ tailWord_6382340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382340).length < 2 ^ (prefixWord ++ tailWord_6382340).sum := by decide
  have hdescent : baseEnd_6382340 < baseStart_6382340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382352 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_6382352 : Nat := 118140960795 + 6382352 * 2 ^ 59
def prefixEnd_6382352 : Nat := 4983230072969 + 3 ^ 40 * 6382352 * 2
def baseEnd_6382352 : Nat := 3277214282184518252148103

theorem tailTrace_6382352 : CollatzResearch.WordTrace tailWord_6382352 prefixEnd_6382352 3277214282184518252148103 := by
  unfold tailWord_6382352
  simp only [CollatzResearch.WordTrace]
  refine ⟨116391750686918098892934655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155189000915890798523912873 116391750686918098892934655)
  ·
    refine ⟨174587626030377148339401983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116391750686918098892934655 174587626030377148339401983)
    ·
      refine ⟨261881439045565722509102975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174587626030377148339401983 261881439045565722509102975)
      ·
        refine ⟨392822158568348583763654463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261881439045565722509102975 392822158568348583763654463)
        ·
          refine ⟨589233237852522875645481695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392822158568348583763654463 589233237852522875645481695)
          ·
            refine ⟨883849856778784313468222543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589233237852522875645481695 883849856778784313468222543)
            ·
              refine ⟨1325774785168176470202333815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883849856778784313468222543 1325774785168176470202333815)
              ·
                refine ⟨1988662177752264705303500723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325774785168176470202333815 1988662177752264705303500723)
                ·
                  refine ⟨2982993266628397057955251085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988662177752264705303500723 2982993266628397057955251085)
                  ·
                    refine ⟨1118622474985648896733219157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982993266628397057955251085 1118622474985648896733219157)
                    ·
                      refine ⟨3277214282184518252148103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1118622474985648896733219157 3277214282184518252148103)
                      ·
                        rfl

theorem cell23_6382352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_6382352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382352 prefixEnd_6382352 := by exact prefixLift 6382352
  have htrace : WordTrace (prefixWord ++ tailWord_6382352) baseStart_6382352 baseEnd_6382352 := by
    simpa [prefixWord, tailWord_6382352, baseEnd_6382352] using wordTrace_append hprefix tailTrace_6382352
  have hstable : (prefixWord ++ tailWord_6382352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382352).length < 2 ^ (prefixWord ++ tailWord_6382352).sum := by decide
  have hdescent : baseEnd_6382352 < baseStart_6382352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382373 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 2, 3, 2]
def baseStart_6382373 : Nat := 118140960795 + 6382373 * 2 ^ 59
def prefixEnd_6382373 : Nat := 4983230072969 + 3 ^ 40 * 6382373 * 2
def baseEnd_6382373 : Nat := 3277225065278262669985507

theorem tailTrace_6382373 : CollatzResearch.WordTrace tailWord_6382373 prefixEnd_6382373 3277225065278262669985507 := by
  unfold tailWord_6382373
  simp only [CollatzResearch.WordTrace]
  refine ⟨232784267306760118372383773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155189511537840078914922515 232784267306760118372383773)
  ·
    refine ⟨87294100240035044389643915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232784267306760118372383773 87294100240035044389643915)
    ·
      refine ⟨130941150360052566584465873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87294100240035044389643915 130941150360052566584465873)
      ·
        refine ⟨98205862770039424938349405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130941150360052566584465873 98205862770039424938349405)
        ·
          refine ⟨36827198538764784351881027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98205862770039424938349405 36827198538764784351881027)
          ·
            refine ⟨55240797808147176527821541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36827198538764784351881027 55240797808147176527821541)
            ·
              refine ⟨10357649589027595598966539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55240797808147176527821541 10357649589027595598966539)
              ·
                refine ⟨15536474383541393398449809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10357649589027595598966539 15536474383541393398449809)
                ·
                  refine ⟨11652355787656045048837357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15536474383541393398449809 11652355787656045048837357)
                  ·
                    refine ⟨4369633420371016893314009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11652355787656045048837357 4369633420371016893314009)
                    ·
                      refine ⟨3277225065278262669985507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369633420371016893314009 3277225065278262669985507)
                      ·
                        rfl

theorem cell23_6382373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_6382373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382373 prefixEnd_6382373 := by exact prefixLift 6382373
  have htrace : WordTrace (prefixWord ++ tailWord_6382373) baseStart_6382373 baseEnd_6382373 := by
    simpa [prefixWord, tailWord_6382373, baseEnd_6382373] using wordTrace_append hprefix tailTrace_6382373
  have hstable : (prefixWord ++ tailWord_6382373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382373).length < 2 ^ (prefixWord ++ tailWord_6382373).sum := by decide
  have hdescent : baseEnd_6382373 < baseStart_6382373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382397 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6382397 : Nat := 118140960795 + 6382397 * 2 ^ 59
def prefixEnd_6382397 : Nat := 4983230072969 + 3 ^ 40 * 6382397 * 2
def baseEnd_6382397 : Nat := 3277237388813970576085397

theorem tailTrace_6382397 : CollatzResearch.WordTrace tailWord_6382397 prefixEnd_6382397 3277237388813970576085397 := by
  unfold tailWord_6382397
  simp only [CollatzResearch.WordTrace]
  refine ⟨232785142658673170471257445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155190095105782113647504963 232785142658673170471257445)
  ·
    refine ⟨43647214248501219463360771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232785142658673170471257445 43647214248501219463360771)
    ·
      refine ⟨65470821372751829195041157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43647214248501219463360771 65470821372751829195041157)
      ·
        refine ⟨12275779007390967974070217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65470821372751829195041157 12275779007390967974070217)
        ·
          refine ⟨9206834255543225980552663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12275779007390967974070217 9206834255543225980552663)
          ·
            refine ⟨13810251383314838970828995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9206834255543225980552663 13810251383314838970828995)
            ·
              refine ⟨20715377074972258456243493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13810251383314838970828995 20715377074972258456243493)
              ·
                refine ⟨3884133201557298460545655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20715377074972258456243493 3884133201557298460545655)
                ·
                  refine ⟨5826199802335947690818483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884133201557298460545655 5826199802335947690818483)
                  ·
                    refine ⟨8739299703503921536227725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5826199802335947690818483 8739299703503921536227725)
                    ·
                      refine ⟨3277237388813970576085397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8739299703503921536227725 3277237388813970576085397)
                      ·
                        rfl

theorem cell23_6382397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6382397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382397 prefixEnd_6382397 := by exact prefixLift 6382397
  have htrace : WordTrace (prefixWord ++ tailWord_6382397) baseStart_6382397 baseEnd_6382397 := by
    simpa [prefixWord, tailWord_6382397, baseEnd_6382397] using wordTrace_append hprefix tailTrace_6382397
  have hstable : (prefixWord ++ tailWord_6382397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382397).length < 2 ^ (prefixWord ++ tailWord_6382397).sum := by decide
  have hdescent : baseEnd_6382397 < baseStart_6382397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382403 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 3, 2, 2]
def baseStart_6382403 : Nat := 118140960795 + 6382403 * 2 ^ 59
def prefixEnd_6382403 : Nat := 4983230072969 + 3 ^ 40 * 6382403 * 2
def baseEnd_6382403 : Nat := 3277240469697897552610369

theorem tailTrace_6382403 : CollatzResearch.WordTrace tailWord_6382403 prefixEnd_6382403 3277240469697897552610369 := by
  unfold tailWord_6382403
  simp only [CollatzResearch.WordTrace]
  refine ⟨232785361496651433495975863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155190240997767622330650575 232785361496651433495975863)
  ·
    refine ⟨349178042244977150243963795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232785361496651433495975863 349178042244977150243963795)
    ·
      refine ⟨523767063367465725365945693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349178042244977150243963795 523767063367465725365945693)
      ·
        refine ⟨196412648762799647012229635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523767063367465725365945693 196412648762799647012229635)
        ·
          refine ⟨294618973144199470518344453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196412648762799647012229635 294618973144199470518344453)
          ·
            refine ⟨55241057464537400722189585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294618973144199470518344453 55241057464537400722189585)
            ·
              refine ⟨41430793098403050541642189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55241057464537400722189585 41430793098403050541642189)
              ·
                refine ⟨15536547411901143953115821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41430793098403050541642189 15536547411901143953115821)
                ·
                  refine ⟨5826205279462928982418433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15536547411901143953115821 5826205279462928982418433)
                  ·
                    refine ⟨4369653959597196736813825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5826205279462928982418433 4369653959597196736813825)
                    ·
                      refine ⟨3277240469697897552610369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369653959597196736813825 3277240469697897552610369)
                      ·
                        rfl

theorem cell23_6382403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_6382403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382403 prefixEnd_6382403 := by exact prefixLift 6382403
  have htrace : WordTrace (prefixWord ++ tailWord_6382403) baseStart_6382403 baseEnd_6382403 := by
    simpa [prefixWord, tailWord_6382403, baseEnd_6382403] using wordTrace_append hprefix tailTrace_6382403
  have hstable : (prefixWord ++ tailWord_6382403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382403).length < 2 ^ (prefixWord ++ tailWord_6382403).sum := by decide
  have hdescent : baseEnd_6382403 < baseStart_6382403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382409 : List Nat := [1, 2, 1, 1, 2, 5, 3, 8]
def baseStart_6382409 : Nat := 118140960795 + 6382409 * 2 ^ 59
def prefixEnd_6382409 : Nat := 4983230072969 + 3 ^ 40 * 6382409 * 2
def baseEnd_6382409 : Nat := 121379390762289797375383

theorem tailTrace_6382409 : CollatzResearch.WordTrace tailWord_6382409 prefixEnd_6382409 121379390762289797375383 := by
  unfold tailWord_6382409
  simp only [CollatzResearch.WordTrace]
  refine ⟨232785580334629696520694281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155190386889753131013796187 232785580334629696520694281)
  ·
    refine ⟨174589185250972272390520711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232785580334629696520694281 174589185250972272390520711)
    ·
      refine ⟨261883777876458408585781067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174589185250972272390520711 261883777876458408585781067)
      ·
        refine ⟨392825666814687612878671601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261883777876458408585781067 392825666814687612878671601)
        ·
          refine ⟨294619250111015709659003701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392825666814687612878671601 294619250111015709659003701)
          ·
            refine ⟨27620554697907722780531597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294619250111015709659003701 27620554697907722780531597)
            ·
              refine ⟨10357708011715396042699349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27620554697907722780531597 10357708011715396042699349)
              ·
                refine ⟨121379390762289797375383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10357708011715396042699349 121379390762289797375383)
                ·
                  rfl

theorem cell23_6382409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 8].length) (baseStart_6382409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382409 prefixEnd_6382409 := by exact prefixLift 6382409
  have htrace : WordTrace (prefixWord ++ tailWord_6382409) baseStart_6382409 baseEnd_6382409 := by
    simpa [prefixWord, tailWord_6382409, baseEnd_6382409] using wordTrace_append hprefix tailTrace_6382409
  have hstable : (prefixWord ++ tailWord_6382409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382409).length < 2 ^ (prefixWord ++ tailWord_6382409).sum := by decide
  have hdescent : baseEnd_6382409 < baseStart_6382409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382426 : List Nat := [3, 1, 1, 2, 1, 5, 3, 7]
def baseStart_6382426 : Nat := 118140960795 + 6382426 * 2 ^ 59
def prefixEnd_6382426 : Nat := 4983230072969 + 3 ^ 40 * 6382426 * 2
def baseEnd_6382426 : Nat := 121379714064924109726769

theorem tailTrace_6382426 : CollatzResearch.WordTrace tailWord_6382426 prefixEnd_6382426 121379714064924109726769 := by
  unfold tailWord_6382426
  simp only [CollatzResearch.WordTrace]
  refine ⟨58196550093892027106015783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155190800250378738949375421 58196550093892027106015783)
  ·
    refine ⟨87294825140838040659023675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58196550093892027106015783 87294825140838040659023675)
    ·
      refine ⟨130942237711257060988535513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87294825140838040659023675 130942237711257060988535513)
      ·
        refine ⟨98206678283442795741401635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130942237711257060988535513 98206678283442795741401635)
        ·
          refine ⟨147310017425164193612102453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98206678283442795741401635 147310017425164193612102453)
          ·
            refine ⟨13810314133609143151134605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147310017425164193612102453 13810314133609143151134605)
            ·
              refine ⟨5178867800103428681675477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13810314133609143151134605 5178867800103428681675477)
              ·
                refine ⟨121379714064924109726769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5178867800103428681675477 121379714064924109726769)
                ·
                  rfl

theorem cell23_6382426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_6382426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382426 prefixEnd_6382426 := by exact prefixLift 6382426
  have htrace : WordTrace (prefixWord ++ tailWord_6382426) baseStart_6382426 baseEnd_6382426 := by
    simpa [prefixWord, tailWord_6382426, baseEnd_6382426] using wordTrace_append hprefix tailTrace_6382426
  have hstable : (prefixWord ++ tailWord_6382426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382426).length < 2 ^ (prefixWord ++ tailWord_6382426).sum := by decide
  have hdescent : baseEnd_6382426 < baseStart_6382426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382440 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_6382440 : Nat := 118140960795 + 6382440 * 2 ^ 59
def prefixEnd_6382440 : Nat := 4983230072969 + 3 ^ 40 * 6382440 * 2
def baseEnd_6382440 : Nat := 3277259468482113907847699

theorem tailTrace_6382440 : CollatzResearch.WordTrace tailWord_6382440 prefixEnd_6382440 3277259468482113907847699 := by
  unfold tailWord_6382440
  simp only [CollatzResearch.WordTrace]
  refine ⟨116393355498758694407536387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155191140665011592543381849 116393355498758694407536387)
  ·
    refine ⟨174590033248138041611304581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116393355498758694407536387 174590033248138041611304581)
    ·
      refine ⟨32735631234025882802119609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174590033248138041611304581 32735631234025882802119609)
      ·
        refine ⟨24551723425519412101589707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32735631234025882802119609 24551723425519412101589707)
        ·
          refine ⟨36827585138279118152384561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24551723425519412101589707 36827585138279118152384561)
          ·
            refine ⟨27620688853709338614288421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36827585138279118152384561 27620688853709338614288421)
            ·
              refine ⟨5178879160070500990179079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27620688853709338614288421 5178879160070500990179079)
              ·
                refine ⟨7768318740105751485268619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178879160070500990179079 7768318740105751485268619)
                ·
                  refine ⟨11652478110158627227902929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7768318740105751485268619 11652478110158627227902929)
                  ·
                    refine ⟨8739358582618970420927197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11652478110158627227902929 8739358582618970420927197)
                    ·
                      refine ⟨3277259468482113907847699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8739358582618970420927197 3277259468482113907847699)
                      ·
                        rfl

theorem cell23_6382440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_6382440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382440 prefixEnd_6382440 := by exact prefixLift 6382440
  have htrace : WordTrace (prefixWord ++ tailWord_6382440) baseStart_6382440 baseEnd_6382440 := by
    simpa [prefixWord, tailWord_6382440, baseEnd_6382440] using wordTrace_append hprefix tailTrace_6382440
  have hstable : (prefixWord ++ tailWord_6382440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382440).length < 2 ^ (prefixWord ++ tailWord_6382440).sum := by decide
  have hdescent : baseEnd_6382440 < baseStart_6382440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382454 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6382454 : Nat := 118140960795 + 6382454 * 2 ^ 59
def prefixEnd_6382454 : Nat := 4983230072969 + 3 ^ 40 * 6382454 * 2
def baseEnd_6382454 : Nat := 3277266657211276853072635

theorem tailTrace_6382454 : CollatzResearch.WordTrace tailWord_6382454 prefixEnd_6382454 3277266657211276853072635 := by
  unfold tailWord_6382454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14549201351216666825380151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155191481079644446137388277 14549201351216666825380151)
  ·
    refine ⟨21823802026825000238070227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14549201351216666825380151 21823802026825000238070227)
    ·
      refine ⟨32735703040237500357105341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21823802026825000238070227 32735703040237500357105341)
      ·
        refine ⟨12275888640089062633914503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32735703040237500357105341 12275888640089062633914503)
        ·
          refine ⟨18413832960133593950871755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275888640089062633914503 18413832960133593950871755)
          ·
            refine ⟨27620749440200390926307633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18413832960133593950871755 27620749440200390926307633)
            ·
              refine ⟨20715562080150293194730725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27620749440200390926307633 20715562080150293194730725)
              ·
                refine ⟨3884167890028179974012011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20715562080150293194730725 3884167890028179974012011)
                ·
                  refine ⟨5826251835042269961018017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884167890028179974012011 5826251835042269961018017)
                  ·
                    refine ⟨4369688876281702470763513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5826251835042269961018017 4369688876281702470763513)
                    ·
                      refine ⟨3277266657211276853072635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369688876281702470763513 3277266657211276853072635)
                      ·
                        rfl

theorem cell23_6382454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6382454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382454 prefixEnd_6382454 := by exact prefixLift 6382454
  have htrace : WordTrace (prefixWord ++ tailWord_6382454) baseStart_6382454 baseEnd_6382454 := by
    simpa [prefixWord, tailWord_6382454, baseEnd_6382454] using wordTrace_append hprefix tailTrace_6382454
  have hstable : (prefixWord ++ tailWord_6382454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382454).length < 2 ^ (prefixWord ++ tailWord_6382454).sum := by decide
  have hdescent : baseEnd_6382454 < baseStart_6382454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382459 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4]
def baseStart_6382459 : Nat := 118140960795 + 6382459 * 2 ^ 59
def prefixEnd_6382459 : Nat := 4983230072969 + 3 ^ 40 * 6382459 * 2
def baseEnd_6382459 : Nat := 3277269224614549333510111

theorem tailTrace_6382459 : CollatzResearch.WordTrace tailWord_6382459 prefixEnd_6382459 3277269224614549333510111 := by
  unfold tailWord_6382459
  simp only [CollatzResearch.WordTrace]
  refine ⟨232787403984448555060014431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155191602656299036706676287 232787403984448555060014431)
  ·
    refine ⟨349181105976672832590021647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232787403984448555060014431 349181105976672832590021647)
    ·
      refine ⟨523771658965009248885032471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349181105976672832590021647 523771658965009248885032471)
      ·
        refine ⟨785657488447513873327548707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523771658965009248885032471 785657488447513873327548707)
        ·
          refine ⟨1178486232671270809991323061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785657488447513873327548707 1178486232671270809991323061)
          ·
            refine ⟨110483084312931638436686537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1178486232671270809991323061 110483084312931638436686537)
            ·
              refine ⟨82862313234698728827514903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110483084312931638436686537 82862313234698728827514903)
              ·
                refine ⟨124293469852048093241272355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82862313234698728827514903 124293469852048093241272355)
                ·
                  refine ⟨186440204778072139861908533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124293469852048093241272355 186440204778072139861908533)
                  ·
                    refine ⟨17478769197944263112053925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186440204778072139861908533 17478769197944263112053925)
                    ·
                      refine ⟨3277269224614549333510111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17478769197944263112053925 3277269224614549333510111)
                      ·
                        rfl

theorem cell23_6382459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_6382459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382459 prefixEnd_6382459 := by exact prefixLift 6382459
  have htrace : WordTrace (prefixWord ++ tailWord_6382459) baseStart_6382459 baseEnd_6382459 := by
    simpa [prefixWord, tailWord_6382459, baseEnd_6382459] using wordTrace_append hprefix tailTrace_6382459
  have hstable : (prefixWord ++ tailWord_6382459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382459).length < 2 ^ (prefixWord ++ tailWord_6382459).sum := by decide
  have hdescent : baseEnd_6382459 < baseStart_6382459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382493 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_6382493 : Nat := 118140960795 + 6382493 * 2 ^ 59
def prefixEnd_6382493 : Nat := 4983230072969 + 3 ^ 40 * 6382493 * 2
def baseEnd_6382493 : Nat := 3277286682956802200484955

theorem tailTrace_6382493 : CollatzResearch.WordTrace tailWord_6382493 prefixEnd_6382493 3277286682956802200484955 := by
  unfold tailWord_6382493
  simp only [CollatzResearch.WordTrace]
  refine ⟨232788644066325378866752133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155192429377550252577834755 232788644066325378866752133)
  ·
    refine ⟨43647870762436008537516025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232788644066325378866752133 43647870762436008537516025)
    ·
      refine ⟨32735903071827006403137019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43647870762436008537516025 32735903071827006403137019)
      ·
        refine ⟨49103854607740509604705529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32735903071827006403137019 49103854607740509604705529)
        ·
          refine ⟨36827890955805382203529147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49103854607740509604705529 36827890955805382203529147)
          ·
            refine ⟨55241836433708073305293721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36827890955805382203529147 55241836433708073305293721)
            ·
              refine ⟨41431377325281054978970291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55241836433708073305293721 41431377325281054978970291)
              ·
                refine ⟨62147065987921582468455437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41431377325281054978970291 62147065987921582468455437)
                ·
                  refine ⟨23305149745470593425670789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62147065987921582468455437 23305149745470593425670789)
                  ·
                    refine ⟨4369715577275736267313273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23305149745470593425670789 4369715577275736267313273)
                    ·
                      refine ⟨3277286682956802200484955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369715577275736267313273 3277286682956802200484955)
                      ·
                        rfl

theorem cell23_6382493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_6382493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382493 prefixEnd_6382493 := by exact prefixLift 6382493
  have htrace : WordTrace (prefixWord ++ tailWord_6382493) baseStart_6382493 baseEnd_6382493 := by
    simpa [prefixWord, tailWord_6382493, baseEnd_6382493] using wordTrace_append hprefix tailTrace_6382493
  have hstable : (prefixWord ++ tailWord_6382493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382493).length < 2 ^ (prefixWord ++ tailWord_6382493).sum := by decide
  have hdescent : baseEnd_6382493 < baseStart_6382493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382499 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 9]
def baseStart_6382499 : Nat := 118140960795 + 6382499 * 2 ^ 59
def prefixEnd_6382499 : Nat := 4983230072969 + 3 ^ 40 * 6382499 * 2
def baseEnd_6382499 : Nat := 364143307093414353001103

theorem tailTrace_6382499 : CollatzResearch.WordTrace tailWord_6382499 prefixEnd_6382499 364143307093414353001103 := by
  unfold tailWord_6382499
  simp only [CollatzResearch.WordTrace]
  refine ⟨232788862904303641891470551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155192575269535761260980367 232788862904303641891470551)
  ·
    refine ⟨349183294356455462837205827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232788862904303641891470551 349183294356455462837205827)
    ·
      refine ⟨523774941534683194255808741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349183294356455462837205827 523774941534683194255808741)
      ·
        refine ⟨98207801537753098922964139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 523774941534683194255808741 98207801537753098922964139)
        ·
          refine ⟨147311702306629648384446209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98207801537753098922964139 147311702306629648384446209)
          ·
            refine ⟨110483776729972236288334657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147311702306629648384446209 110483776729972236288334657)
            ·
              refine ⟨82862832547479177216250993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110483776729972236288334657 82862832547479177216250993)
              ·
                refine ⟨62147124410609382912188245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82862832547479177216250993 62147124410609382912188245)
                ·
                  refine ⟨364143307093414353001103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62147124410609382912188245 364143307093414353001103)
                  ·
                    rfl

theorem cell23_6382499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 9].length) (baseStart_6382499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382499 prefixEnd_6382499 := by exact prefixLift 6382499
  have htrace : WordTrace (prefixWord ++ tailWord_6382499) baseStart_6382499 baseEnd_6382499 := by
    simpa [prefixWord, tailWord_6382499, baseEnd_6382499] using wordTrace_append hprefix tailTrace_6382499
  have hstable : (prefixWord ++ tailWord_6382499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382499).length < 2 ^ (prefixWord ++ tailWord_6382499).sum := by decide
  have hdescent : baseEnd_6382499 < baseStart_6382499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382567 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 5]
def baseStart_6382567 : Nat := 118140960795 + 6382567 * 2 ^ 59
def prefixEnd_6382567 : Nat := 4983230072969 + 3 ^ 40 * 6382567 * 2
def baseEnd_6382567 : Nat := 364147186725026101217735

theorem tailTrace_6382567 : CollatzResearch.WordTrace tailWord_6382567 prefixEnd_6382567 364147186725026101217735 := by
  unfold tailWord_6382567
  simp only [CollatzResearch.WordTrace]
  refine ⟨232791343068057289504945955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155194228712038193003297303 232791343068057289504945955)
  ·
    refine ⟨349187014602085934257418933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232791343068057289504945955 349187014602085934257418933)
    ·
      refine ⟨32736282618945556336633025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 349187014602085934257418933 32736282618945556336633025)
      ·
        refine ⟨24552211964209167252474769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32736282618945556336633025 24552211964209167252474769)
        ·
          refine ⟨18414158973156875439356077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24552211964209167252474769 18414158973156875439356077)
          ·
            refine ⟨6905309614933828289758529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18414158973156875439356077 6905309614933828289758529)
            ·
              refine ⟨5178982211200371217318897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6905309614933828289758529 5178982211200371217318897)
              ·
                refine ⟨3884236658400278412989173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5178982211200371217318897 3884236658400278412989173)
                ·
                  refine ⟨364147186725026101217735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3884236658400278412989173 364147186725026101217735)
                  ·
                    rfl

theorem cell23_6382567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 5].length) (baseStart_6382567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382567 prefixEnd_6382567 := by exact prefixLift 6382567
  have htrace : WordTrace (prefixWord ++ tailWord_6382567) baseStart_6382567 baseEnd_6382567 := by
    simpa [prefixWord, tailWord_6382567, baseEnd_6382567] using wordTrace_append hprefix tailTrace_6382567
  have hstable : (prefixWord ++ tailWord_6382567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382567).length < 2 ^ (prefixWord ++ tailWord_6382567).sum := by decide
  have hdescent : baseEnd_6382567 < baseStart_6382567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382593 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6382593 : Nat := 118140960795 + 6382593 * 2 ^ 59
def prefixEnd_6382593 : Nat := 4983230072969 + 3 ^ 40 * 6382593 * 2
def baseEnd_6382593 : Nat := 1092446010340750603078165

theorem tailTrace_6382593 : CollatzResearch.WordTrace tailWord_6382593 prefixEnd_6382593 1092446010340750603078165 := by
  unfold tailWord_6382593
  simp only [CollatzResearch.WordTrace]
  refine ⟨232792291365963095945392433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155194860910642063963594955 232792291365963095945392433)
  ·
    refine ⟨174594218524472321959044325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232792291365963095945392433 174594218524472321959044325)
    ·
      refine ⟨32736415973338560367320811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174594218524472321959044325 32736415973338560367320811)
      ·
        refine ⟨49104623960007840550981217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32736415973338560367320811 49104623960007840550981217)
        ·
          refine ⟨36828467970005880413235913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49104623960007840550981217 36828467970005880413235913)
          ·
            refine ⟨27621350977504410309926935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36828467970005880413235913 27621350977504410309926935)
            ·
              refine ⟨41432026466256615464890403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27621350977504410309926935 41432026466256615464890403)
              ·
                refine ⟨62148039699384923197335605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41432026466256615464890403 62148039699384923197335605)
                ·
                  refine ⟨5826378721817336549750213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62148039699384923197335605 5826378721817336549750213)
                  ·
                    refine ⟨1092446010340750603078165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826378721817336549750213 1092446010340750603078165)
                    ·
                      rfl

theorem cell23_6382593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6382593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382593 prefixEnd_6382593 := by exact prefixLift 6382593
  have htrace : WordTrace (prefixWord ++ tailWord_6382593) baseStart_6382593 baseEnd_6382593 := by
    simpa [prefixWord, tailWord_6382593, baseEnd_6382593] using wordTrace_append hprefix tailTrace_6382593
  have hstable : (prefixWord ++ tailWord_6382593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382593).length < 2 ^ (prefixWord ++ tailWord_6382593).sum := by decide
  have hdescent : baseEnd_6382593 < baseStart_6382593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382600 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_6382600 : Nat := 118140960795 + 6382600 * 2 ^ 59
def prefixEnd_6382600 : Nat := 4983230072969 + 3 ^ 40 * 6382600 * 2
def baseEnd_6382600 : Nat := 3277341625386833281846963

theorem tailTrace_6382600 : CollatzResearch.WordTrace tailWord_6382600 prefixEnd_6382600 3277341625386833281846963 := by
  unfold tailWord_6382600
  simp only [CollatzResearch.WordTrace]
  refine ⟨116396273338468868070448627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155195031117958490760598169 116396273338468868070448627)
  ·
    refine ⟨174594410007703302105672941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116396273338468868070448627 174594410007703302105672941)
    ·
      refine ⟨65472903752888738289627353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174594410007703302105672941 65472903752888738289627353)
      ·
        refine ⟨49104677814666553717220515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65472903752888738289627353 49104677814666553717220515)
        ·
          refine ⟨73657016721999830575830773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49104677814666553717220515 73657016721999830575830773)
          ·
            refine ⟨6905345317687484116484135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73657016721999830575830773 6905345317687484116484135)
            ·
              refine ⟨10358017976531226174726203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6905345317687484116484135 10358017976531226174726203)
              ·
                refine ⟨15537026964796839262089305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10358017976531226174726203 15537026964796839262089305)
                ·
                  refine ⟨11652770223597629446566979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15537026964796839262089305 11652770223597629446566979)
                  ·
                    refine ⟨17479155335396444169850469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11652770223597629446566979 17479155335396444169850469)
                    ·
                      refine ⟨3277341625386833281846963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17479155335396444169850469 3277341625386833281846963)
                      ·
                        rfl

theorem cell23_6382600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_6382600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382600 prefixEnd_6382600 := by exact prefixLift 6382600
  have htrace : WordTrace (prefixWord ++ tailWord_6382600) baseStart_6382600 baseEnd_6382600 := by
    simpa [prefixWord, tailWord_6382600, baseEnd_6382600] using wordTrace_append hprefix tailTrace_6382600
  have hstable : (prefixWord ++ tailWord_6382600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382600).length < 2 ^ (prefixWord ++ tailWord_6382600).sum := by decide
  have hdescent : baseEnd_6382600 < baseStart_6382600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382603 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 3]
def baseStart_6382603 : Nat := 118140960795 + 6382603 * 2 ^ 59
def prefixEnd_6382603 : Nat := 4983230072969 + 3 ^ 40 * 6382603 * 2
def baseEnd_6382603 : Nat := 3277343165828796770109449

theorem tailTrace_6382603 : CollatzResearch.WordTrace tailWord_6382603 prefixEnd_6382603 3277343165828796770109449 := by
  unfold tailWord_6382603
  simp only [CollatzResearch.WordTrace]
  refine ⟨232792656095926867653256463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155195104063951245102170975 232792656095926867653256463)
  ·
    refine ⟨349188984143890301479884695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232792656095926867653256463 349188984143890301479884695)
    ·
      refine ⟨523783476215835452219827043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349188984143890301479884695 523783476215835452219827043)
      ·
        refine ⟨785675214323753178329740565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523783476215835452219827043 785675214323753178329740565)
        ·
          refine ⟨36828525671425930234206589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 785675214323753178329740565 36828525671425930234206589)
          ·
            refine ⟨13810697126784723837827471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36828525671425930234206589 13810697126784723837827471)
            ·
              refine ⟨20716045690177085756741207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13810697126784723837827471 20716045690177085756741207)
              ·
                refine ⟨31074068535265628635111811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20716045690177085756741207 31074068535265628635111811)
                ·
                  refine ⟨46611102802898442952667717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31074068535265628635111811 46611102802898442952667717)
                  ·
                    refine ⟨8739581775543458053625197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46611102802898442952667717 8739581775543458053625197)
                    ·
                      refine ⟨3277343165828796770109449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8739581775543458053625197 3277343165828796770109449)
                      ·
                        rfl

theorem cell23_6382603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 3].length) (baseStart_6382603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382603 prefixEnd_6382603 := by exact prefixLift 6382603
  have htrace : WordTrace (prefixWord ++ tailWord_6382603) baseStart_6382603 baseEnd_6382603 := by
    simpa [prefixWord, tailWord_6382603, baseEnd_6382603] using wordTrace_append hprefix tailTrace_6382603
  have hstable : (prefixWord ++ tailWord_6382603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382603).length < 2 ^ (prefixWord ++ tailWord_6382603).sum := by decide
  have hdescent : baseEnd_6382603 < baseStart_6382603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382623 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 6]
def baseStart_6382623 : Nat := 118140960795 + 6382623 * 2 ^ 59
def prefixEnd_6382623 : Nat := 4983230072969 + 3 ^ 40 * 6382623 * 2
def baseEnd_6382623 : Nat := 364150381715765187984373

theorem tailTrace_6382623 : CollatzResearch.WordTrace tailWord_6382623 prefixEnd_6382623 364150381715765187984373 := by
  unfold tailWord_6382623
  simp only [CollatzResearch.WordTrace]
  refine ⟨232793385555854411068984523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155195590370569607379323015 232793385555854411068984523)
  ·
    refine ⟨349190078333781616603476785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232793385555854411068984523 349190078333781616603476785)
    ·
      refine ⟨261892558750336212452607589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349190078333781616603476785 261892558750336212452607589)
      ·
        refine ⟨49104854765688039834863923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261892558750336212452607589 49104854765688039834863923)
        ·
          refine ⟨73657282148532059752295885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49104854765688039834863923 73657282148532059752295885)
          ·
            refine ⟨27621480805699522407110957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73657282148532059752295885 27621480805699522407110957)
            ·
              refine ⟨10358055302137320902666609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27621480805699522407110957 10358055302137320902666609)
              ·
                refine ⟨7768541476602990676999957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10358055302137320902666609 7768541476602990676999957)
                ·
                  refine ⟨364150381715765187984373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7768541476602990676999957 364150381715765187984373)
                  ·
                    rfl

theorem cell23_6382623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 6].length) (baseStart_6382623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382623 prefixEnd_6382623 := by exact prefixLift 6382623
  have htrace : WordTrace (prefixWord ++ tailWord_6382623) baseStart_6382623 baseEnd_6382623 := by
    simpa [prefixWord, tailWord_6382623, baseEnd_6382623] using wordTrace_append hprefix tailTrace_6382623
  have hstable : (prefixWord ++ tailWord_6382623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382623).length < 2 ^ (prefixWord ++ tailWord_6382623).sum := by decide
  have hdescent : baseEnd_6382623 < baseStart_6382623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382650 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_6382650 : Nat := 118140960795 + 6382650 * 2 ^ 59
def prefixEnd_6382650 : Nat := 4983230072969 + 3 ^ 40 * 6382650 * 2
def baseEnd_6382650 : Nat := 3277367299419558086221733

theorem tailTrace_6382650 : CollatzResearch.WordTrace tailWord_6382650 prefixEnd_6382650 3277367299419558086221733 := by
  unfold tailWord_6382650
  simp only [CollatzResearch.WordTrace]
  refine ⟨58198592581689148670054351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155196246884504396453478269 58198592581689148670054351)
  ·
    refine ⟨87297888872533723005081527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58198592581689148670054351 87297888872533723005081527)
    ·
      refine ⟨130946833308800584507622291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87297888872533723005081527 130946833308800584507622291)
      ·
        refine ⟨196420249963200876761433437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130946833308800584507622291 196420249963200876761433437)
        ·
          refine ⟨73657593736200328785537539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196420249963200876761433437 73657593736200328785537539)
          ·
            refine ⟨110486390604300493178306309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73657593736200328785537539 110486390604300493178306309)
            ·
              refine ⟨20716198238306342470932433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110486390604300493178306309 20716198238306342470932433)
              ·
                refine ⟨15537148678729756853199325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20716198238306342470932433 15537148678729756853199325)
                ·
                  refine ⟨5826430754523658819949747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15537148678729756853199325 5826430754523658819949747)
                  ·
                    refine ⟨8739646131785488229924621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5826430754523658819949747 8739646131785488229924621)
                    ·
                      refine ⟨3277367299419558086221733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8739646131785488229924621 3277367299419558086221733)
                      ·
                        rfl

theorem cell23_6382650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_6382650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382650 prefixEnd_6382650 := by exact prefixLift 6382650
  have htrace : WordTrace (prefixWord ++ tailWord_6382650) baseStart_6382650 baseEnd_6382650 := by
    simpa [prefixWord, tailWord_6382650, baseEnd_6382650] using wordTrace_append hprefix tailTrace_6382650
  have hstable : (prefixWord ++ tailWord_6382650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382650).length < 2 ^ (prefixWord ++ tailWord_6382650).sum := by decide
  have hdescent : baseEnd_6382650 < baseStart_6382650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382678 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6382678 : Nat := 118140960795 + 6382678 * 2 ^ 59
def prefixEnd_6382678 : Nat := 4983230072969 + 3 ^ 40 * 6382678 * 2
def baseEnd_6382678 : Nat := 1092460558959294658890535

theorem tailTrace_6382678 : CollatzResearch.WordTrace tailWord_6382678 prefixEnd_6382678 1092460558959294658890535 := by
  unfold tailWord_6382678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14549711973165947216389793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155196927713770103641491125 14549711973165947216389793)
  ·
    refine ⟨10912283979874460412292345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14549711973165947216389793 10912283979874460412292345)
    ·
      refine ⟨8184212984905845309219259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10912283979874460412292345 8184212984905845309219259)
      ·
        refine ⟨12276319477358767963828889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8184212984905845309219259 12276319477358767963828889)
        ·
          refine ⟨9207239608019075972871667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12276319477358767963828889 9207239608019075972871667)
          ·
            refine ⟨13810859412028613959307501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207239608019075972871667 13810859412028613959307501)
            ·
              refine ⟨5179072279510730234740313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13810859412028613959307501 5179072279510730234740313)
              ·
                refine ⟨3884304209633047676055235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5179072279510730234740313 3884304209633047676055235)
                ·
                  refine ⟨5826456314449571514082853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884304209633047676055235 5826456314449571514082853)
                  ·
                    refine ⟨1092460558959294658890535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826456314449571514082853 1092460558959294658890535)
                    ·
                      rfl

theorem cell23_6382678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6382678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382678 prefixEnd_6382678 := by exact prefixLift 6382678
  have htrace : WordTrace (prefixWord ++ tailWord_6382678) baseStart_6382678 baseEnd_6382678 := by
    simpa [prefixWord, tailWord_6382678, baseEnd_6382678] using wordTrace_append hprefix tailTrace_6382678
  have hstable : (prefixWord ++ tailWord_6382678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382678).length < 2 ^ (prefixWord ++ tailWord_6382678).sum := by decide
  have hdescent : baseEnd_6382678 < baseStart_6382678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382693 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6382693 : Nat := 118140960795 + 6382693 * 2 ^ 59
def prefixEnd_6382693 : Nat := 4983230072969 + 3 ^ 40 * 6382693 * 2
def baseEnd_6382693 : Nat := 3277389379087701417984035

theorem tailTrace_6382693 : CollatzResearch.WordTrace tailWord_6382693 prefixEnd_6382693 3277389379087701417984035 := by
  unfold tailWord_6382693
  simp only [CollatzResearch.WordTrace]
  refine ⟨232795938665600813024032733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155197292443733875349355155 232795938665600813024032733)
  ·
    refine ⟨87298476999600304884012275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232795938665600813024032733 87298476999600304884012275)
    ·
      refine ⟨130947715499400457326018413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87298476999600304884012275 130947715499400457326018413)
      ·
        refine ⟨49105393312275171497256905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130947715499400457326018413 49105393312275171497256905)
        ·
          refine ⟨36829044984206378622942679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49105393312275171497256905 36829044984206378622942679)
          ·
            refine ⟨55243567476309567934414019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36829044984206378622942679 55243567476309567934414019)
            ·
              refine ⟨82865351214464351901621029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55243567476309567934414019 82865351214464351901621029)
              ·
                refine ⟨15537253352712065981553943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82865351214464351901621029 15537253352712065981553943)
                ·
                  refine ⟨23305880029068098972330915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15537253352712065981553943 23305880029068098972330915)
                  ·
                    refine ⟨34958820043602148458496373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23305880029068098972330915 34958820043602148458496373)
                    ·
                      refine ⟨3277389379087701417984035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34958820043602148458496373 3277389379087701417984035)
                      ·
                        rfl

theorem cell23_6382693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6382693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382693 prefixEnd_6382693 := by exact prefixLift 6382693
  have htrace : WordTrace (prefixWord ++ tailWord_6382693) baseStart_6382693 baseEnd_6382693 := by
    simpa [prefixWord, tailWord_6382693, baseEnd_6382693] using wordTrace_append hprefix tailTrace_6382693
  have hstable : (prefixWord ++ tailWord_6382693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382693).length < 2 ^ (prefixWord ++ tailWord_6382693).sum := by decide
  have hdescent : baseEnd_6382693 < baseStart_6382693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382700 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_6382700 : Nat := 118140960795 + 6382700 * 2 ^ 59
def prefixEnd_6382700 : Nat := 4983230072969 + 3 ^ 40 * 6382700 * 2
def baseEnd_6382700 : Nat := 1092464324484094296865501

theorem tailTrace_6382700 : CollatzResearch.WordTrace tailWord_6382700 prefixEnd_6382700 1092464324484094296865501 := by
  unfold tailWord_6382700
  simp only [CollatzResearch.WordTrace]
  refine ⟨116398096988287726609768777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155197462651050302146358369 116398096988287726609768777)
  ·
    refine ⟨87298572741215794957326583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116398096988287726609768777 87298572741215794957326583)
    ·
      refine ⟨130947859111823692435989875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87298572741215794957326583 130947859111823692435989875)
      ·
        refine ⟨196421788667735538653984813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130947859111823692435989875 196421788667735538653984813)
        ·
          refine ⟨73658170750400826995244305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196421788667735538653984813 73658170750400826995244305)
          ·
            refine ⟨55243628062800620246433229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73658170750400826995244305 55243628062800620246433229)
            ·
              refine ⟨20716360523550232592412461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55243628062800620246433229 20716360523550232592412461)
              ·
                refine ⟨7768635196331337222154673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20716360523550232592412461 7768635196331337222154673)
                ·
                  refine ⟨5826476397248502916616005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7768635196331337222154673 5826476397248502916616005)
                  ·
                    refine ⟨1092464324484094296865501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826476397248502916616005 1092464324484094296865501)
                    ·
                      rfl

theorem cell23_6382700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_6382700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382700 prefixEnd_6382700 := by exact prefixLift 6382700
  have htrace : WordTrace (prefixWord ++ tailWord_6382700) baseStart_6382700 baseEnd_6382700 := by
    simpa [prefixWord, tailWord_6382700, baseEnd_6382700] using wordTrace_append hprefix tailTrace_6382700
  have hstable : (prefixWord ++ tailWord_6382700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382700).length < 2 ^ (prefixWord ++ tailWord_6382700).sum := by decide
  have hdescent : baseEnd_6382700 < baseStart_6382700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382703 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_6382703 : Nat := 118140960795 + 6382703 * 2 ^ 59
def prefixEnd_6382703 : Nat := 4983230072969 + 3 ^ 40 * 6382703 * 2
def baseEnd_6382703 : Nat := 3277394513894246378858989

theorem tailTrace_6382703 : CollatzResearch.WordTrace tailWord_6382703 prefixEnd_6382703 3277394513894246378858989 := by
  unfold tailWord_6382703
  simp only [CollatzResearch.WordTrace]
  refine ⟨232796303395564584731896763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155197535597043056487931175 232796303395564584731896763)
  ·
    refine ⟨349194455093346877097845145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232796303395564584731896763 349194455093346877097845145)
    ·
      refine ⟨261895841320010157823383859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349194455093346877097845145 261895841320010157823383859)
      ·
        refine ⟨392843761980015236735075789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261895841320010157823383859 392843761980015236735075789)
        ·
          refine ⟨147316410742505713775653421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392843761980015236735075789 147316410742505713775653421)
          ·
            refine ⟨55243654028439642665870033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147316410742505713775653421 55243654028439642665870033)
            ·
              refine ⟨41432740521329731999402525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55243654028439642665870033 41432740521329731999402525)
              ·
                refine ⟨15537277695498649499775947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41432740521329731999402525 15537277695498649499775947)
                ·
                  refine ⟨23305916543247974249663921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15537277695498649499775947 23305916543247974249663921)
                  ·
                    refine ⟨17479437407435980687247941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23305916543247974249663921 17479437407435980687247941)
                    ·
                      refine ⟨3277394513894246378858989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17479437407435980687247941 3277394513894246378858989)
                      ·
                        rfl

theorem cell23_6382703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_6382703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382703 prefixEnd_6382703 := by exact prefixLift 6382703
  have htrace : WordTrace (prefixWord ++ tailWord_6382703) baseStart_6382703 baseEnd_6382703 := by
    simpa [prefixWord, tailWord_6382703, baseEnd_6382703] using wordTrace_append hprefix tailTrace_6382703
  have hstable : (prefixWord ++ tailWord_6382703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382703).length < 2 ^ (prefixWord ++ tailWord_6382703).sum := by decide
  have hdescent : baseEnd_6382703 < baseStart_6382703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382743 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 2, 7]
def baseStart_6382743 : Nat := 118140960795 + 6382743 * 2 ^ 59
def prefixEnd_6382743 : Nat := 4983230072969 + 3 ^ 40 * 6382743 * 2
def baseEnd_6382743 : Nat := 1092471684373475407452935

theorem tailTrace_6382743 : CollatzResearch.WordTrace tailWord_6382743 prefixEnd_6382743 1092471684373475407452935 := by
  unfold tailWord_6382743
  simp only [CollatzResearch.WordTrace]
  refine ⟨232797762315419671563352883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155198508210279781042235255 232797762315419671563352883)
  ·
    refine ⟨349196643473129507345029325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232797762315419671563352883 349196643473129507345029325)
    ·
      refine ⟨130948741302423565254385997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349196643473129507345029325 130948741302423565254385997)
      ·
        refine ⟨49105777988408836970394749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130948741302423565254385997 49105777988408836970394749)
        ·
          refine ⟨18414666745653313863898031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49105777988408836970394749 18414666745653313863898031)
          ·
            refine ⟨27622000118479970795847047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18414666745653313863898031 27622000118479970795847047)
            ·
              refine ⟨41433000177719956193770571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27622000118479970795847047 41433000177719956193770571)
              ·
                refine ⟨62149500266579934290655857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41433000177719956193770571 62149500266579934290655857)
                ·
                  refine ⟨46612125199934950717991893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62149500266579934290655857 46612125199934950717991893)
                  ·
                    refine ⟨1092471684373475407452935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46612125199934950717991893 1092471684373475407452935)
                    ·
                      rfl

theorem cell23_6382743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_6382743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382743 prefixEnd_6382743 := by exact prefixLift 6382743
  have htrace : WordTrace (prefixWord ++ tailWord_6382743) baseStart_6382743 baseEnd_6382743 := by
    simpa [prefixWord, tailWord_6382743, baseEnd_6382743] using wordTrace_append hprefix tailTrace_6382743
  have hstable : (prefixWord ++ tailWord_6382743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382743).length < 2 ^ (prefixWord ++ tailWord_6382743).sum := by decide
  have hdescent : baseEnd_6382743 < baseStart_6382743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382757 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_6382757 : Nat := 118140960795 + 6382757 * 2 ^ 59
def prefixEnd_6382757 : Nat := 4983230072969 + 3 ^ 40 * 6382757 * 2
def baseEnd_6382757 : Nat := 3277422241849589167583741

theorem tailTrace_6382757 : CollatzResearch.WordTrace tailWord_6382757 prefixEnd_6382757 3277422241849589167583741 := by
  unfold tailWord_6382757
  simp only [CollatzResearch.WordTrace]
  refine ⟨232798272937368951954362525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155198848624912634636241683 232798272937368951954362525)
  ·
    refine ⟨87299352351513356982885947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232798272937368951954362525 87299352351513356982885947)
    ·
      refine ⟨130949028527270035474328921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87299352351513356982885947 130949028527270035474328921)
      ·
        refine ⟨98211771395452526605746691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130949028527270035474328921 98211771395452526605746691)
        ·
          refine ⟨147317657093178789908620037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98211771395452526605746691 147317657093178789908620037)
          ·
            refine ⟨27622060704971023107866257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147317657093178789908620037 27622060704971023107866257)
            ·
              refine ⟨20716545528728267330899693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27622060704971023107866257 20716545528728267330899693)
              ·
                refine ⟨7768704573273100249087385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20716545528728267330899693 7768704573273100249087385)
                ·
                  refine ⟨5826528429954825186815539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7768704573273100249087385 5826528429954825186815539)
                  ·
                    refine ⟨8739792644932237780223309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5826528429954825186815539 8739792644932237780223309)
                    ·
                      refine ⟨3277422241849589167583741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8739792644932237780223309 3277422241849589167583741)
                      ·
                        rfl

theorem cell23_6382757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_6382757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382757 prefixEnd_6382757 := by exact prefixLift 6382757
  have htrace : WordTrace (prefixWord ++ tailWord_6382757) baseStart_6382757 baseEnd_6382757 := by
    simpa [prefixWord, tailWord_6382757, baseEnd_6382757] using wordTrace_append hprefix tailTrace_6382757
  have hstable : (prefixWord ++ tailWord_6382757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382757).length < 2 ^ (prefixWord ++ tailWord_6382757).sum := by decide
  have hdescent : baseEnd_6382757 < baseStart_6382757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382783 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_6382783 : Nat := 118140960795 + 6382783 * 2 ^ 59
def prefixEnd_6382783 : Nat := 4983230072969 + 3 ^ 40 * 6382783 * 2
def baseEnd_6382783 : Nat := 3277435592346606065858621

theorem tailTrace_6382783 : CollatzResearch.WordTrace tailWord_6382783 prefixEnd_6382783 3277435592346606065858621 := by
  unfold tailWord_6382783
  simp only [CollatzResearch.WordTrace]
  refine ⟨232799221235274758394809003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155199480823516505596539335 232799221235274758394809003)
  ·
    refine ⟨349198831852912137592213505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232799221235274758394809003 349198831852912137592213505)
    ·
      refine ⟨261899123889684103194160129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349198831852912137592213505 261899123889684103194160129)
      ·
        refine ⟨196424342917263077395620097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261899123889684103194160129 196424342917263077395620097)
        ·
          refine ⟨147318257187947308046715073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196424342917263077395620097 147318257187947308046715073)
          ·
            refine ⟨110488692890960481035036305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147318257187947308046715073 110488692890960481035036305)
            ·
              refine ⟨82866519668220360776277229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110488692890960481035036305 82866519668220360776277229)
              ·
                refine ⟨31074944875582635291103961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82866519668220360776277229 31074944875582635291103961)
                ·
                  refine ⟨23306208656686976468327971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31074944875582635291103961 23306208656686976468327971)
                  ·
                    refine ⟨34959312985030464702491957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23306208656686976468327971 34959312985030464702491957)
                    ·
                      refine ⟨3277435592346606065858621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34959312985030464702491957 3277435592346606065858621)
                      ·
                        rfl

theorem cell23_6382783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_6382783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382783 prefixEnd_6382783 := by exact prefixLift 6382783
  have htrace : WordTrace (prefixWord ++ tailWord_6382783) baseStart_6382783 baseEnd_6382783 := by
    simpa [prefixWord, tailWord_6382783, baseEnd_6382783] using wordTrace_append hprefix tailTrace_6382783
  have hstable : (prefixWord ++ tailWord_6382783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382783).length < 2 ^ (prefixWord ++ tailWord_6382783).sum := by decide
  have hdescent : baseEnd_6382783 < baseStart_6382783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382784 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 1, 3, 2]
def baseStart_6382784 : Nat := 118140960795 + 6382784 * 2 ^ 59
def prefixEnd_6382784 : Nat := 4983230072969 + 3 ^ 40 * 6382784 * 2
def baseEnd_6382784 : Nat := 3277436105827260561946117

theorem tailTrace_6382784 : CollatzResearch.WordTrace tailWord_6382784 prefixEnd_6382784 3277436105827260561946117 := by
  unfold tailWord_6382784
  simp only [CollatzResearch.WordTrace]
  refine ⟨116399628854135567782797703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155199505138847423710396937 116399628854135567782797703)
  ·
    refine ⟨174599443281203351674196555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116399628854135567782797703 174599443281203351674196555)
    ·
      refine ⟨261899164921805027511294833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174599443281203351674196555 261899164921805027511294833)
      ·
        refine ⟨196424373691353770633471125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261899164921805027511294833 196424373691353770633471125)
        ·
          refine ⟨9207392516782207998443959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196424373691353770633471125 9207392516782207998443959)
          ·
            refine ⟨13811088775173311997665939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207392516782207998443959 13811088775173311997665939)
            ·
              refine ⟨20716633162759967996498909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811088775173311997665939 20716633162759967996498909)
              ·
                refine ⟨7768737436034987998687091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20716633162759967996498909 7768737436034987998687091)
                ·
                  refine ⟨11653106154052481998030637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7768737436034987998687091 11653106154052481998030637)
                  ·
                    refine ⟨4369914807769680749261489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11653106154052481998030637 4369914807769680749261489)
                    ·
                      refine ⟨3277436105827260561946117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369914807769680749261489 3277436105827260561946117)
                      ·
                        rfl

theorem cell23_6382784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_6382784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382784 prefixEnd_6382784 := by exact prefixLift 6382784
  have htrace : WordTrace (prefixWord ++ tailWord_6382784) baseStart_6382784 baseEnd_6382784 := by
    simpa [prefixWord, tailWord_6382784, baseEnd_6382784] using wordTrace_append hprefix tailTrace_6382784
  have hstable : (prefixWord ++ tailWord_6382784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382784).length < 2 ^ (prefixWord ++ tailWord_6382784).sum := by decide
  have hdescent : baseEnd_6382784 < baseStart_6382784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382830 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_6382830 : Nat := 118140960795 + 6382830 * 2 ^ 59
def prefixEnd_6382830 : Nat := 4983230072969 + 3 ^ 40 * 6382830 * 2
def baseEnd_6382830 : Nat := 3277459725937367381970905

theorem tailTrace_6382830 : CollatzResearch.WordTrace tailWord_6382830 prefixEnd_6382830 3277459725937367381970905 := by
  unfold tailWord_6382830
  simp only [CollatzResearch.WordTrace]
  refine ⟨29100116933263060677721243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155200623644069656947846629 29100116933263060677721243)
  ·
    refine ⟨43650175399894591016581865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29100116933263060677721243 43650175399894591016581865)
    ·
      refine ⟨32737631549920943262436399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43650175399894591016581865 32737631549920943262436399)
      ·
        refine ⟨49106447324881414893654599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32737631549920943262436399 49106447324881414893654599)
        ·
          refine ⟨73659670987322122340481899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49106447324881414893654599 73659670987322122340481899)
          ·
            refine ⟨110489506480983183510722849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73659670987322122340481899 110489506480983183510722849)
            ·
              refine ⟨82867129860737387633042137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110489506480983183510722849 82867129860737387633042137)
              ·
                refine ⟨62150347395553040724781603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82867129860737387633042137 62150347395553040724781603)
                ·
                  refine ⟨93225521093329561087172405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62150347395553040724781603 93225521093329561087172405)
                  ·
                    refine ⟨8739892602499646351922413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93225521093329561087172405 8739892602499646351922413)
                    ·
                      refine ⟨3277459725937367381970905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8739892602499646351922413 3277459725937367381970905)
                      ·
                        rfl

theorem cell23_6382830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_6382830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382830 prefixEnd_6382830 := by exact prefixLift 6382830
  have htrace : WordTrace (prefixWord ++ tailWord_6382830) baseStart_6382830 baseEnd_6382830 := by
    simpa [prefixWord, tailWord_6382830, baseEnd_6382830] using wordTrace_append hprefix tailTrace_6382830
  have hstable : (prefixWord ++ tailWord_6382830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382830).length < 2 ^ (prefixWord ++ tailWord_6382830).sum := by decide
  have hdescent : baseEnd_6382830 < baseStart_6382830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382840 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 7, 2]
def baseStart_6382840 : Nat := 118140960795 + 6382840 * 2 ^ 59
def prefixEnd_6382840 : Nat := 4983230072969 + 3 ^ 40 * 6382840 * 2
def baseEnd_6382840 : Nat := 3277464860743912342845859

theorem tailTrace_6382840 : CollatzResearch.WordTrace tailWord_6382840 prefixEnd_6382840 3277464860743912342845859 := by
  unfold tailWord_6382840
  simp only [CollatzResearch.WordTrace]
  refine ⟨116400650098034128564816987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155200866797378838086422649 116400650098034128564816987)
  ·
    refine ⟨174600975147051192847225481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116400650098034128564816987 174600975147051192847225481)
    ·
      refine ⟨130950731360288394635419111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174600975147051192847225481 130950731360288394635419111)
      ·
        refine ⟨196426097040432591953128667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130950731360288394635419111 196426097040432591953128667)
        ·
          refine ⟨294639145560648887929693001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196426097040432591953128667 294639145560648887929693001)
          ·
            refine ⟨220979359170486665947269751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294639145560648887929693001 220979359170486665947269751)
            ·
              refine ⟨331469038755729998920904627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220979359170486665947269751 331469038755729998920904627)
              ·
                refine ⟨497203558133594998381356941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331469038755729998920904627 497203558133594998381356941)
                ·
                  refine ⟨186451334300098124393008853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497203558133594998381356941 186451334300098124393008853)
                  ·
                    refine ⟨4369953147658549790461145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 186451334300098124393008853 4369953147658549790461145)
                    ·
                      refine ⟨3277464860743912342845859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4369953147658549790461145 3277464860743912342845859)
                      ·
                        rfl

theorem cell23_6382840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_6382840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382840 prefixEnd_6382840 := by exact prefixLift 6382840
  have htrace : WordTrace (prefixWord ++ tailWord_6382840) baseStart_6382840 baseEnd_6382840 := by
    simpa [prefixWord, tailWord_6382840, baseEnd_6382840] using wordTrace_append hprefix tailTrace_6382840
  have hstable : (prefixWord ++ tailWord_6382840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382840).length < 2 ^ (prefixWord ++ tailWord_6382840).sum := by decide
  have hdescent : baseEnd_6382840 < baseStart_6382840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382860 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_6382860 : Nat := 118140960795 + 6382860 * 2 ^ 59
def prefixEnd_6382860 : Nat := 4983230072969 + 3 ^ 40 * 6382860 * 2
def baseEnd_6382860 : Nat := 3277475130357002264595767

theorem tailTrace_6382860 : CollatzResearch.WordTrace tailWord_6382860 prefixEnd_6382860 3277475130357002264595767 := by
  unfold tailWord_6382860
  simp only [CollatzResearch.WordTrace]
  refine ⟨116401014827997900272681017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155201353103997200363574689 116401014827997900272681017)
  ·
    refine ⟨87300761120998425204510763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116401014827997900272681017 87300761120998425204510763)
    ·
      refine ⟨130951141681497637806766145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87300761120998425204510763 130951141681497637806766145)
      ·
        refine ⟨98213356261123228355074609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130951141681497637806766145 98213356261123228355074609)
        ·
          refine ⟨73660017195842421266305957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98213356261123228355074609 73660017195842421266305957)
          ·
            refine ⟨13811253224220453987432367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73660017195842421266305957 13811253224220453987432367)
            ·
              refine ⟨20716879836330680981148551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811253224220453987432367 20716879836330680981148551)
              ·
                refine ⟨31075319754496021471722827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20716879836330680981148551 31075319754496021471722827)
                ·
                  refine ⟨46612979631744032207584241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31075319754496021471722827 46612979631744032207584241)
                  ·
                    refine ⟨34959734723808024155688181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46612979631744032207584241 34959734723808024155688181)
                    ·
                      refine ⟨3277475130357002264595767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34959734723808024155688181 3277475130357002264595767)
                      ·
                        rfl

theorem cell23_6382860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_6382860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382860 prefixEnd_6382860 := by exact prefixLift 6382860
  have htrace : WordTrace (prefixWord ++ tailWord_6382860) baseStart_6382860 baseEnd_6382860 := by
    simpa [prefixWord, tailWord_6382860, baseEnd_6382860] using wordTrace_append hprefix tailTrace_6382860
  have hstable : (prefixWord ++ tailWord_6382860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382860).length < 2 ^ (prefixWord ++ tailWord_6382860).sum := by decide
  have hdescent : baseEnd_6382860 < baseStart_6382860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382873 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_6382873 : Nat := 118140960795 + 6382873 * 2 ^ 59
def prefixEnd_6382873 : Nat := 4983230072969 + 3 ^ 40 * 6382873 * 2
def baseEnd_6382873 : Nat := 3277481805605510713733207

theorem tailTrace_6382873 : CollatzResearch.WordTrace tailWord_6382873 prefixEnd_6382873 3277481805605510713733207 := by
  unfold tailWord_6382873
  simp only [CollatzResearch.WordTrace]
  refine ⟨232802503804948703765585273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155201669203299135843723515 232802503804948703765585273)
  ·
    refine ⟨174601877853711527824188955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232802503804948703765585273 174601877853711527824188955)
    ·
      refine ⟨261902816780567291736283433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174601877853711527824188955 261902816780567291736283433)
      ·
        refine ⟨196427112585425468802212575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261902816780567291736283433 196427112585425468802212575)
        ·
          refine ⟨294640668878138203203318863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196427112585425468802212575 294640668878138203203318863)
          ·
            refine ⟨441961003317207304804978295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294640668878138203203318863 441961003317207304804978295)
            ·
              refine ⟨662941504975810957207467443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441961003317207304804978295 662941504975810957207467443)
              ·
                refine ⟨994412257463716435811201165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662941504975810957207467443 994412257463716435811201165)
                ·
                  refine ⟨372904596548893663429200437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994412257463716435811201165 372904596548893663429200437)
                  ·
                    refine ⟨34959805926458780946487541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 372904596548893663429200437 34959805926458780946487541)
                    ·
                      refine ⟨3277481805605510713733207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34959805926458780946487541 3277481805605510713733207)
                      ·
                        rfl

theorem cell23_6382873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_6382873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382873 prefixEnd_6382873 := by exact prefixLift 6382873
  have htrace : WordTrace (prefixWord ++ tailWord_6382873) baseStart_6382873 baseEnd_6382873 := by
    simpa [prefixWord, tailWord_6382873, baseEnd_6382873] using wordTrace_append hprefix tailTrace_6382873
  have hstable : (prefixWord ++ tailWord_6382873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382873).length < 2 ^ (prefixWord ++ tailWord_6382873).sum := by decide
  have hdescent : baseEnd_6382873 < baseStart_6382873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382920 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_6382920 : Nat := 118140960795 + 6382920 * 2 ^ 59
def prefixEnd_6382920 : Nat := 4983230072969 + 3 ^ 40 * 6382920 * 2
def baseEnd_6382920 : Nat := 3277505939196272029845491

theorem tailTrace_6382920 : CollatzResearch.WordTrace tailWord_6382920 prefixEnd_6382920 3277505939196272029845491 := by
  unfold tailWord_6382920
  simp only [CollatzResearch.WordTrace]
  refine ⟨116402109017889215396273107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155202812023852287195030809 116402109017889215396273107)
  ·
    refine ⟨174603163526833823094409661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116402109017889215396273107 174603163526833823094409661)
    ·
      refine ⟨65476186322562683660403623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174603163526833823094409661 65476186322562683660403623)
      ·
        refine ⟨98214279483844025490605435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65476186322562683660403623 98214279483844025490605435)
        ·
          refine ⟨147321419225766038235908153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98214279483844025490605435 147321419225766038235908153)
          ·
            refine ⟨110491064419324528676931115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147321419225766038235908153 110491064419324528676931115)
            ·
              refine ⟨165736596628986793015396673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110491064419324528676931115 165736596628986793015396673)
              ·
                refine ⟨124302447471740094761547505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165736596628986793015396673 124302447471740094761547505)
                ·
                  refine ⟨93226835603805071071160629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124302447471740094761547505 93226835603805071071160629)
                  ·
                    refine ⟨8740015837856725412921309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93226835603805071071160629 8740015837856725412921309)
                    ·
                      refine ⟨3277505939196272029845491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8740015837856725412921309 3277505939196272029845491)
                      ·
                        rfl

theorem cell23_6382920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_6382920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382920 prefixEnd_6382920 := by exact prefixLift 6382920
  have htrace : WordTrace (prefixWord ++ tailWord_6382920) baseStart_6382920 baseEnd_6382920 := by
    simpa [prefixWord, tailWord_6382920, baseEnd_6382920] using wordTrace_append hprefix tailTrace_6382920
  have hstable : (prefixWord ++ tailWord_6382920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382920).length < 2 ^ (prefixWord ++ tailWord_6382920).sum := by decide
  have hdescent : baseEnd_6382920 < baseStart_6382920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382937 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 3]
def baseStart_6382937 : Nat := 118140960795 + 6382937 * 2 ^ 59
def prefixEnd_6382937 : Nat := 4983230072969 + 3 ^ 40 * 6382937 * 2
def baseEnd_6382937 : Nat := 3277514668367398463332913

theorem tailTrace_6382937 : CollatzResearch.WordTrace tailWord_6382937 prefixEnd_6382937 3277514668367398463332913 := by
  unfold tailWord_6382937
  simp only [CollatzResearch.WordTrace]
  refine ⟨232804838076716842695915065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155203225384477895130610043 232804838076716842695915065)
  ·
    refine ⟨174603628557537632021936299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232804838076716842695915065 174603628557537632021936299)
    ·
      refine ⟨261905442836306448032904449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174603628557537632021936299 261905442836306448032904449)
      ·
        refine ⟨196429082127229836024678337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261905442836306448032904449 196429082127229836024678337)
        ·
          refine ⟨147321811595422377018508753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196429082127229836024678337 147321811595422377018508753)
          ·
            refine ⟨110491358696566782763881565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147321811595422377018508753 110491358696566782763881565)
            ·
              refine ⟨41434259511212543536455587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110491358696566782763881565 41434259511212543536455587)
              ·
                refine ⟨62151389266818815304683381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41434259511212543536455587 62151389266818815304683381)
                ·
                  refine ⟨5826692743764263934814067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62151389266818815304683381 5826692743764263934814067)
                  ·
                    refine ⟨8740039115646395902221101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5826692743764263934814067 8740039115646395902221101)
                    ·
                      refine ⟨3277514668367398463332913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8740039115646395902221101 3277514668367398463332913)
                      ·
                        rfl

theorem cell23_6382937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_6382937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382937 prefixEnd_6382937 := by exact prefixLift 6382937
  have htrace : WordTrace (prefixWord ++ tailWord_6382937) baseStart_6382937 baseEnd_6382937 := by
    simpa [prefixWord, tailWord_6382937, baseEnd_6382937] using wordTrace_append hprefix tailTrace_6382937
  have hstable : (prefixWord ++ tailWord_6382937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382937).length < 2 ^ (prefixWord ++ tailWord_6382937).sum := by decide
  have hdescent : baseEnd_6382937 < baseStart_6382937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6382997 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_6382997 : Nat := 118140960795 + 6382997 * 2 ^ 59
def prefixEnd_6382997 : Nat := 4983230072969 + 3 ^ 40 * 6382997 * 2
def baseEnd_6382997 : Nat := 3277545477206668228582637

theorem tailTrace_6382997 : CollatzResearch.WordTrace tailWord_6382997 prefixEnd_6382997 3277545477206668228582637 := by
  unfold tailWord_6382997
  simp only [CollatzResearch.WordTrace]
  refine ⟨232807026456499472943099245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155204684304332981962066163 232807026456499472943099245)
  ·
    refine ⟨87302634921187302353662217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232807026456499472943099245 87302634921187302353662217)
    ·
      refine ⟨65476976190890476765246663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87302634921187302353662217 65476976190890476765246663)
      ·
        refine ⟨98215464286335715147869995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65476976190890476765246663 98215464286335715147869995)
        ·
          refine ⟨147323196429503572721804993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98215464286335715147869995 147323196429503572721804993)
          ·
            refine ⟨110492397322127679541353745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147323196429503572721804993 110492397322127679541353745)
            ·
              refine ⟨82869297991595759656015309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110492397322127679541353745 82869297991595759656015309)
              ·
                refine ⟨31075986746848409871005741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82869297991595759656015309 31075986746848409871005741)
                ·
                  refine ⟨11653495030068153701627153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31075986746848409871005741 11653495030068153701627153)
                  ·
                    refine ⟨8740121272551115276220365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11653495030068153701627153 8740121272551115276220365)
                    ·
                      refine ⟨3277545477206668228582637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8740121272551115276220365 3277545477206668228582637)
                      ·
                        rfl

theorem cell23_6382997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_6382997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6382997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6382997 prefixEnd_6382997 := by exact prefixLift 6382997
  have htrace : WordTrace (prefixWord ++ tailWord_6382997) baseStart_6382997 baseEnd_6382997 := by
    simpa [prefixWord, tailWord_6382997, baseEnd_6382997] using wordTrace_append hprefix tailTrace_6382997
  have hstable : (prefixWord ++ tailWord_6382997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6382997).length < 2 ^ (prefixWord ++ tailWord_6382997).sum := by decide
  have hdescent : baseEnd_6382997 < baseStart_6382997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6382997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383042 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6383042 : Nat := 118140960795 + 6383042 * 2 ^ 59
def prefixEnd_6383042 : Nat := 4983230072969 + 3 ^ 40 * 6383042 * 2
def baseEnd_6383042 : Nat := 1092522861278706850839977

theorem tailTrace_6383042 : CollatzResearch.WordTrace tailWord_6383042 prefixEnd_6383042 1092522861278706850839977 := by
  unfold tailWord_6383042
  simp only [CollatzResearch.WordTrace]
  refine ⟨58202166935334111407121845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155205778494224297085658253 58202166935334111407121845)
  ·
    refine ⟨5456453150187572944417673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58202166935334111407121845 5456453150187572944417673)
    ·
      refine ⟨4092339862640679708313255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5456453150187572944417673 4092339862640679708313255)
      ·
        refine ⟨6138509793961019562469883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092339862640679708313255 6138509793961019562469883)
        ·
          refine ⟨9207764690941529343704825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138509793961019562469883 9207764690941529343704825)
          ·
            refine ⟨6905823518206147007778619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9207764690941529343704825 6905823518206147007778619)
            ·
              refine ⟨10358735277309220511667929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6905823518206147007778619 10358735277309220511667929)
              ·
                refine ⟨7769051457981915383750947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10358735277309220511667929 7769051457981915383750947)
                ·
                  refine ⟨11653577186972873075626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7769051457981915383750947 11653577186972873075626421)
                  ·
                    refine ⟨1092522861278706850839977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11653577186972873075626421 1092522861278706850839977)
                    ·
                      rfl

theorem cell23_6383042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6383042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383042 prefixEnd_6383042 := by exact prefixLift 6383042
  have htrace : WordTrace (prefixWord ++ tailWord_6383042) baseStart_6383042 baseEnd_6383042 := by
    simpa [prefixWord, tailWord_6383042, baseEnd_6383042] using wordTrace_append hprefix tailTrace_6383042
  have hstable : (prefixWord ++ tailWord_6383042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383042).length < 2 ^ (prefixWord ++ tailWord_6383042).sum := by decide
  have hdescent : baseEnd_6383042 < baseStart_6383042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383087 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_6383087 : Nat := 118140960795 + 6383087 * 2 ^ 59
def prefixEnd_6383087 : Nat := 4983230072969 + 3 ^ 40 * 6383087 * 2
def baseEnd_6383087 : Nat := 3277591690465572876457223

theorem tailTrace_6383087 : CollatzResearch.WordTrace tailWord_6383087 prefixEnd_6383087 3277591690465572876457223 := by
  unfold tailWord_6383087
  simp only [CollatzResearch.WordTrace]
  refine ⟨232810309026173418313875515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155206872684115612209250343 232810309026173418313875515)
  ·
    refine ⟨349215463539260127470813273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232810309026173418313875515 349215463539260127470813273)
    ·
      refine ⟨261911597654445095603109955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349215463539260127470813273 261911597654445095603109955)
      ·
        refine ⟨392867396481667643404664933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261911597654445095603109955 392867396481667643404664933)
        ·
          refine ⟨73662636840312683138374675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392867396481667643404664933 73662636840312683138374675)
          ·
            refine ⟨110493955260469024707562013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73662636840312683138374675 110493955260469024707562013)
            ·
              refine ⟨41435233222675884265335755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110493955260469024707562013 41435233222675884265335755)
              ·
                refine ⟨62152849834013826398003633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41435233222675884265335755 62152849834013826398003633)
                ·
                  refine ⟨46614637375510369798502725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62152849834013826398003633 46614637375510369798502725)
                  ·
                    refine ⟨8740244507908194337219261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46614637375510369798502725 8740244507908194337219261)
                    ·
                      refine ⟨3277591690465572876457223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8740244507908194337219261 3277591690465572876457223)
                      ·
                        rfl

theorem cell23_6383087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_6383087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383087 prefixEnd_6383087 := by exact prefixLift 6383087
  have htrace : WordTrace (prefixWord ++ tailWord_6383087) baseStart_6383087 baseEnd_6383087 := by
    simpa [prefixWord, tailWord_6383087, baseEnd_6383087] using wordTrace_append hprefix tailTrace_6383087
  have hstable : (prefixWord ++ tailWord_6383087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383087).length < 2 ^ (prefixWord ++ tailWord_6383087).sum := by decide
  have hdescent : baseEnd_6383087 < baseStart_6383087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383094 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6383094 : Nat := 118140960795 + 6383094 * 2 ^ 59
def prefixEnd_6383094 : Nat := 4983230072969 + 3 ^ 40 * 6383094 * 2
def baseEnd_6383094 : Nat := 1092531761610051449689897

theorem tailTrace_6383094 : CollatzResearch.WordTrace tailWord_6383094 prefixEnd_6383094 1092531761610051449689897 := by
  unfold tailWord_6383094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550660271071753656836271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155207042891432039006253557 14550660271071753656836271)
  ·
    refine ⟨21825990406607630485254407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14550660271071753656836271 21825990406607630485254407)
    ·
      refine ⟨32738985609911445727881611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21825990406607630485254407 32738985609911445727881611)
      ·
        refine ⟨49108478414867168591822417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32738985609911445727881611 49108478414867168591822417)
        ·
          refine ⟨36831358811150376443866813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49108478414867168591822417 36831358811150376443866813)
          ·
            refine ⟨13811759554181391166450055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36831358811150376443866813 13811759554181391166450055)
            ·
              refine ⟨20717639331272086749675083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811759554181391166450055 20717639331272086749675083)
              ·
                refine ⟨31076458996908130124512625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20717639331272086749675083 31076458996908130124512625)
                ·
                  refine ⟨23307344247681097593384469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31076458996908130124512625 23307344247681097593384469)
                  ·
                    refine ⟨1092531761610051449689897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23307344247681097593384469 1092531761610051449689897)
                    ·
                      rfl

theorem cell23_6383094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6383094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383094 prefixEnd_6383094 := by exact prefixLift 6383094
  have htrace : WordTrace (prefixWord ++ tailWord_6383094) baseStart_6383094 baseEnd_6383094 := by
    simpa [prefixWord, tailWord_6383094, baseEnd_6383094] using wordTrace_append hprefix tailTrace_6383094
  have hstable : (prefixWord ++ tailWord_6383094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383094).length < 2 ^ (prefixWord ++ tailWord_6383094).sum := by decide
  have hdescent : baseEnd_6383094 < baseStart_6383094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383101 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_6383101 : Nat := 118140960795 + 6383101 * 2 ^ 59
def prefixEnd_6383101 : Nat := 4983230072969 + 3 ^ 40 * 6383101 * 2
def baseEnd_6383101 : Nat := 3277598879194735821682159

theorem tailTrace_6383101 : CollatzResearch.WordTrace tailWord_6383101 prefixEnd_6383101 3277598879194735821682159 := by
  unfold tailWord_6383101
  simp only [CollatzResearch.WordTrace]
  refine ⟨232810819648122698704885157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155207213098748465803256771 232810819648122698704885157)
  ·
    refine ⟨43652028684023006007165967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232810819648122698704885157 43652028684023006007165967)
    ·
      refine ⟨65478043026034509010748951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43652028684023006007165967 65478043026034509010748951)
      ·
        refine ⟨98217064539051763516123427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65478043026034509010748951 98217064539051763516123427)
        ·
          refine ⟨147325596808577645274185141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98217064539051763516123427 147325596808577645274185141)
          ·
            refine ⟨13811774700804154244454857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147325596808577645274185141 13811774700804154244454857)
            ·
              refine ⟨10358831025603115683341143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13811774700804154244454857 10358831025603115683341143)
              ·
                refine ⟨15538246538404673525011715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10358831025603115683341143 15538246538404673525011715)
                ·
                  refine ⟨23307369807607010287517573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15538246538404673525011715 23307369807607010287517573)
                  ·
                    refine ⟨4370131838926314428909545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23307369807607010287517573 4370131838926314428909545)
                    ·
                      refine ⟨3277598879194735821682159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370131838926314428909545 3277598879194735821682159)
                      ·
                        rfl

theorem cell23_6383101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_6383101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383101 prefixEnd_6383101 := by exact prefixLift 6383101
  have htrace : WordTrace (prefixWord ++ tailWord_6383101) baseStart_6383101 baseEnd_6383101 := by
    simpa [prefixWord, tailWord_6383101, baseEnd_6383101] using wordTrace_append hprefix tailTrace_6383101
  have hstable : (prefixWord ++ tailWord_6383101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383101).length < 2 ^ (prefixWord ++ tailWord_6383101).sum := by decide
  have hdescent : baseEnd_6383101 < baseStart_6383101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383217 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_6383217 : Nat := 118140960795 + 6383217 * 2 ^ 59
def prefixEnd_6383217 : Nat := 4983230072969 + 3 ^ 40 * 6383217 * 2
def baseEnd_6383217 : Nat := 3277658442950657367831625

theorem tailTrace_6383217 : CollatzResearch.WordTrace tailWord_6383217 prefixEnd_6383217 3277658442950657367831625 := by
  unfold tailWord_6383217
  simp only [CollatzResearch.WordTrace]
  refine ⟨232815050515702450516107905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155210033677134967010738603 232815050515702450516107905)
  ·
    refine ⟨174611287886776837887080929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232815050515702450516107905 174611287886776837887080929)
    ·
      refine ⟨130958465915082628415310697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174611287886776837887080929 130958465915082628415310697)
      ·
        refine ⟨98218849436311971311483023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130958465915082628415310697 98218849436311971311483023)
        ·
          refine ⟨147328274154467956967224535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98218849436311971311483023 147328274154467956967224535)
          ·
            refine ⟨220992411231701935450836803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147328274154467956967224535 220992411231701935450836803)
            ·
              refine ⟨331488616847552903176255205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220992411231701935450836803 331488616847552903176255205)
              ·
                refine ⟨62154115658916169345547851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331488616847552903176255205 62154115658916169345547851)
                ·
                  refine ⟨93231173488374254018321777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62154115658916169345547851 93231173488374254018321777)
                  ·
                    refine ⟨69923380116280690513741333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93231173488374254018321777 69923380116280690513741333)
                    ·
                      refine ⟨3277658442950657367831625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69923380116280690513741333 3277658442950657367831625)
                      ·
                        rfl

theorem cell23_6383217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_6383217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383217 prefixEnd_6383217 := by exact prefixLift 6383217
  have htrace : WordTrace (prefixWord ++ tailWord_6383217) baseStart_6383217 baseEnd_6383217 := by
    simpa [prefixWord, tailWord_6383217, baseEnd_6383217] using wordTrace_append hprefix tailTrace_6383217
  have hstable : (prefixWord ++ tailWord_6383217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383217).length < 2 ^ (prefixWord ++ tailWord_6383217).sum := by decide
  have hdescent : baseEnd_6383217 < baseStart_6383217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383301 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_6383301 : Nat := 118140960795 + 6383301 * 2 ^ 59
def prefixEnd_6383301 : Nat := 4983230072969 + 3 ^ 40 * 6383301 * 2
def baseEnd_6383301 : Nat := 3277701575325635039181239

theorem tailTrace_6383301 : CollatzResearch.WordTrace tailWord_6383301 prefixEnd_6383301 3277701575325635039181239 := by
  unfold tailWord_6383301
  simp only [CollatzResearch.WordTrace]
  refine ⟨232818114247398132862165757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155212076164932088574777171 232818114247398132862165757)
  ·
    refine ⟨87306792842774299823312159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232818114247398132862165757 87306792842774299823312159)
    ·
      refine ⟨130960189264161449734968239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87306792842774299823312159 130960189264161449734968239)
      ·
        refine ⟨196440283896242174602452359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130960189264161449734968239 196440283896242174602452359)
        ·
          refine ⟨294660425844363261903678539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196440283896242174602452359 294660425844363261903678539)
          ·
            refine ⟨441990638766544892855517809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294660425844363261903678539 441990638766544892855517809)
            ·
              refine ⟨331492979074908669641638357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441990638766544892855517809 331492979074908669641638357)
              ·
                refine ⟨7769366697068171944725899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 331492979074908669641638357 7769366697068171944725899)
                ·
                  refine ⟨11654050045602257917088849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7769366697068171944725899 11654050045602257917088849)
                  ·
                    refine ⟨8740537534201693437816637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11654050045602257917088849 8740537534201693437816637)
                    ·
                      refine ⟨3277701575325635039181239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8740537534201693437816637 3277701575325635039181239)
                      ·
                        rfl

theorem cell23_6383301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_6383301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383301 prefixEnd_6383301 := by exact prefixLift 6383301
  have htrace : WordTrace (prefixWord ++ tailWord_6383301) baseStart_6383301 baseEnd_6383301 := by
    simpa [prefixWord, tailWord_6383301, baseEnd_6383301] using wordTrace_append hprefix tailTrace_6383301
  have hstable : (prefixWord ++ tailWord_6383301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383301).length < 2 ^ (prefixWord ++ tailWord_6383301).sum := by decide
  have hdescent : baseEnd_6383301 < baseStart_6383301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383308 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_6383308 : Nat := 118140960795 + 6383308 * 2 ^ 59
def prefixEnd_6383308 : Nat := 4983230072969 + 3 ^ 40 * 6383308 * 2
def baseEnd_6383308 : Nat := 1092568389896738837264569

theorem tailTrace_6383308 : CollatzResearch.WordTrace tailWord_6383308 prefixEnd_6383308 1092568389896738837264569 := by
  unfold tailWord_6383308
  simp only [CollatzResearch.WordTrace]
  refine ⟨116409184779186386528835289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155212246372248515371780385 116409184779186386528835289)
  ·
    refine ⟨87306888584389789896626467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116409184779186386528835289 87306888584389789896626467)
    ·
      refine ⟨130960332876584684844939701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87306888584389789896626467 130960332876584684844939701)
      ·
        refine ⟨12277531207179814204213097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130960332876584684844939701 12277531207179814204213097)
        ·
          refine ⟨9208148405384860653159823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12277531207179814204213097 9208148405384860653159823)
          ·
            refine ⟨13812222608077290979739735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208148405384860653159823 13812222608077290979739735)
            ·
              refine ⟨20718333912115936469609603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13812222608077290979739735 20718333912115936469609603)
              ·
                refine ⟨31077500868173904704414405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20718333912115936469609603 31077500868173904704414405)
                ·
                  refine ⟨5827031412782607132077701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31077500868173904704414405 5827031412782607132077701)
                  ·
                    refine ⟨1092568389896738837264569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827031412782607132077701 1092568389896738837264569)
                    ·
                      rfl

theorem cell23_6383308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_6383308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383308 prefixEnd_6383308 := by exact prefixLift 6383308
  have htrace : WordTrace (prefixWord ++ tailWord_6383308) baseStart_6383308 baseEnd_6383308 := by
    simpa [prefixWord, tailWord_6383308, baseEnd_6383308] using wordTrace_append hprefix tailTrace_6383308
  have hstable : (prefixWord ++ tailWord_6383308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383308).length < 2 ^ (prefixWord ++ tailWord_6383308).sum := by decide
  have hdescent : baseEnd_6383308 < baseStart_6383308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383325 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6383325 : Nat := 118140960795 + 6383325 * 2 ^ 59
def prefixEnd_6383325 : Nat := 4983230072969 + 3 ^ 40 * 6383325 * 2
def baseEnd_6383325 : Nat := 1092571299620447648427043

theorem tailTrace_6383325 : CollatzResearch.WordTrace tailWord_6383325 prefixEnd_6383325 1092571299620447648427043 := by
  unfold tailWord_6383325
  simp only [CollatzResearch.WordTrace]
  refine ⟨232818989599311184961039429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155212659732874123307359619 232818989599311184961039429)
  ·
    refine ⟨43653560549870847180194893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232818989599311184961039429 43653560549870847180194893)
    ·
      refine ⟨16370085206201567692573085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43653560549870847180194893 16370085206201567692573085)
      ·
        refine ⟨6138781952325587884714907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16370085206201567692573085 6138781952325587884714907)
        ·
          refine ⟨9208172928488381827072361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138781952325587884714907 9208172928488381827072361)
          ·
            refine ⟨6906129696366286370304271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9208172928488381827072361 6906129696366286370304271)
            ·
              refine ⟨10359194544549429555456407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6906129696366286370304271 10359194544549429555456407)
              ·
                refine ⟨15538791816824144333184611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10359194544549429555456407 15538791816824144333184611)
                ·
                  refine ⟨23308187725236216499776917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15538791816824144333184611 23308187725236216499776917)
                  ·
                    refine ⟨1092571299620447648427043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23308187725236216499776917 1092571299620447648427043)
                    ·
                      rfl

theorem cell23_6383325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6383325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383325 prefixEnd_6383325 := by exact prefixLift 6383325
  have htrace : WordTrace (prefixWord ++ tailWord_6383325) baseStart_6383325 baseEnd_6383325 := by
    simpa [prefixWord, tailWord_6383325, baseEnd_6383325] using wordTrace_append hprefix tailTrace_6383325
  have hstable : (prefixWord ++ tailWord_6383325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383325).length < 2 ^ (prefixWord ++ tailWord_6383325).sum := by decide
  have hdescent : baseEnd_6383325 < baseStart_6383325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383354 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_6383354 : Nat := 118140960795 + 6383354 * 2 ^ 59
def prefixEnd_6383354 : Nat := 4983230072969 + 3 ^ 40 * 6383354 * 2
def baseEnd_6383354 : Nat := 3277728789800323331818495

theorem tailTrace_6383354 : CollatzResearch.WordTrace tailWord_6383354 prefixEnd_6383354 3277728789800323331818495 := by
  unfold tailWord_6383354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58205011829051530728461279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155213364877470748609230077 58205011829051530728461279)
  ·
    refine ⟨87307517743577296092691919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58205011829051530728461279 87307517743577296092691919)
    ·
      refine ⟨130961276615365944139037879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87307517743577296092691919 130961276615365944139037879)
      ·
        refine ⟨196441914923048916208556819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130961276615365944139037879 196441914923048916208556819)
        ·
          refine ⟨294662872384573374312835229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196441914923048916208556819 294662872384573374312835229)
          ·
            refine ⟨110498577144215015367313211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294662872384573374312835229 110498577144215015367313211)
            ·
              refine ⟨165747865716322523050969817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110498577144215015367313211 165747865716322523050969817)
              ·
                refine ⟨124310899287241892288227363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165747865716322523050969817 124310899287241892288227363)
                ·
                  refine ⟨186466348930862838432341045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124310899287241892288227363 186466348930862838432341045)
                  ·
                    refine ⟨17481220212268391103031973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186466348930862838432341045 17481220212268391103031973)
                    ·
                      refine ⟨3277728789800323331818495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17481220212268391103031973 3277728789800323331818495)
                      ·
                        rfl

theorem cell23_6383354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_6383354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383354 prefixEnd_6383354 := by exact prefixLift 6383354
  have htrace : WordTrace (prefixWord ++ tailWord_6383354) baseStart_6383354 baseEnd_6383354 := by
    simpa [prefixWord, tailWord_6383354, baseEnd_6383354] using wordTrace_append hprefix tailTrace_6383354
  have hstable : (prefixWord ++ tailWord_6383354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383354).length < 2 ^ (prefixWord ++ tailWord_6383354).sum := by decide
  have hdescent : baseEnd_6383354 < baseStart_6383354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383388 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_6383388 : Nat := 118140960795 + 6383388 * 2 ^ 59
def prefixEnd_6383388 : Nat := 4983230072969 + 3 ^ 40 * 6383388 * 2
def baseEnd_6383388 : Nat := 3277746248142576198793339

theorem tailTrace_6383388 : CollatzResearch.WordTrace tailWord_6383388 prefixEnd_6383388 3277746248142576198793339 := by
  unfold tailWord_6383388
  simp only [CollatzResearch.WordTrace]
  refine ⟨116410643699041473360291409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155214191598721964480388545 116410643699041473360291409)
  ·
    refine ⟨87307982774281105020218557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116410643699041473360291409 87307982774281105020218557)
    ·
      refine ⟨32740493540355414382581959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87307982774281105020218557 32740493540355414382581959)
      ·
        refine ⟨49110740310533121573872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32740493540355414382581959 49110740310533121573872939)
        ·
          refine ⟨73666110465799682360809409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49110740310533121573872939 73666110465799682360809409)
          ·
            refine ⟨55249582849349761770607057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73666110465799682360809409 55249582849349761770607057)
            ·
              refine ⟨41437187137012321327955293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55249582849349761770607057 41437187137012321327955293)
              ·
                refine ⟨15538945176379620497983235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41437187137012321327955293 15538945176379620497983235)
                ·
                  refine ⟨23308417764569430746974853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15538945176379620497983235 23308417764569430746974853)
                  ·
                    refine ⟨4370328330856768265057785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23308417764569430746974853 4370328330856768265057785)
                    ·
                      refine ⟨3277746248142576198793339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370328330856768265057785 3277746248142576198793339)
                      ·
                        rfl

theorem cell23_6383388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_6383388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383388 prefixEnd_6383388 := by exact prefixLift 6383388
  have htrace : WordTrace (prefixWord ++ tailWord_6383388) baseStart_6383388 baseEnd_6383388 := by
    simpa [prefixWord, tailWord_6383388, baseEnd_6383388] using wordTrace_append hprefix tailTrace_6383388
  have hstable : (prefixWord ++ tailWord_6383388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383388).length < 2 ^ (prefixWord ++ tailWord_6383388).sum := by decide
  have hdescent : baseEnd_6383388 < baseStart_6383388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383422 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_6383422 : Nat := 118140960795 + 6383422 * 2 ^ 59
def prefixEnd_6383422 : Nat := 4983230072969 + 3 ^ 40 * 6383422 * 2
def baseEnd_6383422 : Nat := 3277763706484829065768183

theorem tailTrace_6383422 : CollatzResearch.WordTrace tailWord_6383422 prefixEnd_6383422 3277763706484829065768183 := by
  unfold tailWord_6383422
  simp only [CollatzResearch.WordTrace]
  refine ⟨29102815934994971315915065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155215018319973180351547013 29102815934994971315915065)
  ·
    refine ⟨21827111951246228486936299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29102815934994971315915065 21827111951246228486936299)
    ·
      refine ⟨32740667926869342730404449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21827111951246228486936299 32740667926869342730404449)
      ·
        refine ⟨24555500945152007047803337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32740667926869342730404449 24555500945152007047803337)
        ·
          refine ⟨18416625708864005285852503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24555500945152007047803337 18416625708864005285852503)
          ·
            refine ⟨27624938563296007928778755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18416625708864005285852503 27624938563296007928778755)
            ·
              refine ⟨41437407844944011893168133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27624938563296007928778755 41437407844944011893168133)
              ·
                refine ⟨7769513970927002229969025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41437407844944011893168133 7769513970927002229969025)
                ·
                  refine ⟨5827135478195251672476769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7769513970927002229969025 5827135478195251672476769)
                  ·
                    refine ⟨4370351608646438754357577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827135478195251672476769 4370351608646438754357577)
                    ·
                      refine ⟨3277763706484829065768183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370351608646438754357577 3277763706484829065768183)
                      ·
                        rfl

theorem cell23_6383422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_6383422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383422 prefixEnd_6383422 := by exact prefixLift 6383422
  have htrace : WordTrace (prefixWord ++ tailWord_6383422) baseStart_6383422 baseEnd_6383422 := by
    simpa [prefixWord, tailWord_6383422, baseEnd_6383422] using wordTrace_append hprefix tailTrace_6383422
  have hstable : (prefixWord ++ tailWord_6383422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383422).length < 2 ^ (prefixWord ++ tailWord_6383422).sum := by decide
  have hdescent : baseEnd_6383422 < baseStart_6383422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383424 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_6383424 : Nat := 118140960795 + 6383424 * 2 ^ 59
def prefixEnd_6383424 : Nat := 4983230072969 + 3 ^ 40 * 6383424 * 2
def baseEnd_6383424 : Nat := 1092588244482046019314391

theorem tailTrace_6383424 : CollatzResearch.WordTrace tailWord_6383424 prefixEnd_6383424 1092588244482046019314391 := by
  unfold tailWord_6383424
  simp only [CollatzResearch.WordTrace]
  refine ⟨116411300212976262434446663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155215066950635016579262217 116411300212976262434446663)
  ·
    refine ⟨174616950319464393651669995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116411300212976262434446663 174616950319464393651669995)
    ·
      refine ⟨261925425479196590477504993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174616950319464393651669995 261925425479196590477504993)
      ·
        refine ⟨196444069109397442858128745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261925425479196590477504993 196444069109397442858128745)
        ·
          refine ⟨147333051832048082143596559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196444069109397442858128745 147333051832048082143596559)
          ·
            refine ⟨220999577748072123215394839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147333051832048082143596559 220999577748072123215394839)
            ·
              refine ⟨331499366622108184823092259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220999577748072123215394839 331499366622108184823092259)
              ·
                refine ⟨497249049933162277234638389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331499366622108184823092259 497249049933162277234638389)
                ·
                  refine ⟨46617098431233963490747349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497249049933162277234638389 46617098431233963490747349)
                  ·
                    refine ⟨1092588244482046019314391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46617098431233963490747349 1092588244482046019314391)
                    ·
                      rfl

theorem cell23_6383424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_6383424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383424 prefixEnd_6383424 := by exact prefixLift 6383424
  have htrace : WordTrace (prefixWord ++ tailWord_6383424) baseStart_6383424 baseEnd_6383424 := by
    simpa [prefixWord, tailWord_6383424, baseEnd_6383424] using wordTrace_append hprefix tailTrace_6383424
  have hstable : (prefixWord ++ tailWord_6383424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383424).length < 2 ^ (prefixWord ++ tailWord_6383424).sum := by decide
  have hdescent : baseEnd_6383424 < baseStart_6383424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383458 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6383458 : Nat := 118140960795 + 6383458 * 2 ^ 59
def prefixEnd_6383458 : Nat := 4983230072969 + 3 ^ 40 * 6383458 * 2
def baseEnd_6383458 : Nat := 1092594063929463641639339

theorem tailTrace_6383458 : CollatzResearch.WordTrace tailWord_6383458 prefixEnd_6383458 1092594063929463641639339 := by
  unfold tailWord_6383458
  simp only [CollatzResearch.WordTrace]
  refine ⟨58205960126957337168907757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155215893671886232450420685 58205960126957337168907757)
  ·
    refine ⟨21827235047609001438340409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58205960126957337168907757 21827235047609001438340409)
    ·
      refine ⟨16370426285706751078755307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21827235047609001438340409 16370426285706751078755307)
      ·
        refine ⟨24555639428560126618132961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16370426285706751078755307 24555639428560126618132961)
        ·
          refine ⟨18416729571420094963599721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24555639428560126618132961 18416729571420094963599721)
          ·
            refine ⟨13812547178565071222699791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18416729571420094963599721 13812547178565071222699791)
            ·
              refine ⟨20718820767847606834049687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13812547178565071222699791 20718820767847606834049687)
              ·
                refine ⟨31078231151771410251074531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20718820767847606834049687 31078231151771410251074531)
                ·
                  refine ⟨46617346727657115376611797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31078231151771410251074531 46617346727657115376611797)
                  ·
                    refine ⟨1092594063929463641639339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46617346727657115376611797 1092594063929463641639339)
                    ·
                      rfl

theorem cell23_6383458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6383458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383458 prefixEnd_6383458 := by exact prefixLift 6383458
  have htrace : WordTrace (prefixWord ++ tailWord_6383458) baseStart_6383458 baseEnd_6383458 := by
    simpa [prefixWord, tailWord_6383458, baseEnd_6383458] using wordTrace_append hprefix tailTrace_6383458
  have hstable : (prefixWord ++ tailWord_6383458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383458).length < 2 ^ (prefixWord ++ tailWord_6383458).sum := by decide
  have hdescent : baseEnd_6383458 < baseStart_6383458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383488 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 3, 4]
def baseStart_6383488 : Nat := 118140960795 + 6383488 * 2 ^ 59
def prefixEnd_6383488 : Nat := 4983230072969 + 3 ^ 40 * 6383488 * 2
def baseEnd_6383488 : Nat := 1092599198736008602514293

theorem tailTrace_6383488 : CollatzResearch.WordTrace tailWord_6383488 prefixEnd_6383488 1092599198736008602514293 := by
  unfold tailWord_6383488
  simp only [CollatzResearch.WordTrace]
  refine ⟨116412467348860331899611559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155216623131813775866148745 116412467348860331899611559)
  ·
    refine ⟨174618701023290497849417339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116412467348860331899611559 174618701023290497849417339)
    ·
      refine ⟨261928051534935746774126009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174618701023290497849417339 261928051534935746774126009)
      ·
        refine ⟨196446038651201810080594507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261928051534935746774126009 196446038651201810080594507)
        ·
          refine ⟨294669057976802715120891761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196446038651201810080594507 294669057976802715120891761)
          ·
            refine ⟨221001793482602036340668821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294669057976802715120891761 221001793482602036340668821)
            ·
              refine ⟨10359459069496970453468851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221001793482602036340668821 10359459069496970453468851)
              ·
                refine ⟨15539188604245455680203277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10359459069496970453468851 15539188604245455680203277)
                ·
                  refine ⟨5827195726592045880076229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15539188604245455680203277 5827195726592045880076229)
                  ·
                    refine ⟨1092599198736008602514293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827195726592045880076229 1092599198736008602514293)
                    ·
                      rfl

theorem cell23_6383488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_6383488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383488 prefixEnd_6383488 := by exact prefixLift 6383488
  have htrace : WordTrace (prefixWord ++ tailWord_6383488) baseStart_6383488 baseEnd_6383488 := by
    simpa [prefixWord, tailWord_6383488, baseEnd_6383488] using wordTrace_append hprefix tailTrace_6383488
  have hstable : (prefixWord ++ tailWord_6383488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383488).length < 2 ^ (prefixWord ++ tailWord_6383488).sum := by decide
  have hdescent : baseEnd_6383488 < baseStart_6383488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383568 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 6, 2]
def baseStart_6383568 : Nat := 118140960795 + 6383568 * 2 ^ 59
def prefixEnd_6383568 : Nat := 4983230072969 + 3 ^ 40 * 6383568 * 2
def baseEnd_6383568 : Nat := 3277838674660385494542511

theorem tailTrace_6383568 : CollatzResearch.WordTrace tailWord_6383568 prefixEnd_6383568 3277838674660385494542511 := by
  unfold tailWord_6383568
  simp only [CollatzResearch.WordTrace]
  refine ⟨116413926268715418731067679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155218568358287224974756905 116413926268715418731067679)
  ·
    refine ⟨174620889403073128096601519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116413926268715418731067679 174620889403073128096601519)
    ·
      refine ⟨261931334104609692144902279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174620889403073128096601519 261931334104609692144902279)
      ·
        refine ⟨392897001156914538217353419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261931334104609692144902279 392897001156914538217353419)
        ·
          refine ⟨589345501735371807326030129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392897001156914538217353419 589345501735371807326030129)
          ·
            refine ⟨442009126301528855494522597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589345501735371807326030129 442009126301528855494522597)
            ·
              refine ⟨82876711181536660405222987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442009126301528855494522597 82876711181536660405222987)
              ·
                refine ⟨124315066772304990607834481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82876711181536660405222987 124315066772304990607834481)
                ·
                  refine ⟨93236300079228742955875861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124315066772304990607834481 93236300079228742955875861)
                  ·
                    refine ⟨4370451566213847326056681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93236300079228742955875861 4370451566213847326056681)
                    ·
                      refine ⟨3277838674660385494542511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370451566213847326056681 3277838674660385494542511)
                      ·
                        rfl

theorem cell23_6383568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 6, 2].length) (baseStart_6383568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383568 prefixEnd_6383568 := by exact prefixLift 6383568
  have htrace : WordTrace (prefixWord ++ tailWord_6383568) baseStart_6383568 baseEnd_6383568 := by
    simpa [prefixWord, tailWord_6383568, baseEnd_6383568] using wordTrace_append hprefix tailTrace_6383568
  have hstable : (prefixWord ++ tailWord_6383568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383568).length < 2 ^ (prefixWord ++ tailWord_6383568).sum := by decide
  have hdescent : baseEnd_6383568 < baseStart_6383568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383572 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_6383572 : Nat := 118140960795 + 6383572 * 2 ^ 59
def prefixEnd_6383572 : Nat := 4983230072969 + 3 ^ 40 * 6383572 * 2
def baseEnd_6383572 : Nat := 3277840728583003478892493

theorem tailTrace_6383572 : CollatzResearch.WordTrace tailWord_6383572 prefixEnd_6383572 3277840728583003478892493 := by
  unfold tailWord_6383572
  simp only [CollatzResearch.WordTrace]
  refine ⟨116413999214708173072640485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155218665619610897430187313 116413999214708173072640485)
  ·
    refine ⟨21827624852757782451120091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116413999214708173072640485 21827624852757782451120091)
    ·
      refine ⟨32741437279136673676680137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21827624852757782451120091 32741437279136673676680137)
      ·
        refine ⟨24556077959352505257510103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32741437279136673676680137 24556077959352505257510103)
        ·
          refine ⟨36834116939028757886265155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24556077959352505257510103 36834116939028757886265155)
          ·
            refine ⟨55251175408543136829397733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36834116939028757886265155 55251175408543136829397733)
            ·
              refine ⟨10359595389101838155512075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55251175408543136829397733 10359595389101838155512075)
              ·
                refine ⟨15539393083652757233268113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10359595389101838155512075 15539393083652757233268113)
                ·
                  refine ⟨11654544812739567924951085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15539393083652757233268113 11654544812739567924951085)
                  ·
                    refine ⟨4370454304777337971856657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11654544812739567924951085 4370454304777337971856657)
                    ·
                      refine ⟨3277840728583003478892493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370454304777337971856657 3277840728583003478892493)
                      ·
                        rfl

theorem cell23_6383572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_6383572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383572 prefixEnd_6383572 := by exact prefixLift 6383572
  have htrace : WordTrace (prefixWord ++ tailWord_6383572) baseStart_6383572 baseEnd_6383572 := by
    simpa [prefixWord, tailWord_6383572, baseEnd_6383572] using wordTrace_append hprefix tailTrace_6383572
  have hstable : (prefixWord ++ tailWord_6383572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383572).length < 2 ^ (prefixWord ++ tailWord_6383572).sum := by decide
  have hdescent : baseEnd_6383572 < baseStart_6383572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383591 : List Nat := [1, 1, 5, 2, 14]
def baseStart_6383591 : Nat := 118140960795 + 6383591 * 2 ^ 59
def prefixEnd_6383591 : Nat := 4983230072969 + 3 ^ 40 * 6383591 * 2
def baseEnd_6383591 : Nat := 4496365548306500554945

theorem tailTrace_6383591 : CollatzResearch.WordTrace tailWord_6383591 prefixEnd_6383591 4496365548306500554945 := by
  unfold tailWord_6383591
  simp only [CollatzResearch.WordTrace]
  refine ⟨232828691416347512390222627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155219127610898341593481751 232828691416347512390222627)
  ·
    refine ⟨349243037124521268585333941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232828691416347512390222627 349243037124521268585333941)
    ·
      refine ⟨32741534730423868929875057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 349243037124521268585333941 32741534730423868929875057)
      ·
        refine ⟨24556151047817901697406293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32741534730423868929875057 24556151047817901697406293)
        ·
          refine ⟨4496365548306500554945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 24556151047817901697406293 4496365548306500554945)
          ·
            rfl

theorem cell23_6383591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 14].length) (baseStart_6383591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383591 prefixEnd_6383591 := by exact prefixLift 6383591
  have htrace : WordTrace (prefixWord ++ tailWord_6383591) baseStart_6383591 baseEnd_6383591 := by
    simpa [prefixWord, tailWord_6383591, baseEnd_6383591] using wordTrace_append hprefix tailTrace_6383591
  have hstable : (prefixWord ++ tailWord_6383591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383591).length < 2 ^ (prefixWord ++ tailWord_6383591).sum := by decide
  have hdescent : baseEnd_6383591 < baseStart_6383591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383611 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_6383611 : Nat := 118140960795 + 6383611 * 2 ^ 59
def prefixEnd_6383611 : Nat := 4983230072969 + 3 ^ 40 * 6383611 * 2
def baseEnd_6383611 : Nat := 3277860754328528826304813

theorem tailTrace_6383611 : CollatzResearch.WordTrace tailWord_6383611 prefixEnd_6383611 3277860754328528826304813 := by
  unfold tailWord_6383611
  simp only [CollatzResearch.WordTrace]
  refine ⟨232829420876275055805950687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155219613917516703870633791 232829420876275055805950687)
  ·
    refine ⟨349244131314412583708926031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232829420876275055805950687 349244131314412583708926031)
    ·
      refine ⟨523866196971618875563389047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349244131314412583708926031 523866196971618875563389047)
      ·
        refine ⟨785799295457428313345083571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523866196971618875563389047 785799295457428313345083571)
        ·
          refine ⟨1178698943186142470017625357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785799295457428313345083571 1178698943186142470017625357)
          ·
            refine ⟨442012103694803426256609509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1178698943186142470017625357 442012103694803426256609509)
            ·
              refine ⟨82877269442775642423114283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442012103694803426256609509 82877269442775642423114283)
              ·
                refine ⟨124315904164163463634671425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82877269442775642423114283 124315904164163463634671425)
                ·
                  refine ⟨93236928123122597726003569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124315904164163463634671425 93236928123122597726003569)
                  ·
                    refine ⟨69927696092341948294502677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93236928123122597726003569 69927696092341948294502677)
                    ·
                      refine ⟨3277860754328528826304813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69927696092341948294502677 3277860754328528826304813)
                      ·
                        rfl

theorem cell23_6383611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_6383611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383611 prefixEnd_6383611 := by exact prefixLift 6383611
  have htrace : WordTrace (prefixWord ++ tailWord_6383611) baseStart_6383611 baseEnd_6383611 := by
    simpa [prefixWord, tailWord_6383611, baseEnd_6383611] using wordTrace_append hprefix tailTrace_6383611
  have hstable : (prefixWord ++ tailWord_6383611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383611).length < 2 ^ (prefixWord ++ tailWord_6383611).sum := by decide
  have hdescent : baseEnd_6383611 < baseStart_6383611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383688 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_6383688 : Nat := 118140960795 + 6383688 * 2 ^ 59
def prefixEnd_6383688 : Nat := 4983230072969 + 3 ^ 40 * 6383688 * 2
def baseEnd_6383688 : Nat := 3277900292338925025041959

theorem tailTrace_6383688 : CollatzResearch.WordTrace tailWord_6383688 prefixEnd_6383688 3277900292338925025041959 := by
  unfold tailWord_6383688
  simp only [CollatzResearch.WordTrace]
  refine ⟨116416114648498048978251859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155221486197997398637669145 116416114648498048978251859)
  ·
    refine ⟨174624171972747073467377789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116416114648498048978251859 174624171972747073467377789)
    ·
      refine ⟨65484064489780152550266671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174624171972747073467377789 65484064489780152550266671)
      ·
        refine ⟨98226096734670228825400007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65484064489780152550266671 98226096734670228825400007)
        ·
          refine ⟨147339145102005343238100011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98226096734670228825400007 147339145102005343238100011)
          ·
            refine ⟨221008717653008014857150017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147339145102005343238100011 221008717653008014857150017)
            ·
              refine ⟨165756538239756011142862513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221008717653008014857150017 165756538239756011142862513)
              ·
                refine ⟨124317403679817008357146885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165756538239756011142862513 124317403679817008357146885)
                ·
                  refine ⟨23309513189965689066965041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124317403679817008357146885 23309513189965689066965041)
                  ·
                    refine ⟨17482134892474266800223781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23309513189965689066965041 17482134892474266800223781)
                    ·
                      refine ⟨3277900292338925025041959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17482134892474266800223781 3277900292338925025041959)
                      ·
                        rfl

theorem cell23_6383688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_6383688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383688 prefixEnd_6383688 := by exact prefixLift 6383688
  have htrace : WordTrace (prefixWord ++ tailWord_6383688) baseStart_6383688 baseEnd_6383688 := by
    simpa [prefixWord, tailWord_6383688, baseEnd_6383688] using wordTrace_append hprefix tailTrace_6383688
  have hstable : (prefixWord ++ tailWord_6383688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383688).length < 2 ^ (prefixWord ++ tailWord_6383688).sum := by decide
  have hdescent : baseEnd_6383688 < baseStart_6383688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383692 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6383692 : Nat := 118140960795 + 6383692 * 2 ^ 59
def prefixEnd_6383692 : Nat := 4983230072969 + 3 ^ 40 * 6383692 * 2
def baseEnd_6383692 : Nat := 3277902346261543009391941

theorem tailTrace_6383692 : CollatzResearch.WordTrace tailWord_6383692 prefixEnd_6383692 3277902346261543009391941 := by
  unfold tailWord_6383692
  simp only [CollatzResearch.WordTrace]
  refine ⟨116416187594490803319824665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155221583459321071093099553 116416187594490803319824665)
  ·
    refine ⟨87312140695868102489868499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116416187594490803319824665 87312140695868102489868499)
    ·
      refine ⟨130968211043802153734802749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87312140695868102489868499 130968211043802153734802749)
      ·
        refine ⟨49113079141425807650551031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130968211043802153734802749 49113079141425807650551031)
        ·
          refine ⟨73669618712138711475826547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49113079141425807650551031 73669618712138711475826547)
          ·
            refine ⟨110504428068208067213739821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73669618712138711475826547 110504428068208067213739821)
            ·
              refine ⟨41439160525578025205152433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110504428068208067213739821 41439160525578025205152433)
              ·
                refine ⟨31079370394183518903864325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41439160525578025205152433 31079370394183518903864325)
                ·
                  refine ⟨5827381948909409794474561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31079370394183518903864325 5827381948909409794474561)
                  ·
                    refine ⟨4370536461682057345855921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827381948909409794474561 4370536461682057345855921)
                    ·
                      refine ⟨3277902346261543009391941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370536461682057345855921 3277902346261543009391941)
                      ·
                        rfl

theorem cell23_6383692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6383692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383692 prefixEnd_6383692 := by exact prefixLift 6383692
  have htrace : WordTrace (prefixWord ++ tailWord_6383692) baseStart_6383692 baseEnd_6383692 := by
    simpa [prefixWord, tailWord_6383692, baseEnd_6383692] using wordTrace_append hprefix tailTrace_6383692
  have hstable : (prefixWord ++ tailWord_6383692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383692).length < 2 ^ (prefixWord ++ tailWord_6383692).sum := by decide
  have hdescent : baseEnd_6383692 < baseStart_6383692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383715 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 5]
def baseStart_6383715 : Nat := 118140960795 + 6383715 * 2 ^ 59
def prefixEnd_6383715 : Nat := 4983230072969 + 3 ^ 40 * 6383715 * 2
def baseEnd_6383715 : Nat := 364212684035177379933815

theorem tailTrace_6383715 : CollatzResearch.WordTrace tailWord_6383715 prefixEnd_6383715 364212684035177379933815 := by
  unfold tailWord_6383715
  simp only [CollatzResearch.WordTrace]
  refine ⟨232833214067898281567736599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155222142711932187711824399 232833214067898281567736599)
  ·
    refine ⟨349249821101847422351604899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232833214067898281567736599 349249821101847422351604899)
    ·
      refine ⟨523874731652771133527407349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349249821101847422351604899 523874731652771133527407349)
      ·
        refine ⟨49113256092447293768194439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 523874731652771133527407349 49113256092447293768194439)
        ·
          refine ⟨73669884138670940652291659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49113256092447293768194439 73669884138670940652291659)
          ·
            refine ⟨110504826208006410978437489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73669884138670940652291659 110504826208006410978437489)
            ·
              refine ⟨82878619656004808233828117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110504826208006410978437489 82878619656004808233828117)
              ·
                refine ⟨3884935296375225385960693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82878619656004808233828117 3884935296375225385960693)
                ·
                  refine ⟨364212684035177379933815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3884935296375225385960693 364212684035177379933815)
                  ·
                    rfl

theorem cell23_6383715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 5].length) (baseStart_6383715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383715 prefixEnd_6383715 := by exact prefixLift 6383715
  have htrace : WordTrace (prefixWord ++ tailWord_6383715) baseStart_6383715 baseEnd_6383715 := by
    simpa [prefixWord, tailWord_6383715, baseEnd_6383715] using wordTrace_append hprefix tailTrace_6383715
  have hstable : (prefixWord ++ tailWord_6383715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383715).length < 2 ^ (prefixWord ++ tailWord_6383715).sum := by decide
  have hdescent : baseEnd_6383715 < baseStart_6383715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383725 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_6383725 : Nat := 118140960795 + 6383725 * 2 ^ 59
def prefixEnd_6383725 : Nat := 4983230072969 + 3 ^ 40 * 6383725 * 2
def baseEnd_6383725 : Nat := 3277919291123141380279289

theorem tailTrace_6383725 : CollatzResearch.WordTrace tailWord_6383725 prefixEnd_6383725 3277919291123141380279289 := by
  unfold tailWord_6383725
  simp only [CollatzResearch.WordTrace]
  refine ⟨232833578797862053275600629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155222385865241368850400419 232833578797862053275600629)
  ·
    refine ⟨21828148012299567494587559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232833578797862053275600629 21828148012299567494587559)
    ·
      refine ⟨32742222018449351241881339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21828148012299567494587559 32742222018449351241881339)
      ·
        refine ⟨49113333027674026862822009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32742222018449351241881339 49113333027674026862822009)
        ·
          refine ⟨36834999770755520147116507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49113333027674026862822009 36834999770755520147116507)
          ·
            refine ⟨55252499656133280220674761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36834999770755520147116507 55252499656133280220674761)
            ·
              refine ⟨41439374742099960165506071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55252499656133280220674761 41439374742099960165506071)
              ·
                refine ⟨62159062113149940248259107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41439374742099960165506071 62159062113149940248259107)
                ·
                  refine ⟨93238593169724910372388661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62159062113149940248259107 93238593169724910372388661)
                  ·
                    refine ⟨8741118109661710347411437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93238593169724910372388661 8741118109661710347411437)
                    ·
                      refine ⟨3277919291123141380279289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741118109661710347411437 3277919291123141380279289)
                      ·
                        rfl

theorem cell23_6383725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_6383725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383725 prefixEnd_6383725 := by exact prefixLift 6383725
  have htrace : WordTrace (prefixWord ++ tailWord_6383725) baseStart_6383725 baseEnd_6383725 := by
    simpa [prefixWord, tailWord_6383725, baseEnd_6383725] using wordTrace_append hprefix tailTrace_6383725
  have hstable : (prefixWord ++ tailWord_6383725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383725).length < 2 ^ (prefixWord ++ tailWord_6383725).sum := by decide
  have hdescent : baseEnd_6383725 < baseStart_6383725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383765 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_6383765 : Nat := 118140960795 + 6383765 * 2 ^ 59
def prefixEnd_6383765 : Nat := 4983230072969 + 3 ^ 40 * 6383765 * 2
def baseEnd_6383765 : Nat := 3277939830349321223779105

theorem tailTrace_6383765 : CollatzResearch.WordTrace tailWord_6383765 prefixEnd_6383765 3277939830349321223779105 := by
  unfold tailWord_6383765
  simp only [CollatzResearch.WordTrace]
  refine ⟨232835037717717140107056749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155223358478478093404704499 232835037717717140107056749)
  ·
    refine ⟨87313139144143927540146281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232835037717717140107056749 87313139144143927540146281)
    ·
      refine ⟨65484854358107945655109711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87313139144143927540146281 65484854358107945655109711)
      ·
        refine ⟨98227281537161918482664567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65484854358107945655109711 98227281537161918482664567)
        ·
          refine ⟨147340922305742877723996851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98227281537161918482664567 147340922305742877723996851)
          ·
            refine ⟨221011383458614316585995277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147340922305742877723996851 221011383458614316585995277)
            ·
              refine ⟨82879268796980368719748229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221011383458614316585995277 82879268796980368719748229)
              ·
                refine ⟨15539862899433819134952793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82879268796980368719748229 15539862899433819134952793)
                ·
                  refine ⟨11654897174575364351214595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15539862899433819134952793 11654897174575364351214595)
                  ·
                    refine ⟨17482345761863046526821893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11654897174575364351214595 17482345761863046526821893)
                    ·
                      refine ⟨3277939830349321223779105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17482345761863046526821893 3277939830349321223779105)
                      ·
                        rfl

theorem cell23_6383765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_6383765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383765 prefixEnd_6383765 := by exact prefixLift 6383765
  have htrace : WordTrace (prefixWord ++ tailWord_6383765) baseStart_6383765 baseEnd_6383765 := by
    simpa [prefixWord, tailWord_6383765, baseEnd_6383765] using wordTrace_append hprefix tailTrace_6383765
  have hstable : (prefixWord ++ tailWord_6383765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383765).length < 2 ^ (prefixWord ++ tailWord_6383765).sum := by decide
  have hdescent : baseEnd_6383765 < baseStart_6383765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383796 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6383796 : Nat := 118140960795 + 6383796 * 2 ^ 59
def prefixEnd_6383796 : Nat := 4983230072969 + 3 ^ 40 * 6383796 * 2
def baseEnd_6383796 : Nat := 1092651916083203534163821

theorem tailTrace_6383796 : CollatzResearch.WordTrace tailWord_6383796 prefixEnd_6383796 1092651916083203534163821 := by
  unfold tailWord_6383796
  simp only [CollatzResearch.WordTrace]
  refine ⟨116418084190302416200717621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155224112253736554934290161 116418084190302416200717621)
  ·
    refine ⟨10914195392840851518817277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116418084190302416200717621 10914195392840851518817277)
    ·
      refine ⟨4092823272315319319556479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10914195392840851518817277 4092823272315319319556479)
      ·
        refine ⟨6139234908472978979334719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092823272315319319556479 6139234908472978979334719)
        ·
          refine ⟨9208852362709468469002079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139234908472978979334719 9208852362709468469002079)
          ·
            refine ⟨13813278544064202703503119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208852362709468469002079 13813278544064202703503119)
            ·
              refine ⟨20719917816096304055254679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13813278544064202703503119 20719917816096304055254679)
              ·
                refine ⟨31079876724144456082882019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20719917816096304055254679 31079876724144456082882019)
                ·
                  refine ⟨46619815086216684124323029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31079876724144456082882019 46619815086216684124323029)
                  ·
                    refine ⟨1092651916083203534163821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46619815086216684124323029 1092651916083203534163821)
                    ·
                      rfl

theorem cell23_6383796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6383796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383796 prefixEnd_6383796 := by exact prefixLift 6383796
  have htrace : WordTrace (prefixWord ++ tailWord_6383796) baseStart_6383796 baseEnd_6383796 := by
    simpa [prefixWord, tailWord_6383796, baseEnd_6383796] using wordTrace_append hprefix tailTrace_6383796
  have hstable : (prefixWord ++ tailWord_6383796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383796).length < 2 ^ (prefixWord ++ tailWord_6383796).sum := by decide
  have hdescent : baseEnd_6383796 < baseStart_6383796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383802 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_6383802 : Nat := 118140960795 + 6383802 * 2 ^ 59
def prefixEnd_6383802 : Nat := 4983230072969 + 3 ^ 40 * 6383802 * 2
def baseEnd_6383802 : Nat := 3277958829133537579016435

theorem tailTrace_6383802 : CollatzResearch.WordTrace tailWord_6383802 prefixEnd_6383802 3277958829133537579016435 := by
  unfold tailWord_6383802
  simp only [CollatzResearch.WordTrace]
  refine ⟨58209096804645773856538415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155224258145722063617435773 58209096804645773856538415)
  ·
    refine ⟨87313645206968660784807623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58209096804645773856538415 87313645206968660784807623)
    ·
      refine ⟨130970467810452991177211435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87313645206968660784807623 130970467810452991177211435)
      ·
        refine ⟨196455701715679486765817153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130970467810452991177211435 196455701715679486765817153)
        ·
          refine ⟨147341776286759615074362865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196455701715679486765817153 147341776286759615074362865)
          ·
            refine ⟨110506332215069711305772149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147341776286759615074362865 110506332215069711305772149)
            ·
              refine ⟨10359968645162785434916139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110506332215069711305772149 10359968645162785434916139)
              ·
                refine ⟨15539952967744178152374209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10359968645162785434916139 15539952967744178152374209)
                ·
                  refine ⟨11654964725808133614280657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15539952967744178152374209 11654964725808133614280657)
                  ·
                    refine ⟨8741223544356100210710493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11654964725808133614280657 8741223544356100210710493)
                    ·
                      refine ⟨3277958829133537579016435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741223544356100210710493 3277958829133537579016435)
                      ·
                        rfl

theorem cell23_6383802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_6383802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383802 prefixEnd_6383802 := by exact prefixLift 6383802
  have htrace : WordTrace (prefixWord ++ tailWord_6383802) baseStart_6383802 baseEnd_6383802 := by
    simpa [prefixWord, tailWord_6383802, baseEnd_6383802] using wordTrace_append hprefix tailTrace_6383802
  have hstable : (prefixWord ++ tailWord_6383802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383802).length < 2 ^ (prefixWord ++ tailWord_6383802).sum := by decide
  have hdescent : baseEnd_6383802 < baseStart_6383802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383822 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_6383822 : Nat := 118140960795 + 6383822 * 2 ^ 59
def prefixEnd_6383822 : Nat := 4983230072969 + 3 ^ 40 * 6383822 * 2
def baseEnd_6383822 : Nat := 364218788749625277862927

theorem tailTrace_6383822 : CollatzResearch.WordTrace tailWord_6383822 prefixEnd_6383822 364218788749625277862927 := by
  unfold tailWord_6383822
  simp only [CollatzResearch.WordTrace]
  refine ⟨29104639584813829855235215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155224744452340425894587813 29104639584813829855235215)
  ·
    refine ⟨43656959377220744782852823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29104639584813829855235215 43656959377220744782852823)
    ·
      refine ⟨65485439065831117174279235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43656959377220744782852823 65485439065831117174279235)
      ·
        refine ⟨98228158598746675761418853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65485439065831117174279235 98228158598746675761418853)
        ·
          refine ⟨18417779737265001705266035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98228158598746675761418853 18417779737265001705266035)
          ·
            refine ⟨27626669605897502557899053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18417779737265001705266035 27626669605897502557899053)
            ·
              refine ⟨10360001102211563459212145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27626669605897502557899053 10360001102211563459212145)
              ·
                refine ⟨7770000826658672594409109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10360001102211563459212145 7770000826658672594409109)
                ·
                  refine ⟨364218788749625277862927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7770000826658672594409109 364218788749625277862927)
                  ·
                    rfl

theorem cell23_6383822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_6383822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383822 prefixEnd_6383822 := by exact prefixLift 6383822
  have htrace : WordTrace (prefixWord ++ tailWord_6383822) baseStart_6383822 baseEnd_6383822 := by
    simpa [prefixWord, tailWord_6383822, baseEnd_6383822] using wordTrace_append hprefix tailTrace_6383822
  have hstable : (prefixWord ++ tailWord_6383822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383822).length < 2 ^ (prefixWord ++ tailWord_6383822).sum := by decide
  have hdescent : baseEnd_6383822 < baseStart_6383822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383852 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_6383852 : Nat := 118140960795 + 6383852 * 2 ^ 59
def prefixEnd_6383852 : Nat := 4983230072969 + 3 ^ 40 * 6383852 * 2
def baseEnd_6383852 : Nat := 1092661501055420794463735

theorem tailTrace_6383852 : CollatzResearch.WordTrace tailWord_6383852 prefixEnd_6383852 1092661501055420794463735 := by
  unfold tailWord_6383852
  simp only [CollatzResearch.WordTrace]
  refine ⟨116419105434200976982736905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155225473912267969310315873 116419105434200976982736905)
  ·
    refine ⟨87314329075650732737052679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116419105434200976982736905 87314329075650732737052679)
    ·
      refine ⟨130971493613476099105579019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87314329075650732737052679 130971493613476099105579019)
      ·
        refine ⟨196457240420214148658368529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130971493613476099105579019 196457240420214148658368529)
        ·
          refine ⟨147342930315160611493776397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196457240420214148658368529 147342930315160611493776397)
          ·
            refine ⟨55253598868185229310166149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147342930315160611493776397 55253598868185229310166149)
            ·
              refine ⟨10360049787784730495656153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55253598868185229310166149 10360049787784730495656153)
              ·
                refine ⟨7770037340838547871742115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10360049787784730495656153 7770037340838547871742115)
                ·
                  refine ⟨11655056011257821807613173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770037340838547871742115 11655056011257821807613173)
                  ·
                    refine ⟨1092661501055420794463735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11655056011257821807613173 1092661501055420794463735)
                    ·
                      rfl

theorem cell23_6383852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_6383852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383852 prefixEnd_6383852 := by exact prefixLift 6383852
  have htrace : WordTrace (prefixWord ++ tailWord_6383852) baseStart_6383852 baseEnd_6383852 := by
    simpa [prefixWord, tailWord_6383852, baseEnd_6383852] using wordTrace_append hprefix tailTrace_6383852
  have hstable : (prefixWord ++ tailWord_6383852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383852).length < 2 ^ (prefixWord ++ tailWord_6383852).sum := by decide
  have hdescent : baseEnd_6383852 < baseStart_6383852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383866 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3]
def baseStart_6383866 : Nat := 118140960795 + 6383866 * 2 ^ 59
def prefixEnd_6383866 : Nat := 4983230072969 + 3 ^ 40 * 6383866 * 2
def baseEnd_6383866 : Nat := 3277991691895425328616141

theorem tailTrace_6383866 : CollatzResearch.WordTrace tailWord_6383866 prefixEnd_6383866 3277991691895425328616141 := by
  unfold tailWord_6383866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58209680372587808589120863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155225814326900822904322301 58209680372587808589120863)
  ·
    refine ⟨87314520558881712883681295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58209680372587808589120863 87314520558881712883681295)
    ·
      refine ⟨130971780838322569325521943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87314520558881712883681295 130971780838322569325521943)
      ·
        refine ⟨196457671257483853988282915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130971780838322569325521943 196457671257483853988282915)
        ·
          refine ⟨294686506886225780982424373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196457671257483853988282915 294686506886225780982424373)
          ·
            refine ⟨27626860020583666967102285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294686506886225780982424373 27626860020583666967102285)
            ·
              refine ⟨10360072507718875112663357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27626860020583666967102285 10360072507718875112663357)
              ·
                refine ⟨3885027190394578167248759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10360072507718875112663357 3885027190394578167248759)
                ·
                  refine ⟨5827540785591867250873139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885027190394578167248759 5827540785591867250873139)
                  ·
                    refine ⟨8741311178387800876309709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5827540785591867250873139 8741311178387800876309709)
                    ·
                      refine ⟨3277991691895425328616141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741311178387800876309709 3277991691895425328616141)
                      ·
                        rfl

theorem cell23_6383866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_6383866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383866 prefixEnd_6383866 := by exact prefixLift 6383866
  have htrace : WordTrace (prefixWord ++ tailWord_6383866) baseStart_6383866 baseEnd_6383866 := by
    simpa [prefixWord, tailWord_6383866, baseEnd_6383866] using wordTrace_append hprefix tailTrace_6383866
  have hstable : (prefixWord ++ tailWord_6383866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383866).length < 2 ^ (prefixWord ++ tailWord_6383866).sum := by decide
  have hdescent : baseEnd_6383866 < baseStart_6383866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383872 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4]
def baseStart_6383872 : Nat := 118140960795 + 6383872 * 2 ^ 59
def prefixEnd_6383872 : Nat := 4983230072969 + 3 ^ 40 * 6383872 * 2
def baseEnd_6383872 : Nat := 3277994772779352305141113

theorem tailTrace_6383872 : CollatzResearch.WordTrace tailWord_6383872 prefixEnd_6383872 3277994772779352305141113 := by
  unfold tailWord_6383872
  simp only [CollatzResearch.WordTrace]
  refine ⟨116419470164164748690600935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155225960218886331587467913 116419470164164748690600935)
  ·
    refine ⟨174629205246247123035901403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116419470164164748690600935 174629205246247123035901403)
    ·
      refine ⟨261943807869370684553852105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174629205246247123035901403 261943807869370684553852105)
      ·
        refine ⟨196457855902028013415389079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261943807869370684553852105 196457855902028013415389079)
        ·
          refine ⟨294686783853042020123083619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196457855902028013415389079 294686783853042020123083619)
          ·
            refine ⟨442030175779563030184625429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294686783853042020123083619 442030175779563030184625429)
            ·
              refine ⟨20720164489667017039904317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 442030175779563030184625429 20720164489667017039904317)
              ·
                refine ⟨7770061683625131389964119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20720164489667017039904317 7770061683625131389964119)
                ·
                  refine ⟨11655092525437697084946179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770061683625131389964119 11655092525437697084946179)
                  ·
                    refine ⟨17482638788156545627419269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11655092525437697084946179 17482638788156545627419269)
                    ·
                      refine ⟨3277994772779352305141113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17482638788156545627419269 3277994772779352305141113)
                      ·
                        rfl

theorem cell23_6383872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_6383872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383872 prefixEnd_6383872 := by exact prefixLift 6383872
  have htrace : WordTrace (prefixWord ++ tailWord_6383872) baseStart_6383872 baseEnd_6383872 := by
    simpa [prefixWord, tailWord_6383872, baseEnd_6383872] using wordTrace_append hprefix tailTrace_6383872
  have hstable : (prefixWord ++ tailWord_6383872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383872).length < 2 ^ (prefixWord ++ tailWord_6383872).sum := by decide
  have hdescent : baseEnd_6383872 < baseStart_6383872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383876 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_6383876 : Nat := 118140960795 + 6383876 * 2 ^ 59
def prefixEnd_6383876 : Nat := 4983230072969 + 3 ^ 40 * 6383876 * 2
def baseEnd_6383876 : Nat := 3277996826701970289491095

theorem tailTrace_6383876 : CollatzResearch.WordTrace tailWord_6383876 prefixEnd_6383876 3277996826701970289491095 := by
  unfold tailWord_6383876
  simp only [CollatzResearch.WordTrace]
  refine ⟨116419543110157503032173741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155226057480210004042898321 116419543110157503032173741)
  ·
    refine ⟨43657328666309063637065153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116419543110157503032173741 43657328666309063637065153)
    ·
      refine ⟨32742996499731797727798865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43657328666309063637065153 32742996499731797727798865)
      ·
        refine ⟨24557247374798848295849149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32742996499731797727798865 24557247374798848295849149)
        ·
          refine ⟨9208967765549568110943431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24557247374798848295849149 9208967765549568110943431)
          ·
            refine ⟨13813451648324352166415147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208967765549568110943431 13813451648324352166415147)
            ·
              refine ⟨20720177472486528249622721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13813451648324352166415147 20720177472486528249622721)
              ·
                refine ⟨15540133104364896187217041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20720177472486528249622721 15540133104364896187217041)
                ·
                  refine ⟨11655099828273672140412781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15540133104364896187217041 11655099828273672140412781)
                  ·
                    refine ⟨4370662435602627052654793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11655099828273672140412781 4370662435602627052654793)
                    ·
                      refine ⟨3277996826701970289491095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370662435602627052654793 3277996826701970289491095)
                      ·
                        rfl

theorem cell23_6383876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_6383876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383876 prefixEnd_6383876 := by exact prefixLift 6383876
  have htrace : WordTrace (prefixWord ++ tailWord_6383876) baseStart_6383876 baseEnd_6383876 := by
    simpa [prefixWord, tailWord_6383876, baseEnd_6383876] using wordTrace_append hprefix tailTrace_6383876
  have hstable : (prefixWord ++ tailWord_6383876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383876).length < 2 ^ (prefixWord ++ tailWord_6383876).sum := by decide
  have hdescent : baseEnd_6383876 < baseStart_6383876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383882 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_6383882 : Nat := 118140960795 + 6383882 * 2 ^ 59
def prefixEnd_6383882 : Nat := 4983230072969 + 3 ^ 40 * 6383882 * 2
def baseEnd_6383882 : Nat := 1092666635861965755338689

theorem tailTrace_6383882 : CollatzResearch.WordTrace tailWord_6383882 prefixEnd_6383882 1092666635861965755338689 := by
  unfold tailWord_6383882
  simp only [CollatzResearch.WordTrace]
  refine ⟨58209826264573317272266475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155226203372195512726043933 58209826264573317272266475)
  ·
    refine ⟨87314739396859975908399713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58209826264573317272266475 87314739396859975908399713)
    ·
      refine ⟨65486054547644981931299785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87314739396859975908399713 65486054547644981931299785)
      ·
        refine ⟨49114540910733736448474839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65486054547644981931299785 49114540910733736448474839)
        ·
          refine ⟨73671811366100604672712259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49114540910733736448474839 73671811366100604672712259)
          ·
            refine ⟨110507717049150907009068389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73671811366100604672712259 110507717049150907009068389)
            ·
              refine ⟨20720196946715795064200323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110507717049150907009068389 20720196946715795064200323)
              ·
                refine ⟨31080295420073692596300485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20720196946715795064200323 31080295420073692596300485)
                ·
                  refine ⟨5827555391263817361806341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31080295420073692596300485 5827555391263817361806341)
                  ·
                    refine ⟨1092666635861965755338689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827555391263817361806341 1092666635861965755338689)
                    ·
                      rfl

theorem cell23_6383882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_6383882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383882 prefixEnd_6383882 := by exact prefixLift 6383882
  have htrace : WordTrace (prefixWord ++ tailWord_6383882) baseStart_6383882 baseEnd_6383882 := by
    simpa [prefixWord, tailWord_6383882, baseEnd_6383882] using wordTrace_append hprefix tailTrace_6383882
  have hstable : (prefixWord ++ tailWord_6383882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383882).length < 2 ^ (prefixWord ++ tailWord_6383882).sum := by decide
  have hdescent : baseEnd_6383882 < baseStart_6383882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383895 : List Nat := [1, 1, 3, 4, 1, 2, 1, 10]
def baseStart_6383895 : Nat := 118140960795 + 6383895 * 2 ^ 59
def prefixEnd_6383895 : Nat := 4983230072969 + 3 ^ 40 * 6383895 * 2
def baseEnd_6383895 : Nat := 121407651216089100561241

theorem tailTrace_6383895 : CollatzResearch.WordTrace tailWord_6383895 prefixEnd_6383895 121407651216089100561241 := by
  unfold tailWord_6383895
  simp only [CollatzResearch.WordTrace]
  refine ⟨232839779207246172309289139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155226519471497448206192759 232839779207246172309289139)
  ·
    refine ⟨349259668810869258463933709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232839779207246172309289139 349259668810869258463933709)
    ·
      refine ⟨130972375804075971923975141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349259668810869258463933709 130972375804075971923975141)
      ·
        refine ⟨24557320463264244735745339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130972375804075971923975141 24557320463264244735745339)
        ·
          refine ⟨36835980694896367103618009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24557320463264244735745339 36835980694896367103618009)
          ·
            refine ⟨27626985521172275327713507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36835980694896367103618009 27626985521172275327713507)
            ·
              refine ⟨41440478281758412991570261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27626985521172275327713507 41440478281758412991570261)
              ·
                refine ⟨121407651216089100561241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41440478281758412991570261 121407651216089100561241)
                ·
                  rfl

theorem cell23_6383895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 10].length) (baseStart_6383895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383895 prefixEnd_6383895 := by exact prefixLift 6383895
  have htrace : WordTrace (prefixWord ++ tailWord_6383895) baseStart_6383895 baseEnd_6383895 := by
    simpa [prefixWord, tailWord_6383895, baseEnd_6383895] using wordTrace_append hprefix tailTrace_6383895
  have hstable : (prefixWord ++ tailWord_6383895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383895).length < 2 ^ (prefixWord ++ tailWord_6383895).sum := by decide
  have hdescent : baseEnd_6383895 < baseStart_6383895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383899 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 2, 4]
def baseStart_6383899 : Nat := 118140960795 + 6383899 * 2 ^ 59
def prefixEnd_6383899 : Nat := 4983230072969 + 3 ^ 40 * 6383899 * 2
def baseEnd_6383899 : Nat := 1092669545585674566501163

theorem tailTrace_6383899 : CollatzResearch.WordTrace tailWord_6383899 prefixEnd_6383899 1092669545585674566501163 := by
  unfold tailWord_6383899
  simp only [CollatzResearch.WordTrace]
  refine ⟨232839925099231680992434751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155226616732821120661623167 232839925099231680992434751)
  ·
    refine ⟨349259887648847521488652127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232839925099231680992434751 349259887648847521488652127)
    ·
      refine ⟨523889831473271282232978191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349259887648847521488652127 523889831473271282232978191)
      ·
        refine ⟨785834747209906923349467287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523889831473271282232978191 785834747209906923349467287)
        ·
          refine ⟨1178752120814860385024200931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785834747209906923349467287 1178752120814860385024200931)
          ·
            refine ⟨1768128181222290577536301397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178752120814860385024200931 1768128181222290577536301397)
            ·
              refine ⟨5180063030924679426375883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1768128181222290577536301397 5180063030924679426375883)
              ·
                refine ⟨7770094546387019139563825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180063030924679426375883 7770094546387019139563825)
                ·
                  refine ⟨5827570909790264354672869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770094546387019139563825 5827570909790264354672869)
                  ·
                    refine ⟨1092669545585674566501163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827570909790264354672869 1092669545585674566501163)
                    ·
                      rfl

theorem cell23_6383899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 4].length) (baseStart_6383899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383899 prefixEnd_6383899 := by exact prefixLift 6383899
  have htrace : WordTrace (prefixWord ++ tailWord_6383899) baseStart_6383899 baseEnd_6383899 := by
    simpa [prefixWord, tailWord_6383899, baseEnd_6383899] using wordTrace_append hprefix tailTrace_6383899
  have hstable : (prefixWord ++ tailWord_6383899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383899).length < 2 ^ (prefixWord ++ tailWord_6383899).sum := by decide
  have hdescent : baseEnd_6383899 < baseStart_6383899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383906 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_6383906 : Nat := 118140960795 + 6383906 * 2 ^ 59
def prefixEnd_6383906 : Nat := 4983230072969 + 3 ^ 40 * 6383906 * 2
def baseEnd_6383906 : Nat := 3278012231121605172115957

theorem tailTrace_6383906 : CollatzResearch.WordTrace tailWord_6383906 prefixEnd_6383906 3278012231121605172115957 := by
  unfold tailWord_6383906
  simp only [CollatzResearch.WordTrace]
  refine ⟨58210045102551580296984893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155226786940137547458626381 58210045102551580296984893)
  ·
    refine ⟨21828766913456842611369335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58210045102551580296984893 21828766913456842611369335)
    ·
      refine ⟨32743150370185263917054003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21828766913456842611369335 32743150370185263917054003)
      ·
        refine ⟨49114725555277895875581005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32743150370185263917054003 49114725555277895875581005)
        ·
          refine ⟨18418022083229210953342877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49114725555277895875581005 18418022083229210953342877)
          ·
            refine ⟨6906758281210954107503579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18418022083229210953342877 6906758281210954107503579)
            ·
              refine ⟨10360137421816431161255369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6906758281210954107503579 10360137421816431161255369)
              ·
                refine ⟨7770103066362323370941527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10360137421816431161255369 7770103066362323370941527)
                ·
                  refine ⟨11655154599543485056412291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770103066362323370941527 11655154599543485056412291)
                  ·
                    refine ⟨17482731899315227584618437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11655154599543485056412291 17482731899315227584618437)
                    ·
                      refine ⟨3278012231121605172115957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17482731899315227584618437 3278012231121605172115957)
                      ·
                        rfl

theorem cell23_6383906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_6383906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383906 prefixEnd_6383906 := by exact prefixLift 6383906
  have htrace : WordTrace (prefixWord ++ tailWord_6383906) baseStart_6383906 baseEnd_6383906 := by
    simpa [prefixWord, tailWord_6383906, baseEnd_6383906] using wordTrace_append hprefix tailTrace_6383906
  have hstable : (prefixWord ++ tailWord_6383906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383906).length < 2 ^ (prefixWord ++ tailWord_6383906).sum := by decide
  have hdescent : baseEnd_6383906 < baseStart_6383906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383909 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_6383909 : Nat := 118140960795 + 6383909 * 2 ^ 59
def prefixEnd_6383909 : Nat := 4983230072969 + 3 ^ 40 * 6383909 * 2
def baseEnd_6383909 : Nat := 3278013771563568660378443

theorem tailTrace_6383909 : CollatzResearch.WordTrace tailWord_6383909 prefixEnd_6383909 3278013771563568660378443 := by
  unfold tailWord_6383909
  simp only [CollatzResearch.WordTrace]
  refine ⟨232840289829195452700298781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155226859886130301800199187 232840289829195452700298781)
  ·
    refine ⟨87315108685948294762612043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232840289829195452700298781 87315108685948294762612043)
    ·
      refine ⟨130972663028922442143918065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87315108685948294762612043 130972663028922442143918065)
      ·
        refine ⟨98229497271691831607938549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130972663028922442143918065 98229497271691831607938549)
        ·
          refine ⟨9209015369221109213244239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98229497271691831607938549 9209015369221109213244239)
          ·
            refine ⟨13813523053831663819866359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9209015369221109213244239 13813523053831663819866359)
            ·
              refine ⟨20720284580747495729799539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13813523053831663819866359 20720284580747495729799539)
              ·
                refine ⟨31080426871121243594699309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20720284580747495729799539 31080426871121243594699309)
                ·
                  refine ⟨11655160076670466348012241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31080426871121243594699309 11655160076670466348012241)
                  ·
                    refine ⟨8741370057502849761009181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11655160076670466348012241 8741370057502849761009181)
                    ·
                      refine ⟨3278013771563568660378443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741370057502849761009181 3278013771563568660378443)
                      ·
                        rfl

theorem cell23_6383909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_6383909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383909 prefixEnd_6383909 := by exact prefixLift 6383909
  have htrace : WordTrace (prefixWord ++ tailWord_6383909) baseStart_6383909 baseEnd_6383909 := by
    simpa [prefixWord, tailWord_6383909, baseEnd_6383909] using wordTrace_append hprefix tailTrace_6383909
  have hstable : (prefixWord ++ tailWord_6383909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383909).length < 2 ^ (prefixWord ++ tailWord_6383909).sum := by decide
  have hdescent : baseEnd_6383909 < baseStart_6383909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383939 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 3]
def baseStart_6383939 : Nat := 118140960795 + 6383939 * 2 ^ 59
def prefixEnd_6383939 : Nat := 4983230072969 + 3 ^ 40 * 6383939 * 2
def baseEnd_6383939 : Nat := 3278029175983203543003305

theorem tailTrace_6383939 : CollatzResearch.WordTrace tailWord_6383939 prefixEnd_6383939 3278029175983203543003305 := by
  unfold tailWord_6383939
  simp only [CollatzResearch.WordTrace]
  refine ⟨232841384019086767823890871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155227589346057845215927247 232841384019086767823890871)
  ·
    refine ⟨349262076028630151735836307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232841384019086767823890871 349262076028630151735836307)
    ·
      refine ⟨523893114042945227603754461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349262076028630151735836307 523893114042945227603754461)
      ·
        refine ⟨196459917766104460351407923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523893114042945227603754461 196459917766104460351407923)
        ·
          refine ⟨294689876649156690527111885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196459917766104460351407923 294689876649156690527111885)
          ·
            refine ⟨110508703743433758947666957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294689876649156690527111885 110508703743433758947666957)
            ·
              refine ⟨41440763903787659605375109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110508703743433758947666957 41440763903787659605375109)
              ·
                refine ⟨7770143231960186176007833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41440763903787659605375109 7770143231960186176007833)
                ·
                  refine ⟨5827607423970139632005875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770143231960186176007833 5827607423970139632005875)
                  ·
                    refine ⟨8741411135955209448008813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5827607423970139632005875 8741411135955209448008813)
                    ·
                      refine ⟨3278029175983203543003305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741411135955209448008813 3278029175983203543003305)
                      ·
                        rfl

theorem cell23_6383939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_6383939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383939 prefixEnd_6383939 := by exact prefixLift 6383939
  have htrace : WordTrace (prefixWord ++ tailWord_6383939) baseStart_6383939 baseEnd_6383939 := by
    simpa [prefixWord, tailWord_6383939, baseEnd_6383939] using wordTrace_append hprefix tailTrace_6383939
  have hstable : (prefixWord ++ tailWord_6383939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383939).length < 2 ^ (prefixWord ++ tailWord_6383939).sum := by decide
  have hdescent : baseEnd_6383939 < baseStart_6383939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383956 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_6383956 : Nat := 118140960795 + 6383956 * 2 ^ 59
def prefixEnd_6383956 : Nat := 4983230072969 + 3 ^ 40 * 6383956 * 2
def baseEnd_6383956 : Nat := 3278037905154329976490727

theorem tailTrace_6383956 : CollatzResearch.WordTrace tailWord_6383956 prefixEnd_6383956 3278037905154329976490727 := by
  unfold tailWord_6383956
  simp only [CollatzResearch.WordTrace]
  refine ⟨116421002030012589863629861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155228002706683453151506481 116421002030012589863629861)
  ·
    refine ⟨21828937880627360599430599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116421002030012589863629861 21828937880627360599430599)
    ·
      refine ⟨32743406820941040899145899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21828937880627360599430599 32743406820941040899145899)
      ·
        refine ⟨49115110231411561348718849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32743406820941040899145899 49115110231411561348718849)
        ·
          refine ⟨36836332673558671011539137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49115110231411561348718849 36836332673558671011539137)
          ·
            refine ⟨27627249505169003258654353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36836332673558671011539137 27627249505169003258654353)
            ·
              refine ⟨20720437128876752443990765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27627249505169003258654353 20720437128876752443990765)
              ·
                refine ⟨7770163923328782166496537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20720437128876752443990765 7770163923328782166496537)
                ·
                  refine ⟨5827622942496586624872403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770163923328782166496537 5827622942496586624872403)
                  ·
                    refine ⟨8741434413744879937308605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5827622942496586624872403 8741434413744879937308605)
                    ·
                      refine ⟨3278037905154329976490727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741434413744879937308605 3278037905154329976490727)
                      ·
                        rfl

theorem cell23_6383956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_6383956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383956 prefixEnd_6383956 := by exact prefixLift 6383956
  have htrace : WordTrace (prefixWord ++ tailWord_6383956) baseStart_6383956 baseEnd_6383956 := by
    simpa [prefixWord, tailWord_6383956, baseEnd_6383956] using wordTrace_append hprefix tailTrace_6383956
  have hstable : (prefixWord ++ tailWord_6383956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383956).length < 2 ^ (prefixWord ++ tailWord_6383956).sum := by decide
  have hdescent : baseEnd_6383956 < baseStart_6383956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383979 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 6, 2, 2]
def baseStart_6383979 : Nat := 118140960795 + 6383979 * 2 ^ 59
def prefixEnd_6383979 : Nat := 4983230072969 + 3 ^ 40 * 6383979 * 2
def baseEnd_6383979 : Nat := 3278049715209383386503121

theorem tailTrace_6383979 : CollatzResearch.WordTrace tailWord_6383979 prefixEnd_6383979 3278049715209383386503121 := by
  unfold tailWord_6383979
  simp only [CollatzResearch.WordTrace]
  refine ⟨232842842938941854655346991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155228561959294569770231327 232842842938941854655346991)
  ·
    refine ⟨349264264408412781983020487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232842842938941854655346991 349264264408412781983020487)
    ·
      refine ⟨523896396612619172974530731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349264264408412781983020487 523896396612619172974530731)
      ·
        refine ⟨785844594918928759461796097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523896396612619172974530731 785844594918928759461796097)
        ·
          refine ⟨589383446189196569596347073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785844594918928759461796097 589383446189196569596347073)
          ·
            refine ⟨442037584641897427197260305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589383446189196569596347073 442037584641897427197260305)
            ·
              refine ⟨331528188481423070397945229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442037584641897427197260305 331528188481423070397945229)
              ·
                refine ⟨124323070680533651399229461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331528188481423070397945229 124323070680533651399229461)
                ·
                  refine ⟨5827643938150014909338881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124323070680533651399229461 5827643938150014909338881)
                  ·
                    refine ⟨4370732953612511182004161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827643938150014909338881 4370732953612511182004161)
                    ·
                      refine ⟨3278049715209383386503121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370732953612511182004161 3278049715209383386503121)
                      ·
                        rfl

theorem cell23_6383979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 2, 2].length) (baseStart_6383979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383979 prefixEnd_6383979 := by exact prefixLift 6383979
  have htrace : WordTrace (prefixWord ++ tailWord_6383979) baseStart_6383979 baseEnd_6383979 := by
    simpa [prefixWord, tailWord_6383979, baseEnd_6383979] using wordTrace_append hprefix tailTrace_6383979
  have hstable : (prefixWord ++ tailWord_6383979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383979).length < 2 ^ (prefixWord ++ tailWord_6383979).sum := by decide
  have hdescent : baseEnd_6383979 < baseStart_6383979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383985 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 11]
def baseStart_6383985 : Nat := 118140960795 + 6383985 * 2 ^ 59
def prefixEnd_6383985 : Nat := 4983230072969 + 3 ^ 40 * 6383985 * 2
def baseEnd_6383985 : Nat := 364228088454812262558677

theorem tailTrace_6383985 : CollatzResearch.WordTrace tailWord_6383985 prefixEnd_6383985 364228088454812262558677 := by
  unfold tailWord_6383985
  simp only [CollatzResearch.WordTrace]
  refine ⟨232843061776920117680065409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155228707851280078453376939 232843061776920117680065409)
  ·
    refine ⟨174632296332690088260049057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232843061776920117680065409 174632296332690088260049057)
    ·
      refine ⟨130974222249517566195036793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174632296332690088260049057 130974222249517566195036793)
      ·
        refine ⟨98230666687138174646277595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130974222249517566195036793 98230666687138174646277595)
        ·
          refine ⟨147346000030707261969416393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98230666687138174646277595 147346000030707261969416393)
          ·
            refine ⟨110509500023030446477062295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147346000030707261969416393 110509500023030446477062295)
            ·
              refine ⟨165764250034545669715593443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110509500023030446477062295 165764250034545669715593443)
              ·
                refine ⟨248646375051818504573390165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165764250034545669715593443 248646375051818504573390165)
                ·
                  refine ⟨364228088454812262558677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 248646375051818504573390165 364228088454812262558677)
                  ·
                    rfl

theorem cell23_6383985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_6383985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383985 prefixEnd_6383985 := by exact prefixLift 6383985
  have htrace : WordTrace (prefixWord ++ tailWord_6383985) baseStart_6383985 baseEnd_6383985 := by
    simpa [prefixWord, tailWord_6383985, baseEnd_6383985] using wordTrace_append hprefix tailTrace_6383985
  have hstable : (prefixWord ++ tailWord_6383985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383985).length < 2 ^ (prefixWord ++ tailWord_6383985).sum := by decide
  have hdescent : baseEnd_6383985 < baseStart_6383985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6383996 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_6383996 : Nat := 118140960795 + 6383996 * 2 ^ 59
def prefixEnd_6383996 : Nat := 4983230072969 + 3 ^ 40 * 6383996 * 2
def baseEnd_6383996 : Nat := 3278058444380509819990543

theorem tailTrace_6383996 : CollatzResearch.WordTrace tailWord_6383996 prefixEnd_6383996 3278058444380509819990543 := by
  unfold tailWord_6383996
  simp only [CollatzResearch.WordTrace]
  refine ⟨116421731489940133279357921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155228975319920177705810561 116421731489940133279357921)
  ·
    refine ⟨87316298617455099959518441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116421731489940133279357921 87316298617455099959518441)
    ·
      refine ⟨65487223963091324969638831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87316298617455099959518441 65487223963091324969638831)
      ·
        refine ⟨98230835944636987454458247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65487223963091324969638831 98230835944636987454458247)
        ·
          refine ⟨147346253916955481181687371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98230835944636987454458247 147346253916955481181687371)
          ·
            refine ⟨221019380875433221772531057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147346253916955481181687371 221019380875433221772531057)
            ·
              refine ⟨165764535656574916329398293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221019380875433221772531057 165764535656574916329398293)
              ·
                refine ⟨7770212608901949202940545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165764535656574916329398293 7770212608901949202940545)
                ·
                  refine ⟨5827659456676461902205409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770212608901949202940545 5827659456676461902205409)
                  ·
                    refine ⟨4370744592507346426654057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827659456676461902205409 4370744592507346426654057)
                    ·
                      refine ⟨3278058444380509819990543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370744592507346426654057 3278058444380509819990543)
                      ·
                        rfl

theorem cell23_6383996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_6383996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6383996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6383996 prefixEnd_6383996 := by exact prefixLift 6383996
  have htrace : WordTrace (prefixWord ++ tailWord_6383996) baseStart_6383996 baseEnd_6383996 := by
    simpa [prefixWord, tailWord_6383996, baseEnd_6383996] using wordTrace_append hprefix tailTrace_6383996
  have hstable : (prefixWord ++ tailWord_6383996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6383996).length < 2 ^ (prefixWord ++ tailWord_6383996).sum := by decide
  have hdescent : baseEnd_6383996 < baseStart_6383996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6383996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384032 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_6384032 : Nat := 118140960795 + 6384032 * 2 ^ 59
def prefixEnd_6384032 : Nat := 4983230072969 + 3 ^ 40 * 6384032 * 2
def baseEnd_6384032 : Nat := 1092692309894690559713459

theorem tailTrace_6384032 : CollatzResearch.WordTrace tailWord_6384032 prefixEnd_6384032 1092692309894690559713459 := by
  unfold tailWord_6384032
  simp only [CollatzResearch.WordTrace]
  refine ⟨116422388003874922353513175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155229850671833229804684233 116422388003874922353513175)
  ·
    refine ⟨174633582005812383530269763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116422388003874922353513175 174633582005812383530269763)
    ·
      refine ⟨261950373008718575295404645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174633582005812383530269763 261950373008718575295404645)
      ·
        refine ⟨49115694939134732867888371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261950373008718575295404645 49115694939134732867888371)
        ·
          refine ⟨73673542408702099301832557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49115694939134732867888371 73673542408702099301832557)
          ·
            refine ⟨27627578403263287238187209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73673542408702099301832557 27627578403263287238187209)
            ·
              refine ⟨20720683802447465428640407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27627578403263287238187209 20720683802447465428640407)
              ·
                refine ⟨31081025703671198142960611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20720683802447465428640407 31081025703671198142960611)
                ·
                  refine ⟨46621538555506797214440917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31081025703671198142960611 46621538555506797214440917)
                  ·
                    refine ⟨1092692309894690559713459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46621538555506797214440917 1092692309894690559713459)
                    ·
                      rfl

theorem cell23_6384032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_6384032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384032 prefixEnd_6384032 := by exact prefixLift 6384032
  have htrace : WordTrace (prefixWord ++ tailWord_6384032) baseStart_6384032 baseEnd_6384032 := by
    simpa [prefixWord, tailWord_6384032, baseEnd_6384032] using wordTrace_append hprefix tailTrace_6384032
  have hstable : (prefixWord ++ tailWord_6384032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384032).length < 2 ^ (prefixWord ++ tailWord_6384032).sum := by decide
  have hdescent : baseEnd_6384032 < baseStart_6384032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384049 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_6384049 : Nat := 118140960795 + 6384049 * 2 ^ 59
def prefixEnd_6384049 : Nat := 4983230072969 + 3 ^ 40 * 6384049 * 2
def baseEnd_6384049 : Nat := 1092695219618399370875933

theorem tailTrace_6384049 : CollatzResearch.WordTrace tailWord_6384049 prefixEnd_6384049 1092695219618399370875933 := by
  unfold tailWord_6384049
  simp only [CollatzResearch.WordTrace]
  refine ⟨232845396048688256610395201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155230264032458837740263467 232845396048688256610395201)
  ·
    refine ⟨174634047036516192457796401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232845396048688256610395201 174634047036516192457796401)
    ·
      refine ⟨130975535277387144343347301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174634047036516192457796401 130975535277387144343347301)
      ·
        refine ⟨24557912864510089564377619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130975535277387144343347301 24557912864510089564377619)
        ·
          refine ⟨36836869296765134346566429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24557912864510089564377619 36836869296765134346566429)
          ·
            refine ⟨13813825986286925379962411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36836869296765134346566429 13813825986286925379962411)
            ·
              refine ⟨20720738979430388069943617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13813825986286925379962411 20720738979430388069943617)
              ·
                refine ⟨15540554234572791052457713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20720738979430388069943617 15540554234572791052457713)
                ·
                  refine ⟨11655415675929593289343285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15540554234572791052457713 11655415675929593289343285)
                  ·
                    refine ⟨1092695219618399370875933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11655415675929593289343285 1092695219618399370875933)
                    ·
                      rfl

theorem cell23_6384049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_6384049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384049 prefixEnd_6384049 := by exact prefixLift 6384049
  have htrace : WordTrace (prefixWord ++ tailWord_6384049) baseStart_6384049 baseEnd_6384049 := by
    simpa [prefixWord, tailWord_6384049, baseEnd_6384049] using wordTrace_append hprefix tailTrace_6384049
  have hstable : (prefixWord ++ tailWord_6384049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384049).length < 2 ^ (prefixWord ++ tailWord_6384049).sum := by decide
  have hdescent : baseEnd_6384049 < baseStart_6384049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384053 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 5]
def baseStart_6384053 : Nat := 118140960795 + 6384053 * 2 ^ 59
def prefixEnd_6384053 : Nat := 4983230072969 + 3 ^ 40 * 6384053 * 2
def baseEnd_6384053 : Nat := 364231968086424010775309

theorem tailTrace_6384053 : CollatzResearch.WordTrace tailWord_6384053 prefixEnd_6384053 364231968086424010775309 := by
  unfold tailWord_6384053
  simp only [CollatzResearch.WordTrace]
  refine ⟨232845541940673765293540813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155230361293782510195693875 232845541940673765293540813)
  ·
    refine ⟨87317078227752661985077805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232845541940673765293540813 87317078227752661985077805)
    ·
      refine ⟨32743904335407248244404177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87317078227752661985077805 32743904335407248244404177)
      ·
        refine ⟨24557928251555436183303133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32743904335407248244404177 24557928251555436183303133)
        ·
          refine ⟨9209223094333288568738675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24557928251555436183303133 9209223094333288568738675)
          ·
            refine ⟨13813834641499932853108013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9209223094333288568738675 13813834641499932853108013)
            ·
              refine ⟨5180187990562474819915505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13813834641499932853108013 5180187990562474819915505)
              ·
                refine ⟨3885140992921856114936629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180187990562474819915505 3885140992921856114936629)
                ·
                  refine ⟨364231968086424010775309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3885140992921856114936629 364231968086424010775309)
                  ·
                    rfl

theorem cell23_6384053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_6384053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384053 prefixEnd_6384053 := by exact prefixLift 6384053
  have htrace : WordTrace (prefixWord ++ tailWord_6384053) baseStart_6384053 baseEnd_6384053 := by
    simpa [prefixWord, tailWord_6384053, baseEnd_6384053] using wordTrace_append hprefix tailTrace_6384053
  have hstable : (prefixWord ++ tailWord_6384053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384053).length < 2 ^ (prefixWord ++ tailWord_6384053).sum := by decide
  have hdescent : baseEnd_6384053 < baseStart_6384053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384096 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 1, 4]
def baseStart_6384096 : Nat := 118140960795 + 6384096 * 2 ^ 59
def prefixEnd_6384096 : Nat := 4983230072969 + 3 ^ 40 * 6384096 * 2
def baseEnd_6384096 : Nat := 1092703264148653142913361

theorem tailTrace_6384096 : CollatzResearch.WordTrace tailWord_6384096 prefixEnd_6384096 1092703264148653142913361 := by
  unfold tailWord_6384096
  simp only [CollatzResearch.WordTrace]
  refine ⟨116423555139758991818678071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155231406853011989091570761 116423555139758991818678071)
  ·
    refine ⟨174635332709638487728017107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116423555139758991818678071 174635332709638487728017107)
    ·
      refine ⟨261952999064457731592025661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174635332709638487728017107 261952999064457731592025661)
      ·
        refine ⟨98232374649171649347009623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261952999064457731592025661 98232374649171649347009623)
        ·
          refine ⟨147348561973757474020514435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98232374649171649347009623 147348561973757474020514435)
          ·
            refine ⟨221022842960636211030771653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147348561973757474020514435 221022842960636211030771653)
            ·
              refine ⟨41441783055119289568269685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221022842960636211030771653 41441783055119289568269685)
              ·
                refine ⟨3885167161417433397025283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41441783055119289568269685 3885167161417433397025283)
                ·
                  refine ⟨5827750742126150095537925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885167161417433397025283 5827750742126150095537925)
                  ·
                    refine ⟨1092703264148653142913361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5827750742126150095537925 1092703264148653142913361)
                    ·
                      rfl

theorem cell23_6384096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 4].length) (baseStart_6384096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384096 prefixEnd_6384096 := by exact prefixLift 6384096
  have htrace : WordTrace (prefixWord ++ tailWord_6384096) baseStart_6384096 baseEnd_6384096 := by
    simpa [prefixWord, tailWord_6384096, baseEnd_6384096] using wordTrace_append hprefix tailTrace_6384096
  have hstable : (prefixWord ++ tailWord_6384096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384096).length < 2 ^ (prefixWord ++ tailWord_6384096).sum := by decide
  have hdescent : baseEnd_6384096 < baseStart_6384096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384106 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_6384106 : Nat := 118140960795 + 6384106 * 2 ^ 59
def prefixEnd_6384106 : Nat := 4983230072969 + 3 ^ 40 * 6384106 * 2
def baseEnd_6384106 : Nat := 3278114927252504389615037

theorem tailTrace_6384106 : CollatzResearch.WordTrace tailWord_6384106 prefixEnd_6384106 3278114927252504389615037 := by
  unfold tailWord_6384106
  simp only [CollatzResearch.WordTrace]
  refine ⟨58211868752370438836305043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155231650006321170230146781 58211868752370438836305043)
  ·
    refine ⟨87317803128555658254457565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58211868752370438836305043 87317803128555658254457565)
    ·
      refine ⟨32744176173208371845421587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87317803128555658254457565 32744176173208371845421587)
      ·
        refine ⟨49116264259812557768132381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32744176173208371845421587 49116264259812557768132381)
        ·
          refine ⟨18418599097429709163049643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49116264259812557768132381 18418599097429709163049643)
          ·
            refine ⟨27627898646144563744574465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18418599097429709163049643 27627898646144563744574465)
            ·
              refine ⟨20720923984608422808430849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27627898646144563744574465 20720923984608422808430849)
              ·
                refine ⟨15540692988456317106323137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20720923984608422808430849 15540692988456317106323137)
                ·
                  refine ⟨11655519741342237829742353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15540692988456317106323137 11655519741342237829742353)
                  ·
                    refine ⟨8741639806006678372306765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11655519741342237829742353 8741639806006678372306765)
                    ·
                      refine ⟨3278114927252504389615037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741639806006678372306765 3278114927252504389615037)
                      ·
                        rfl

theorem cell23_6384106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_6384106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384106 prefixEnd_6384106 := by exact prefixLift 6384106
  have htrace : WordTrace (prefixWord ++ tailWord_6384106) baseStart_6384106 baseEnd_6384106 := by
    simpa [prefixWord, tailWord_6384106, baseEnd_6384106] using wordTrace_append hprefix tailTrace_6384106
  have hstable : (prefixWord ++ tailWord_6384106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384106).length < 2 ^ (prefixWord ++ tailWord_6384106).sum := by decide
  have hdescent : baseEnd_6384106 < baseStart_6384106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384112 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_6384112 : Nat := 118140960795 + 6384112 * 2 ^ 59
def prefixEnd_6384112 : Nat := 4983230072969 + 3 ^ 40 * 6384112 * 2
def baseEnd_6384112 : Nat := 3278118008136431366140009

theorem tailTrace_6384112 : CollatzResearch.WordTrace tailWord_6384112 prefixEnd_6384112 3278118008136431366140009 := by
  unfold tailWord_6384112
  simp only [CollatzResearch.WordTrace]
  refine ⟨116423846923730009184969295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155231795898306678913292393 116423846923730009184969295)
  ·
    refine ⟨174635770385595013777453943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116423846923730009184969295 174635770385595013777453943)
    ·
      refine ⟨261953655578392520666180915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174635770385595013777453943 261953655578392520666180915)
      ·
        refine ⟨392930483367588780999271373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261953655578392520666180915 392930483367588780999271373)
        ·
          refine ⟨147348931262845792874726765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392930483367588780999271373 147348931262845792874726765)
          ·
            refine ⟨55255849223567172328022537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147348931262845792874726765 55255849223567172328022537)
            ·
              refine ⟨41441886917675379246016903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55255849223567172328022537 41441886917675379246016903)
              ·
                refine ⟨62162830376513068869025355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41441886917675379246016903 62162830376513068869025355)
                ·
                  refine ⟨93244245564769603303538033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62162830376513068869025355 93244245564769603303538033)
                  ·
                    refine ⟨69933184173577202477653525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93244245564769603303538033 69933184173577202477653525)
                    ·
                      refine ⟨3278118008136431366140009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69933184173577202477653525 3278118008136431366140009)
                      ·
                        rfl

theorem cell23_6384112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_6384112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384112 prefixEnd_6384112 := by exact prefixLift 6384112
  have htrace : WordTrace (prefixWord ++ tailWord_6384112) baseStart_6384112 baseEnd_6384112 := by
    simpa [prefixWord, tailWord_6384112, baseEnd_6384112] using wordTrace_append hprefix tailTrace_6384112
  have hstable : (prefixWord ++ tailWord_6384112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384112).length < 2 ^ (prefixWord ++ tailWord_6384112).sum := by decide
  have hdescent : baseEnd_6384112 < baseStart_6384112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384139 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 3, 5]
def baseStart_6384139 : Nat := 118140960795 + 6384139 * 2 ^ 59
def prefixEnd_6384139 : Nat := 4983230072969 + 3 ^ 40 * 6384139 * 2
def baseEnd_6384139 : Nat := 1092710624038034253500795

theorem tailTrace_6384139 : CollatzResearch.WordTrace tailWord_6384139 prefixEnd_6384139 1092710624038034253500795 := by
  unfold tailWord_6384139
  simp only [CollatzResearch.WordTrace]
  refine ⟨232848678618362201981171471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155232452412241467987447647 232848678618362201981171471)
  ·
    refine ⟨349273017927543302971757207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232848678618362201981171471 349273017927543302971757207)
    ·
      refine ⟨523909526891314954457635811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349273017927543302971757207 523909526891314954457635811)
      ·
        refine ⟨785864290336972431686453717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523909526891314954457635811 785864290336972431686453717)
        ·
          refine ⟨18418694304772791367651259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 785864290336972431686453717 18418694304772791367651259)
          ·
            refine ⟨27628041457159187051476889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18418694304772791367651259 27628041457159187051476889)
            ·
              refine ⟨20721031092869390288607667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27628041457159187051476889 20721031092869390288607667)
              ·
                refine ⟨31081546639304085432911501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20721031092869390288607667 31081546639304085432911501)
                ·
                  refine ⟨11655579989739032037341813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31081546639304085432911501 11655579989739032037341813)
                  ·
                    refine ⟨1092710624038034253500795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11655579989739032037341813 1092710624038034253500795)
                    ·
                      rfl

theorem cell23_6384139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 5].length) (baseStart_6384139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384139 prefixEnd_6384139 := by exact prefixLift 6384139
  have htrace : WordTrace (prefixWord ++ tailWord_6384139) baseStart_6384139 baseEnd_6384139 := by
    simpa [prefixWord, tailWord_6384139, baseEnd_6384139] using wordTrace_append hprefix tailTrace_6384139
  have hstable : (prefixWord ++ tailWord_6384139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384139).length < 2 ^ (prefixWord ++ tailWord_6384139).sum := by decide
  have hdescent : baseEnd_6384139 < baseStart_6384139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384156 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_6384156 : Nat := 118140960795 + 6384156 * 2 ^ 59
def prefixEnd_6384156 : Nat := 4983230072969 + 3 ^ 40 * 6384156 * 2
def baseEnd_6384156 : Nat := 1092713533761743064663269

theorem tailTrace_6384156 : CollatzResearch.WordTrace tailWord_6384156 prefixEnd_6384156 1092713533761743064663269 := by
  unfold tailWord_6384156
  simp only [CollatzResearch.WordTrace]
  refine ⟨116424649329650306942270161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155232865772867075923026881 116424649329650306942270161)
  ·
    refine ⟨87318486997237730206702621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116424649329650306942270161 87318486997237730206702621)
    ·
      refine ⟨32744432623964148827513483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87318486997237730206702621 32744432623964148827513483)
      ·
        refine ⟨49116648935946223241270225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32744432623964148827513483 49116648935946223241270225)
        ·
          refine ⟨36837486701959667430952669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49116648935946223241270225 36837486701959667430952669)
          ·
            refine ⟨13814057513234875286607251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36837486701959667430952669 13814057513234875286607251)
            ·
              refine ⟨20721086269852312929910877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13814057513234875286607251 20721086269852312929910877)
              ·
                refine ⟨7770407351194617348716579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20721086269852312929910877 7770407351194617348716579)
                ·
                  refine ⟨11655611026791926023074869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770407351194617348716579 11655611026791926023074869)
                  ·
                    refine ⟨1092713533761743064663269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11655611026791926023074869 1092713533761743064663269)
                    ·
                      rfl

theorem cell23_6384156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_6384156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384156 prefixEnd_6384156 := by exact prefixLift 6384156
  have htrace : WordTrace (prefixWord ++ tailWord_6384156) baseStart_6384156 baseEnd_6384156 := by
    simpa [prefixWord, tailWord_6384156, baseEnd_6384156] using wordTrace_append hprefix tailTrace_6384156
  have hstable : (prefixWord ++ tailWord_6384156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384156).length < 2 ^ (prefixWord ++ tailWord_6384156).sum := by decide
  have hdescent : baseEnd_6384156 < baseStart_6384156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384170 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6384170 : Nat := 118140960795 + 6384170 * 2 ^ 59
def prefixEnd_6384170 : Nat := 4983230072969 + 3 ^ 40 * 6384170 * 2
def baseEnd_6384170 : Nat := 3278147790014392139214743

theorem tailTrace_6384170 : CollatzResearch.WordTrace tailWord_6384170 prefixEnd_6384170 3278147790014392139214743 := by
  unfold tailWord_6384170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58212452320312473568887491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155233206187499929517033309 58212452320312473568887491)
  ·
    refine ⟨87318678480468710353331237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58212452320312473568887491 87318678480468710353331237)
    ·
      refine ⟨16372252215087883191249607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87318678480468710353331237 16372252215087883191249607)
      ·
        refine ⟨24558378322631824786874411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16372252215087883191249607 24558378322631824786874411)
        ·
          refine ⟨36837567483947737180311617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24558378322631824786874411 36837567483947737180311617)
          ·
            refine ⟨27628175612960802885233713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36837567483947737180311617 27628175612960802885233713)
            ·
              refine ⟨20721131709720602163925285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27628175612960802885233713 20721131709720602163925285)
              ·
                refine ⟨3885212195572612905735991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20721131709720602163925285 3885212195572612905735991)
                ·
                  refine ⟨5827818293358919358603987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885212195572612905735991 5827818293358919358603987)
                  ·
                    refine ⟨8741727440038379037905981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5827818293358919358603987 8741727440038379037905981)
                    ·
                      refine ⟨3278147790014392139214743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741727440038379037905981 3278147790014392139214743)
                      ·
                        rfl

theorem cell23_6384170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6384170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384170 prefixEnd_6384170 := by exact prefixLift 6384170
  have htrace : WordTrace (prefixWord ++ tailWord_6384170) baseStart_6384170 baseEnd_6384170 := by
    simpa [prefixWord, tailWord_6384170, baseEnd_6384170] using wordTrace_append hprefix tailTrace_6384170
  have hstable : (prefixWord ++ tailWord_6384170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384170).length < 2 ^ (prefixWord ++ tailWord_6384170).sum := by decide
  have hdescent : baseEnd_6384170 < baseStart_6384170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384179 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5]
def baseStart_6384179 : Nat := 118140960795 + 6384179 * 2 ^ 59
def prefixEnd_6384179 : Nat := 4983230072969 + 3 ^ 40 * 6384179 * 2
def baseEnd_6384179 : Nat := 3278152411340282604002201

theorem tailTrace_6384179 : CollatzResearch.WordTrace tailWord_6384179 prefixEnd_6384179 3278152411340282604002201 := by
  unfold tailWord_6384179
  simp only [CollatzResearch.WordTrace]
  refine ⟨232850137538217288812627591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155233425025478192541751727 232850137538217288812627591)
  ·
    refine ⟨349275206307325933218941387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232850137538217288812627591 349275206307325933218941387)
    ·
      refine ⟨523912809460988899828412081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349275206307325933218941387 523912809460988899828412081)
      ·
        refine ⟨392934607095741674871309061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523912809460988899828412081 392934607095741674871309061)
        ·
          refine ⟨73675238830451564038370449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392934607095741674871309061 73675238830451564038370449)
          ·
            refine ⟨55256429122838673028777837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73675238830451564038370449 55256429122838673028777837)
            ·
              refine ⟨20721160921064502385791689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55256429122838673028777837 20721160921064502385791689)
              ·
                refine ⟨15540870690798376789343767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20721160921064502385791689 15540870690798376789343767)
                ·
                  refine ⟨23311306036197565184015651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15540870690798376789343767 23311306036197565184015651)
                  ·
                    refine ⟨34966959054296347776023477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23311306036197565184015651 34966959054296347776023477)
                    ·
                      refine ⟨3278152411340282604002201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34966959054296347776023477 3278152411340282604002201)
                      ·
                        rfl

theorem cell23_6384179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_6384179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384179 prefixEnd_6384179 := by exact prefixLift 6384179
  have htrace : WordTrace (prefixWord ++ tailWord_6384179) baseStart_6384179 baseEnd_6384179 := by
    simpa [prefixWord, tailWord_6384179, baseEnd_6384179] using wordTrace_append hprefix tailTrace_6384179
  have hstable : (prefixWord ++ tailWord_6384179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384179).length < 2 ^ (prefixWord ++ tailWord_6384179).sum := by decide
  have hdescent : baseEnd_6384179 < baseStart_6384179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384186 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_6384186 : Nat := 118140960795 + 6384186 * 2 ^ 59
def prefixEnd_6384186 : Nat := 4983230072969 + 3 ^ 40 * 6384186 * 2
def baseEnd_6384186 : Nat := 1092718668568288025538223

theorem tailTrace_6384186 : CollatzResearch.WordTrace tailWord_6384186 prefixEnd_6384186 1092718668568288025538223 := by
  unfold tailWord_6384186
  simp only [CollatzResearch.WordTrace]
  refine ⟨58212598212297982252033103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155233595232794619338754941 58212598212297982252033103)
  ·
    refine ⟨87318897318446973378049655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58212598212297982252033103 87318897318446973378049655)
    ·
      refine ⟨130978345977670460067074483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87318897318446973378049655 130978345977670460067074483)
      ·
        refine ⟨196467518966505690100611725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130978345977670460067074483 196467518966505690100611725)
        ·
          refine ⟨73675319612439633787729397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196467518966505690100611725 73675319612439633787729397)
          ·
            refine ⟨6907061213666215667599631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73675319612439633787729397 6907061213666215667599631)
            ·
              refine ⟨10360591820499323501399447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907061213666215667599631 10360591820499323501399447)
              ·
                refine ⟨15540887730748985252099171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10360591820499323501399447 15540887730748985252099171)
                ·
                  refine ⟨23311331596123477878148757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15540887730748985252099171 23311331596123477878148757)
                  ·
                    refine ⟨1092718668568288025538223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23311331596123477878148757 1092718668568288025538223)
                    ·
                      rfl

theorem cell23_6384186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_6384186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384186 prefixEnd_6384186 := by exact prefixLift 6384186
  have htrace : WordTrace (prefixWord ++ tailWord_6384186) baseStart_6384186 baseEnd_6384186 := by
    simpa [prefixWord, tailWord_6384186, baseEnd_6384186] using wordTrace_append hprefix tailTrace_6384186
  have hstable : (prefixWord ++ tailWord_6384186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384186).length < 2 ^ (prefixWord ++ tailWord_6384186).sum := by decide
  have hdescent : baseEnd_6384186 < baseStart_6384186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384190 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_6384190 : Nat := 118140960795 + 6384190 * 2 ^ 59
def prefixEnd_6384190 : Nat := 4983230072969 + 3 ^ 40 * 6384190 * 2
def baseEnd_6384190 : Nat := 1092719353209160686988217

theorem tailTrace_6384190 : CollatzResearch.WordTrace tailWord_6384190 prefixEnd_6384190 1092719353209160686988217 := by
  unfold tailWord_6384190
  simp only [CollatzResearch.WordTrace]
  refine ⟨29106317342647179711409753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155233692494118291794185349 29106317342647179711409753)
  ·
    refine ⟨21829738006985384783557315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29106317342647179711409753 21829738006985384783557315)
    ·
      refine ⟨32744607010478077175335973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21829738006985384783557315 32744607010478077175335973)
      ·
        refine ⟨6139613814464639470375495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32744607010478077175335973 6139613814464639470375495)
        ·
          refine ⟨9209420721696959205563243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139613814464639470375495 9209420721696959205563243)
          ·
            refine ⟨13814131082545438808344865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9209420721696959205563243 13814131082545438808344865)
            ·
              refine ⟨10360598311909079106258649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13814131082545438808344865 10360598311909079106258649)
              ·
                refine ⟨7770448733931809329693987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10360598311909079106258649 7770448733931809329693987)
                ·
                  refine ⟨11655673100897713994540981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770448733931809329693987 11655673100897713994540981)
                  ·
                    refine ⟨1092719353209160686988217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11655673100897713994540981 1092719353209160686988217)
                    ·
                      rfl

theorem cell23_6384190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_6384190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384190 prefixEnd_6384190 := by exact prefixLift 6384190
  have htrace : WordTrace (prefixWord ++ tailWord_6384190) baseStart_6384190 baseEnd_6384190 := by
    simpa [prefixWord, tailWord_6384190, baseEnd_6384190] using wordTrace_append hprefix tailTrace_6384190
  have hstable : (prefixWord ++ tailWord_6384190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384190).length < 2 ^ (prefixWord ++ tailWord_6384190).sum := by decide
  have hdescent : baseEnd_6384190 < baseStart_6384190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384193 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6384193 : Nat := 118140960795 + 6384193 * 2 ^ 59
def prefixEnd_6384193 : Nat := 4983230072969 + 3 ^ 40 * 6384193 * 2
def baseEnd_6384193 : Nat := 3278159600069445549227137

theorem tailTrace_6384193 : CollatzResearch.WordTrace tailWord_6384193 prefixEnd_6384193 3278159600069445549227137 := by
  unfold tailWord_6384193
  simp only [CollatzResearch.WordTrace]
  refine ⟨232850648160166569203637233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155233765440111046135758155 232850648160166569203637233)
  ·
    refine ⟨174637986120124926902727925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232850648160166569203637233 174637986120124926902727925)
    ·
      refine ⟨16372311198761711897130743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174637986120124926902727925 16372311198761711897130743)
      ·
        refine ⟨24558466798142567845696115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16372311198761711897130743 24558466798142567845696115)
        ·
          refine ⟨36837700197213851768544173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24558466798142567845696115 36837700197213851768544173)
          ·
            refine ⟨13814137573955194413204065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36837700197213851768544173 13814137573955194413204065)
            ·
              refine ⟨10360603180466395809903049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13814137573955194413204065 10360603180466395809903049)
              ·
                refine ⟨7770452385349796857427287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10360603180466395809903049 7770452385349796857427287)
                ·
                  refine ⟨11655678578024695286140931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770452385349796857427287 11655678578024695286140931)
                  ·
                    refine ⟨17483517867037042929211397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11655678578024695286140931 17483517867037042929211397)
                    ·
                      refine ⟨3278159600069445549227137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17483517867037042929211397 3278159600069445549227137)
                      ·
                        rfl

theorem cell23_6384193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6384193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384193 prefixEnd_6384193 := by exact prefixLift 6384193
  have htrace : WordTrace (prefixWord ++ tailWord_6384193) baseStart_6384193 baseEnd_6384193 := by
    simpa [prefixWord, tailWord_6384193, baseEnd_6384193] using wordTrace_append hprefix tailTrace_6384193
  have hstable : (prefixWord ++ tailWord_6384193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384193).length < 2 ^ (prefixWord ++ tailWord_6384193).sum := by decide
  have hdescent : baseEnd_6384193 < baseStart_6384193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384199 : List Nat := [1, 1, 4, 1, 4, 2, 1, 9]
def baseStart_6384199 : Nat := 118140960795 + 6384199 * 2 ^ 59
def prefixEnd_6384199 : Nat := 4983230072969 + 3 ^ 40 * 6384199 * 2
def baseEnd_6384199 : Nat := 121413432627902686138967

theorem tailTrace_6384199 : CollatzResearch.WordTrace tailWord_6384199 prefixEnd_6384199 121413432627902686138967 := by
  unfold tailWord_6384199
  simp only [CollatzResearch.WordTrace]
  refine ⟨232850866998144832228355651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155233911332096554818903767 232850866998144832228355651)
  ·
    refine ⟨349276300497217248342533477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232850866998144832228355651 349276300497217248342533477)
    ·
      refine ⟨65489306343228234064225027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349276300497217248342533477 65489306343228234064225027)
      ·
        refine ⟨98233959514842351096337541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65489306343228234064225027 98233959514842351096337541)
        ·
          refine ⟨18418867409032940830563289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98233959514842351096337541 18418867409032940830563289)
          ·
            refine ⟨13814150556774705622922467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18418867409032940830563289 13814150556774705622922467)
            ·
              refine ⟨20721225835162058434383701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13814150556774705622922467 20721225835162058434383701)
              ·
                refine ⟨121413432627902686138967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20721225835162058434383701 121413432627902686138967)
                ·
                  rfl

theorem cell23_6384199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 9].length) (baseStart_6384199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384199 prefixEnd_6384199 := by exact prefixLift 6384199
  have htrace : WordTrace (prefixWord ++ tailWord_6384199) baseStart_6384199 baseEnd_6384199 := by
    simpa [prefixWord, tailWord_6384199, baseEnd_6384199] using wordTrace_append hprefix tailTrace_6384199
  have hstable : (prefixWord ++ tailWord_6384199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384199).length < 2 ^ (prefixWord ++ tailWord_6384199).sum := by decide
  have hdescent : baseEnd_6384199 < baseStart_6384199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384227 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 1, 2, 2]
def baseStart_6384227 : Nat := 118140960795 + 6384227 * 2 ^ 59
def prefixEnd_6384227 : Nat := 4983230072969 + 3 ^ 40 * 6384227 * 2
def baseEnd_6384227 : Nat := 3278177058411698416201981

theorem tailTrace_6384227 : CollatzResearch.WordTrace tailWord_6384227 prefixEnd_6384227 3278177058411698416201981 := by
  unfold tailWord_6384227
  simp only [CollatzResearch.WordTrace]
  refine ⟨232851888242043393010374935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155234592161362262006916623 232851888242043393010374935)
  ·
    refine ⟨349277832363065089515562403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232851888242043393010374935 349277832363065089515562403)
    ·
      refine ⟨523916748544597634273343605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349277832363065089515562403 523916748544597634273343605)
      ·
        refine ⟨49117195176056028213125963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 523916748544597634273343605 49117195176056028213125963)
        ·
          refine ⟨73675792764084042319688945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49117195176056028213125963 73675792764084042319688945)
          ·
            refine ⟨55256844573063031739766709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73675792764084042319688945 55256844573063031739766709)
            ·
              refine ⟨5180329178724659225603129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55256844573063031739766709 5180329178724659225603129)
              ·
                refine ⟨3885246884043494419202347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180329178724659225603129 3885246884043494419202347)
                ·
                  refine ⟨5827870326065241628803521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885246884043494419202347 5827870326065241628803521)
                  ·
                    refine ⟨4370902744548931221602641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827870326065241628803521 4370902744548931221602641)
                    ·
                      refine ⟨3278177058411698416201981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370902744548931221602641 3278177058411698416201981)
                      ·
                        rfl

theorem cell23_6384227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_6384227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384227 prefixEnd_6384227 := by exact prefixLift 6384227
  have htrace : WordTrace (prefixWord ++ tailWord_6384227) baseStart_6384227 baseEnd_6384227 := by
    simpa [prefixWord, tailWord_6384227, baseEnd_6384227] using wordTrace_append hprefix tailTrace_6384227
  have hstable : (prefixWord ++ tailWord_6384227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384227).length < 2 ^ (prefixWord ++ tailWord_6384227).sum := by decide
  have hdescent : baseEnd_6384227 < baseStart_6384227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384316 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_6384316 : Nat := 118140960795 + 6384316 * 2 ^ 59
def prefixEnd_6384316 : Nat := 4983230072969 + 3 ^ 40 * 6384316 * 2
def baseEnd_6384316 : Nat := 3278222758189948567989071

theorem tailTrace_6384316 : CollatzResearch.WordTrace tailWord_6384316 prefixEnd_6384316 3278222758189948567989071 := by
  unfold tailWord_6384316
  simp only [CollatzResearch.WordTrace]
  refine ⟨116427567169360480605182401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155236756225813974140243201 116427567169360480605182401)
  ·
    refine ⟨87320675377020360453886801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116427567169360480605182401 87320675377020360453886801)
    ·
      refine ⟨65490506532765270340415101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87320675377020360453886801 65490506532765270340415101)
      ·
        refine ⟨24558939949786976377655663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65490506532765270340415101 24558939949786976377655663)
        ·
          refine ⟨36838409924680464566483495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24558939949786976377655663 36838409924680464566483495)
          ·
            refine ⟨55257614887020696849725243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36838409924680464566483495 55257614887020696849725243)
            ·
              refine ⟨82886422330531045274587865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55257614887020696849725243 82886422330531045274587865)
              ·
                refine ⟨62164816747898283955940899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82886422330531045274587865 62164816747898283955940899)
                ·
                  refine ⟨93247225121847425933911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62164816747898283955940899 93247225121847425933911349)
                  ·
                    refine ⟨8741927355173196181304189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93247225121847425933911349 8741927355173196181304189)
                    ·
                      refine ⟨3278222758189948567989071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8741927355173196181304189 3278222758189948567989071)
                      ·
                        rfl

theorem cell23_6384316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_6384316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384316 prefixEnd_6384316 := by exact prefixLift 6384316
  have htrace : WordTrace (prefixWord ++ tailWord_6384316) baseStart_6384316 baseEnd_6384316 := by
    simpa [prefixWord, tailWord_6384316, baseEnd_6384316] using wordTrace_append hprefix tailTrace_6384316
  have hstable : (prefixWord ++ tailWord_6384316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384316).length < 2 ^ (prefixWord ++ tailWord_6384316).sum := by decide
  have hdescent : baseEnd_6384316 < baseStart_6384316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384321 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6384321 : Nat := 118140960795 + 6384321 * 2 ^ 59
def prefixEnd_6384321 : Nat := 4983230072969 + 3 ^ 40 * 6384321 * 2
def baseEnd_6384321 : Nat := 3278225325593221048426549

theorem tailTrace_6384321 : CollatzResearch.WordTrace tailWord_6384321 prefixEnd_6384321 3278225325593221048426549 := by
  unfold tailWord_6384321
  simp only [CollatzResearch.WordTrace]
  refine ⟨232855316703702847064296817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155236877802468564709531211 232855316703702847064296817)
  ·
    refine ⟨174641487527777135298222613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232855316703702847064296817 174641487527777135298222613)
    ·
      refine ⟨8186319727864553217104185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174641487527777135298222613 8186319727864553217104185)
      ·
        refine ⟨6139739795898414912828139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8186319727864553217104185 6139739795898414912828139)
        ·
          refine ⟨9209609693847622369242209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139739795898414912828139 9209609693847622369242209)
          ·
            refine ⟨6907207270385716776931657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209609693847622369242209 6907207270385716776931657)
            ·
              refine ⟨5180405452789287582698743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6907207270385716776931657 5180405452789287582698743)
              ·
                refine ⟨7770608179183931374048115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180405452789287582698743 7770608179183931374048115)
                ·
                  refine ⟨11655912268775897061072173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770608179183931374048115 11655912268775897061072173)
                  ·
                    refine ⟨4370967100790961397902065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11655912268775897061072173 4370967100790961397902065)
                    ·
                      refine ⟨3278225325593221048426549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4370967100790961397902065 3278225325593221048426549)
                      ·
                        rfl

theorem cell23_6384321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6384321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384321 prefixEnd_6384321 := by exact prefixLift 6384321
  have htrace : WordTrace (prefixWord ++ tailWord_6384321) baseStart_6384321 baseEnd_6384321 := by
    simpa [prefixWord, tailWord_6384321, baseEnd_6384321] using wordTrace_append hprefix tailTrace_6384321
  have hstable : (prefixWord ++ tailWord_6384321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384321).length < 2 ^ (prefixWord ++ tailWord_6384321).sum := by decide
  have hdescent : baseEnd_6384321 < baseStart_6384321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384356 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_6384356 : Nat := 118140960795 + 6384356 * 2 ^ 59
def prefixEnd_6384356 : Nat := 4983230072969 + 3 ^ 40 * 6384356 * 2
def baseEnd_6384356 : Nat := 3278243297416128411488887

theorem tailTrace_6384356 : CollatzResearch.WordTrace tailWord_6384356 prefixEnd_6384356 3278243297416128411488887 := by
  unfold tailWord_6384356
  simp only [CollatzResearch.WordTrace]
  refine ⟨116428296629288024020910461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155237728839050698694547281 116428296629288024020910461)
  ·
    refine ⟨43660611235983009007841423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116428296629288024020910461 43660611235983009007841423)
    ·
      refine ⟨65490916853974513511762135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43660611235983009007841423 65490916853974513511762135)
      ·
        refine ⟨98236375280961770267643203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65490916853974513511762135 98236375280961770267643203)
        ·
          refine ⟨147354562921442655401464805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98236375280961770267643203 147354562921442655401464805)
          ·
            refine ⟨27628980547770497887774651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147354562921442655401464805 27628980547770497887774651)
            ·
              refine ⟨41443470821655746831661977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27628980547770497887774651 41443470821655746831661977)
              ·
                refine ⟨31082603116241810123746483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41443470821655746831661977 31082603116241810123746483)
                ·
                  refine ⟨46623904674362715185619725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31082603116241810123746483 46623904674362715185619725)
                  ·
                    refine ⟨17483964252886018194607397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46623904674362715185619725 17483964252886018194607397)
                    ·
                      refine ⟨3278243297416128411488887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17483964252886018194607397 3278243297416128411488887)
                      ·
                        rfl

theorem cell23_6384356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_6384356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384356 prefixEnd_6384356 := by exact prefixLift 6384356
  have htrace : WordTrace (prefixWord ++ tailWord_6384356) baseStart_6384356 baseEnd_6384356 := by
    simpa [prefixWord, tailWord_6384356, baseEnd_6384356] using wordTrace_append hprefix tailTrace_6384356
  have hstable : (prefixWord ++ tailWord_6384356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384356).length < 2 ^ (prefixWord ++ tailWord_6384356).sum := by decide
  have hdescent : baseEnd_6384356 < baseStart_6384356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384376 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_6384376 : Nat := 118140960795 + 6384376 * 2 ^ 59
def prefixEnd_6384376 : Nat := 4983230072969 + 3 ^ 40 * 6384376 * 2
def baseEnd_6384376 : Nat := 3278253567029218333238795

theorem tailTrace_6384376 : CollatzResearch.WordTrace tailWord_6384376 prefixEnd_6384376 3278253567029218333238795 := by
  unfold tailWord_6384376
  simp only [CollatzResearch.WordTrace]
  refine ⟨116428661359251795728774491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155238215145669060971699321 116428661359251795728774491)
  ·
    refine ⟨174642992038877693593161737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116428661359251795728774491 174642992038877693593161737)
    ·
      refine ⟨130982244029158270194871303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174642992038877693593161737 130982244029158270194871303)
      ·
        refine ⟨196473366043737405292306955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130982244029158270194871303 196473366043737405292306955)
        ·
          refine ⟨294710049065606107938460433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196473366043737405292306955 294710049065606107938460433)
          ·
            refine ⟨221032536799204580953845325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294710049065606107938460433 221032536799204580953845325)
            ·
              refine ⟨82887201299701717857691997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221032536799204580953845325 82887201299701717857691997)
              ·
                refine ⟨31082700487388144196634499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82887201299701717857691997 31082700487388144196634499)
                ·
                  refine ⟨46624050731082216294951749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31082700487388144196634499 46624050731082216294951749)
                  ·
                    refine ⟨8742009512077915555303453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46624050731082216294951749 8742009512077915555303453)
                    ·
                      refine ⟨3278253567029218333238795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8742009512077915555303453 3278253567029218333238795)
                      ·
                        rfl

theorem cell23_6384376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_6384376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384376 prefixEnd_6384376 := by exact prefixLift 6384376
  have htrace : WordTrace (prefixWord ++ tailWord_6384376) baseStart_6384376 baseEnd_6384376 := by
    simpa [prefixWord, tailWord_6384376, baseEnd_6384376] using wordTrace_append hprefix tailTrace_6384376
  have hstable : (prefixWord ++ tailWord_6384376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384376).length < 2 ^ (prefixWord ++ tailWord_6384376).sum := by decide
  have hdescent : baseEnd_6384376 < baseStart_6384376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384396 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 6]
def baseStart_6384396 : Nat := 118140960795 + 6384396 * 2 ^ 59
def prefixEnd_6384396 : Nat := 4983230072969 + 3 ^ 40 * 6384396 * 2
def baseEnd_6384396 : Nat := 364251537404700917220967

theorem tailTrace_6384396 : CollatzResearch.WordTrace tailWord_6384396 prefixEnd_6384396 364251537404700917220967 := by
  unfold tailWord_6384396
  simp only [CollatzResearch.WordTrace]
  refine ⟨116429026089215567436638521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155238701452287423248851361 116429026089215567436638521)
  ·
    refine ⟨87321769566911675577478891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116429026089215567436638521 87321769566911675577478891)
    ·
      refine ⟨130982654350367513366218337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87321769566911675577478891 130982654350367513366218337)
      ·
        refine ⟨98236990762775635024663753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130982654350367513366218337 98236990762775635024663753)
        ·
          refine ⟨73677743072081726268497815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98236990762775635024663753 73677743072081726268497815)
          ·
            refine ⟨110516614608122589402746723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73677743072081726268497815 110516614608122589402746723)
            ·
              refine ⟨165774921912183884104120085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110516614608122589402746723 165774921912183884104120085)
              ·
                refine ⟨7770699464633619567380629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165774921912183884104120085 7770699464633619567380629)
                ·
                  refine ⟨364251537404700917220967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7770699464633619567380629 364251537404700917220967)
                  ·
                    rfl

theorem cell23_6384396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_6384396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384396 prefixEnd_6384396 := by exact prefixLift 6384396
  have htrace : WordTrace (prefixWord ++ tailWord_6384396) baseStart_6384396 baseEnd_6384396 := by
    simpa [prefixWord, tailWord_6384396, baseEnd_6384396] using wordTrace_append hprefix tailTrace_6384396
  have hstable : (prefixWord ++ tailWord_6384396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384396).length < 2 ^ (prefixWord ++ tailWord_6384396).sum := by decide
  have hdescent : baseEnd_6384396 < baseStart_6384396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384456 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_6384456 : Nat := 118140960795 + 6384456 * 2 ^ 59
def prefixEnd_6384456 : Nat := 4983230072969 + 3 ^ 40 * 6384456 * 2
def baseEnd_6384456 : Nat := 1092764881827192673412809

theorem tailTrace_6384456 : CollatzResearch.WordTrace tailWord_6384456 prefixEnd_6384456 1092764881827192673412809 := by
  unfold tailWord_6384456
  simp only [CollatzResearch.WordTrace]
  refine ⟨116430120279106882560230611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155240160372142510080307481 116430120279106882560230611)
  ·
    refine ⟨174645180418660323840345917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116430120279106882560230611 174645180418660323840345917)
    ·
      refine ⟨65491942656997621440129719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174645180418660323840345917 65491942656997621440129719)
      ·
        refine ⟨98237913985496432160194579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65491942656997621440129719 98237913985496432160194579)
        ·
          refine ⟨147356870978244648240291869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98237913985496432160194579 147356870978244648240291869)
          ·
            refine ⟨55258826616841743090109451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147356870978244648240291869 55258826616841743090109451)
            ·
              refine ⟨82888239925262614635164177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55258826616841743090109451 82888239925262614635164177)
              ·
                refine ⟨62166179943946960976373133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82888239925262614635164177 62166179943946960976373133)
                ·
                  refine ⟨23312317478980110366139925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62166179943946960976373133 23312317478980110366139925)
                  ·
                    refine ⟨1092764881827192673412809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23312317478980110366139925 1092764881827192673412809)
                    ·
                      rfl

theorem cell23_6384456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_6384456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384456 prefixEnd_6384456 := by exact prefixLift 6384456
  have htrace : WordTrace (prefixWord ++ tailWord_6384456) baseStart_6384456 baseEnd_6384456 := by
    simpa [prefixWord, tailWord_6384456, baseEnd_6384456] using wordTrace_append hprefix tailTrace_6384456
  have hstable : (prefixWord ++ tailWord_6384456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384456).length < 2 ^ (prefixWord ++ tailWord_6384456).sum := by decide
  have hdescent : baseEnd_6384456 < baseStart_6384456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384457 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 1, 1, 3]
def baseStart_6384457 : Nat := 118140960795 + 6384457 * 2 ^ 59
def prefixEnd_6384457 : Nat := 4983230072969 + 3 ^ 40 * 6384457 * 2
def baseEnd_6384457 : Nat := 3278295158962232516325923

theorem tailTrace_6384457 : CollatzResearch.WordTrace tailWord_6384457 prefixEnd_6384457 3278295158962232516325923 := by
  unfold tailWord_6384457
  simp only [CollatzResearch.WordTrace]
  refine ⟨232860277031210142291247625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155240184687473428194165083 232860277031210142291247625)
  ·
    refine ⟨174645207773407606718435719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232860277031210142291247625 174645207773407606718435719)
    ·
      refine ⟨261967811660111410077653579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174645207773407606718435719 261967811660111410077653579)
      ·
        refine ⟨392951717490167115116480369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261967811660111410077653579 392951717490167115116480369)
        ·
          refine ⟨294713788117625336337360277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392951717490167115116480369 294713788117625336337360277)
          ·
            refine ⟨13814708818013687640813763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 294713788117625336337360277 13814708818013687640813763)
            ·
              refine ⟨20722063227020531461220645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13814708818013687640813763 20722063227020531461220645)
              ·
                refine ⟨3885386855066349648978871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20722063227020531461220645 3885386855066349648978871)
                ·
                  refine ⟨5828080282599524473468307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885386855066349648978871 5828080282599524473468307)
                  ·
                    refine ⟨8742120423899286710202461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828080282599524473468307 8742120423899286710202461)
                    ·
                      refine ⟨3278295158962232516325923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8742120423899286710202461 3278295158962232516325923)
                      ·
                        rfl

theorem cell23_6384457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 1, 3].length) (baseStart_6384457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384457 prefixEnd_6384457 := by exact prefixLift 6384457
  have htrace : WordTrace (prefixWord ++ tailWord_6384457) baseStart_6384457 baseEnd_6384457 := by
    simpa [prefixWord, tailWord_6384457, baseEnd_6384457] using wordTrace_append hprefix tailTrace_6384457
  have hstable : (prefixWord ++ tailWord_6384457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384457).length < 2 ^ (prefixWord ++ tailWord_6384457).sum := by decide
  have hdescent : baseEnd_6384457 < baseStart_6384457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384473 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 1, 6]
def baseStart_6384473 : Nat := 118140960795 + 6384473 * 2 ^ 59
def prefixEnd_6384473 : Nat := 4983230072969 + 3 ^ 40 * 6384473 * 2
def baseEnd_6384473 : Nat := 1092767791550901484575283

theorem tailTrace_6384473 : CollatzResearch.WordTrace tailWord_6384473 prefixEnd_6384473 1092767791550901484575283 := by
  unfold tailWord_6384473
  simp only [CollatzResearch.WordTrace]
  refine ⟨232860860599152177023830073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155240573732768118015886715 232860860599152177023830073)
  ·
    refine ⟨174645645449364132767872555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232860860599152177023830073 174645645449364132767872555)
    ·
      refine ⟨261968468174046199151808833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174645645449364132767872555 261968468174046199151808833)
      ·
        refine ⟨196476351130534649363856625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261968468174046199151808833 196476351130534649363856625)
        ·
          refine ⟨147357263347900987022892469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196476351130534649363856625 147357263347900987022892469)
          ·
            refine ⟨13814743438865717533396169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147357263347900987022892469 13814743438865717533396169)
            ·
              refine ⟨10361057579149288150047127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13814743438865717533396169 10361057579149288150047127)
              ·
                refine ⟨15541586368723932225070691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10361057579149288150047127 15541586368723932225070691)
                ·
                  refine ⟨23312379553085898337606037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15541586368723932225070691 23312379553085898337606037)
                  ·
                    refine ⟨1092767791550901484575283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23312379553085898337606037 1092767791550901484575283)
                    ·
                      rfl

theorem cell23_6384473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_6384473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384473 prefixEnd_6384473 := by exact prefixLift 6384473
  have htrace : WordTrace (prefixWord ++ tailWord_6384473) baseStart_6384473 baseEnd_6384473 := by
    simpa [prefixWord, tailWord_6384473, baseEnd_6384473] using wordTrace_append hprefix tailTrace_6384473
  have hstable : (prefixWord ++ tailWord_6384473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384473).length < 2 ^ (prefixWord ++ tailWord_6384473).sum := by decide
  have hdescent : baseEnd_6384473 < baseStart_6384473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384494 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_6384494 : Nat := 118140960795 + 6384494 * 2 ^ 59
def prefixEnd_6384494 : Nat := 4983230072969 + 3 ^ 40 * 6384494 * 2
def baseEnd_6384494 : Nat := 1092771385915482957187751

theorem tailTrace_6384494 : CollatzResearch.WordTrace tailWord_6384494 prefixEnd_6384494 1092771385915482957187751 := by
  unfold tailWord_6384494
  simp only [CollatzResearch.WordTrace]
  refine ⟨29107703316509512201293067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155241084354717398406896357 29107703316509512201293067)
  ·
    refine ⟨43661554974764268301939601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29107703316509512201293067 43661554974764268301939601)
    ·
      refine ⟨32746166231073201226454701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43661554974764268301939601 32746166231073201226454701)
      ·
        refine ⟨12279812336652450459920513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32746166231073201226454701 12279812336652450459920513)
        ·
          refine ⟨9209859252489337844940385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12279812336652450459920513 9209859252489337844940385)
          ·
            refine ⟨6907394439367003383705289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209859252489337844940385 6907394439367003383705289)
            ·
              refine ⟨5180545829525252537778967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6907394439367003383705289 5180545829525252537778967)
              ·
                refine ⟨7770818744287878806668451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180545829525252537778967 7770818744287878806668451)
                ·
                  refine ⟨11656228116431818210002677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770818744287878806668451 11656228116431818210002677)
                  ·
                    refine ⟨1092771385915482957187751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11656228116431818210002677 1092771385915482957187751)
                    ·
                      rfl

theorem cell23_6384494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_6384494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384494 prefixEnd_6384494 := by exact prefixLift 6384494
  have htrace : WordTrace (prefixWord ++ tailWord_6384494) baseStart_6384494 baseEnd_6384494 := by
    simpa [prefixWord, tailWord_6384494, baseEnd_6384494] using wordTrace_append hprefix tailTrace_6384494
  have hstable : (prefixWord ++ tailWord_6384494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384494).length < 2 ^ (prefixWord ++ tailWord_6384494).sum := by decide
  have hdescent : baseEnd_6384494 < baseStart_6384494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384497 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 1, 1, 4]
def baseStart_6384497 : Nat := 118140960795 + 6384497 * 2 ^ 59
def prefixEnd_6384497 : Nat := 4983230072969 + 3 ^ 40 * 6384497 * 2
def baseEnd_6384497 : Nat := 3278315698188412359825739

theorem tailTrace_6384497 : CollatzResearch.WordTrace tailWord_6384497 prefixEnd_6384497 3278315698188412359825739 := by
  unfold tailWord_6384497
  simp only [CollatzResearch.WordTrace]
  refine ⟨232861735951065229122703745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155241157300710152748469163 232861735951065229122703745)
  ·
    refine ⟨174646301963298921842027809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232861735951065229122703745 174646301963298921842027809)
    ·
      refine ⟨130984726472474191381520857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174646301963298921842027809 130984726472474191381520857)
      ·
        refine ⟨98238544854355643536140643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130984726472474191381520857 98238544854355643536140643)
        ·
          refine ⟨147357817281533465304210965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98238544854355643536140643 147357817281533465304210965)
          ·
            refine ⟨6907397685071881186134889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147357817281533465304210965 6907397685071881186134889)
            ·
              refine ⟨5180548263803910889601167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6907397685071881186134889 5180548263803910889601167)
              ·
                refine ⟨7770822395705866334401751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180548263803910889601167 7770822395705866334401751)
                ·
                  refine ⟨11656233593558799501602627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770822395705866334401751 11656233593558799501602627)
                  ·
                    refine ⟨17484350390338199252403941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11656233593558799501602627 17484350390338199252403941)
                    ·
                      refine ⟨3278315698188412359825739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17484350390338199252403941 3278315698188412359825739)
                      ·
                        rfl

theorem cell23_6384497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_6384497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384497 prefixEnd_6384497 := by exact prefixLift 6384497
  have htrace : WordTrace (prefixWord ++ tailWord_6384497) baseStart_6384497 baseEnd_6384497 := by
    simpa [prefixWord, tailWord_6384497, baseEnd_6384497] using wordTrace_append hprefix tailTrace_6384497
  have hstable : (prefixWord ++ tailWord_6384497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384497).length < 2 ^ (prefixWord ++ tailWord_6384497).sum := by decide
  have hdescent : baseEnd_6384497 < baseStart_6384497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384506 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_6384506 : Nat := 118140960795 + 6384506 * 2 ^ 59
def prefixEnd_6384506 : Nat := 4983230072969 + 3 ^ 40 * 6384506 * 2
def baseEnd_6384506 : Nat := 3278320319514302824613197

theorem tailTrace_6384506 : CollatzResearch.WordTrace tailWord_6384506 prefixEnd_6384506 3278320319514302824613197 := by
  unfold tailWord_6384506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58215516052008155914945343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155241376138688415773187581 58215516052008155914945343)
  ·
    refine ⟨87323274078012233872418015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58215516052008155914945343 87323274078012233872418015)
    ·
      refine ⟨130984911117018350808627023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87323274078012233872418015 130984911117018350808627023)
      ·
        refine ⟨196477366675527526212940535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130984911117018350808627023 196477366675527526212940535)
        ·
          refine ⟨294716050013291289319410803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196477366675527526212940535 294716050013291289319410803)
          ·
            refine ⟨442074075019936933979116205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294716050013291289319410803 442074075019936933979116205)
            ·
              refine ⟨165777778132476350242168577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442074075019936933979116205 165777778132476350242168577)
              ·
                refine ⟨124333333599357262681626433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165777778132476350242168577 124333333599357262681626433)
                ·
                  refine ⟨93250000199517947011219825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124333333599357262681626433 93250000199517947011219825)
                  ·
                    refine ⟨69937500149638460258414869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93250000199517947011219825 69937500149638460258414869)
                    ·
                      refine ⟨3278320319514302824613197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69937500149638460258414869 3278320319514302824613197)
                      ·
                        rfl

theorem cell23_6384506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_6384506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384506 prefixEnd_6384506 := by exact prefixLift 6384506
  have htrace : WordTrace (prefixWord ++ tailWord_6384506) baseStart_6384506 baseEnd_6384506 := by
    simpa [prefixWord, tailWord_6384506, baseEnd_6384506] using wordTrace_append hprefix tailTrace_6384506
  have hstable : (prefixWord ++ tailWord_6384506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384506).length < 2 ^ (prefixWord ++ tailWord_6384506).sum := by decide
  have hdescent : baseEnd_6384506 < baseStart_6384506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384543 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6384543 : Nat := 118140960795 + 6384543 * 2 ^ 59
def prefixEnd_6384543 : Nat := 4983230072969 + 3 ^ 40 * 6384543 * 2
def baseEnd_6384543 : Nat := 3278339318298519179850527

theorem tailTrace_6384543 : CollatzResearch.WordTrace tailWord_6384543 prefixEnd_6384543 3278339318298519179850527 := by
  unfold tailWord_6384543
  simp only [CollatzResearch.WordTrace]
  refine ⟨232863413708898578978878283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155242275805932385985918855 232863413708898578978878283)
  ·
    refine ⟨349295120563347868468317425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232863413708898578978878283 349295120563347868468317425)
    ·
      refine ⟨261971340422510901351238069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349295120563347868468317425 261971340422510901351238069)
      ·
        refine ⟨24559813164610397001678569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261971340422510901351238069 24559813164610397001678569)
        ·
          refine ⟨18419859873457797751258927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24559813164610397001678569 18419859873457797751258927)
          ·
            refine ⟨27629789810186696626888391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18419859873457797751258927 27629789810186696626888391)
            ·
              refine ⟨41444684715280044940332587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27629789810186696626888391 41444684715280044940332587)
              ·
                refine ⟨62167027072920067410498881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41444684715280044940332587 62167027072920067410498881)
                ·
                  refine ⟨46625270304690050557874161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62167027072920067410498881 46625270304690050557874161)
                  ·
                    refine ⟨34968952728517537918405621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46625270304690050557874161 34968952728517537918405621)
                    ·
                      refine ⟨3278339318298519179850527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34968952728517537918405621 3278339318298519179850527)
                      ·
                        rfl

theorem cell23_6384543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6384543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384543 prefixEnd_6384543 := by exact prefixLift 6384543
  have htrace : WordTrace (prefixWord ++ tailWord_6384543) baseStart_6384543 baseEnd_6384543 := by
    simpa [prefixWord, tailWord_6384543, baseEnd_6384543] using wordTrace_append hprefix tailTrace_6384543
  have hstable : (prefixWord ++ tailWord_6384543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384543).length < 2 ^ (prefixWord ++ tailWord_6384543).sum := by decide
  have hdescent : baseEnd_6384543 < baseStart_6384543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384564 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_6384564 : Nat := 118140960795 + 6384564 * 2 ^ 59
def prefixEnd_6384564 : Nat := 4983230072969 + 3 ^ 40 * 6384564 * 2
def baseEnd_6384564 : Nat := 3278350101392263597687931

theorem tailTrace_6384564 : CollatzResearch.WordTrace tailWord_6384564 prefixEnd_6384564 3278350101392263597687931 := by
  unfold tailWord_6384564
  simp only [CollatzResearch.WordTrace]
  refine ⟨116432089820911249782696373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155242786427881666376928497 116432089820911249782696373)
  ·
    refine ⟨10915508420710429667127785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116432089820911249782696373 10915508420710429667127785)
    ·
      refine ⟨8186631315532822250345839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10915508420710429667127785 8186631315532822250345839)
      ·
        refine ⟨12279946973299233375518759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8186631315532822250345839 12279946973299233375518759)
        ·
          refine ⟨18419920459948850063278139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12279946973299233375518759 18419920459948850063278139)
          ·
            refine ⟨27629880689923275094917209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18419920459948850063278139 27629880689923275094917209)
            ·
              refine ⟨20722410517442456321187907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27629880689923275094917209 20722410517442456321187907)
              ·
                refine ⟨31083615776163684481781861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20722410517442456321187907 31083615776163684481781861)
                ·
                  refine ⟨5828177958030690840334099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31083615776163684481781861 5828177958030690840334099)
                  ·
                    refine ⟨8742266937046036260501149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828177958030690840334099 8742266937046036260501149)
                    ·
                      refine ⟨3278350101392263597687931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8742266937046036260501149 3278350101392263597687931)
                      ·
                        rfl

theorem cell23_6384564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_6384564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384564 prefixEnd_6384564 := by exact prefixLift 6384564
  have htrace : WordTrace (prefixWord ++ tailWord_6384564) baseStart_6384564 baseEnd_6384564 := by
    simpa [prefixWord, tailWord_6384564, baseEnd_6384564] using wordTrace_append hprefix tailTrace_6384564
  have hstable : (prefixWord ++ tailWord_6384564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384564).length < 2 ^ (prefixWord ++ tailWord_6384564).sum := by decide
  have hdescent : baseEnd_6384564 < baseStart_6384564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384583 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_6384583 : Nat := 118140960795 + 6384583 * 2 ^ 59
def prefixEnd_6384583 : Nat := 4983230072969 + 3 ^ 40 * 6384583 * 2
def baseEnd_6384583 : Nat := 3278359857524699023350343

theorem tailTrace_6384583 : CollatzResearch.WordTrace tailWord_6384583 prefixEnd_6384583 3278359857524699023350343 := by
  unfold tailWord_6384583
  simp only [CollatzResearch.WordTrace]
  refine ⟨232864872628753665810334403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155243248419169110540222935 232864872628753665810334403)
  ·
    refine ⟨349297308943130498715501605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232864872628753665810334403 349297308943130498715501605)
    ·
      refine ⟨65493245426836968509156551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349297308943130498715501605 65493245426836968509156551)
      ·
        refine ⟨98239868140255452763734827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65493245426836968509156551 98239868140255452763734827)
        ·
          refine ⟨147359802210383179145602241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98239868140255452763734827 147359802210383179145602241)
          ·
            refine ⟨110519851657787384359201681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147359802210383179145602241 110519851657787384359201681)
            ·
              refine ⟨82889888743340538269401261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110519851657787384359201681 82889888743340538269401261)
              ·
                refine ⟨31083708278752701851025473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82889888743340538269401261 31083708278752701851025473)
                ·
                  refine ⟨23312781209064526388269105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31083708278752701851025473 23312781209064526388269105)
                  ·
                    refine ⟨17484585906798394791201829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23312781209064526388269105 17484585906798394791201829)
                    ·
                      refine ⟨3278359857524699023350343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17484585906798394791201829 3278359857524699023350343)
                      ·
                        rfl

theorem cell23_6384583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_6384583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384583 prefixEnd_6384583 := by exact prefixLift 6384583
  have htrace : WordTrace (prefixWord ++ tailWord_6384583) baseStart_6384583 baseEnd_6384583 := by
    simpa [prefixWord, tailWord_6384583, baseEnd_6384583] using wordTrace_append hprefix tailTrace_6384583
  have hstable : (prefixWord ++ tailWord_6384583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384583).length < 2 ^ (prefixWord ++ tailWord_6384583).sum := by decide
  have hdescent : baseEnd_6384583 < baseStart_6384583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384633 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_6384633 : Nat := 118140960795 + 6384633 * 2 ^ 59
def prefixEnd_6384633 : Nat := 4983230072969 + 3 ^ 40 * 6384633 * 2
def baseEnd_6384633 : Nat := 3278385531557423827725113

theorem tailTrace_6384633 : CollatzResearch.WordTrace tailWord_6384633 prefixEnd_6384633 3278385531557423827725113 := by
  unfold tailWord_6384633
  simp only [CollatzResearch.WordTrace]
  refine ⟨232866696278572524349654553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155244464185715016233103035 232866696278572524349654553)
  ·
    refine ⟨174650022208929393262240915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232866696278572524349654553 174650022208929393262240915)
    ·
      refine ⟨261975033313394089893361373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174650022208929393262240915 261975033313394089893361373)
      ·
        refine ⟨98240637492522783710010515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261975033313394089893361373 98240637492522783710010515)
        ·
          refine ⟨147360956238784175565015773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98240637492522783710010515 147360956238784175565015773)
          ·
            refine ⟨55260358589544065836880915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147360956238784175565015773 55260358589544065836880915)
            ·
              refine ⟨82890537884316098755321373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55260358589544065836880915 82890537884316098755321373)
              ·
                refine ⟨31083951706618537033245515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82890537884316098755321373 31083951706618537033245515)
                ·
                  refine ⟨46625927559927805549868273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31083951706618537033245515 46625927559927805549868273)
                  ·
                    refine ⟨34969445669945854162401205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46625927559927805549868273 34969445669945854162401205)
                    ·
                      refine ⟨3278385531557423827725113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34969445669945854162401205 3278385531557423827725113)
                      ·
                        rfl

theorem cell23_6384633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_6384633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384633 prefixEnd_6384633 := by exact prefixLift 6384633
  have htrace : WordTrace (prefixWord ++ tailWord_6384633) baseStart_6384633 baseEnd_6384633 := by
    simpa [prefixWord, tailWord_6384633, baseEnd_6384633] using wordTrace_append hprefix tailTrace_6384633
  have hstable : (prefixWord ++ tailWord_6384633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384633).length < 2 ^ (prefixWord ++ tailWord_6384633).sum := by decide
  have hdescent : baseEnd_6384633 < baseStart_6384633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384683 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 8]
def baseStart_6384683 : Nat := 118140960795 + 6384683 * 2 ^ 59
def prefixEnd_6384683 : Nat := 4983230072969 + 3 ^ 40 * 6384683 * 2
def baseEnd_6384683 : Nat := 364267911732238736899987

theorem tailTrace_6384683 : CollatzResearch.WordTrace tailWord_6384683 prefixEnd_6384683 364267911732238736899987 := by
  unfold tailWord_6384683
  simp only [CollatzResearch.WordTrace]
  refine ⟨232868519928391382888974703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155245679952260921925983135 232868519928391382888974703)
  ·
    refine ⟨349302779892587074333462055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232868519928391382888974703 349302779892587074333462055)
    ·
      refine ⟨523954169838880611500193083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349302779892587074333462055 523954169838880611500193083)
      ·
        refine ⟨785931254758320917250289625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523954169838880611500193083 785931254758320917250289625)
        ·
          refine ⟨589448441068740687937717219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785931254758320917250289625 589448441068740687937717219)
          ·
            refine ⟨884172661603111031906575829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589448441068740687937717219 884172661603111031906575829)
            ·
              refine ⟨20722796756322914810310371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 884172661603111031906575829 20722796756322914810310371)
              ·
                refine ⟨31084195134484372215465557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20722796756322914810310371 31084195134484372215465557)
                ·
                  refine ⟨364267911732238736899987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31084195134484372215465557 364267911732238736899987)
                  ·
                    rfl

theorem cell23_6384683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 8].length) (baseStart_6384683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384683 prefixEnd_6384683 := by exact prefixLift 6384683
  have htrace : WordTrace (prefixWord ++ tailWord_6384683) baseStart_6384683 baseEnd_6384683 := by
    simpa [prefixWord, tailWord_6384683, baseEnd_6384683] using wordTrace_append hprefix tailTrace_6384683
  have hstable : (prefixWord ++ tailWord_6384683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384683).length < 2 ^ (prefixWord ++ tailWord_6384683).sum := by decide
  have hdescent : baseEnd_6384683 < baseStart_6384683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384694 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6384694 : Nat := 118140960795 + 6384694 * 2 ^ 59
def prefixEnd_6384694 : Nat := 4983230072969 + 3 ^ 40 * 6384694 * 2
def baseEnd_6384694 : Nat := 3278416853877348089062333

theorem tailTrace_6384694 : CollatzResearch.WordTrace tailWord_6384694 prefixEnd_6384694 3278416853877348089062333 := by
  unfold tailWord_6384694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554307570709470735476571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155245947420901021178416757 14554307570709470735476571)
  ·
    refine ⟨21831461356064206103214857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14554307570709470735476571 21831461356064206103214857)
    ·
      refine ⟨16373596017048154577411143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21831461356064206103214857 16373596017048154577411143)
      ·
        refine ⟨24560394025572231866116715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16373596017048154577411143 24560394025572231866116715)
        ·
          refine ⟨36840591038358347799175073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24560394025572231866116715 36840591038358347799175073)
          ·
            refine ⟨27630443278768760849381305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36840591038358347799175073 27630443278768760849381305)
            ·
              refine ⟨20722832459076570637035979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27630443278768760849381305 20722832459076570637035979)
              ·
                refine ⟨31084248688614855955553969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20722832459076570637035979 31084248688614855955553969)
                ·
                  refine ⟨23313186516461141966665477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31084248688614855955553969 23313186516461141966665477)
                  ·
                    refine ⟨4371222471836464118749777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23313186516461141966665477 4371222471836464118749777)
                    ·
                      refine ⟨3278416853877348089062333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371222471836464118749777 3278416853877348089062333)
                      ·
                        rfl

theorem cell23_6384694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6384694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384694 prefixEnd_6384694 := by exact prefixLift 6384694
  have htrace : WordTrace (prefixWord ++ tailWord_6384694) baseStart_6384694 baseEnd_6384694 := by
    simpa [prefixWord, tailWord_6384694, baseEnd_6384694] using wordTrace_append hprefix tailTrace_6384694
  have hstable : (prefixWord ++ tailWord_6384694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384694).length < 2 ^ (prefixWord ++ tailWord_6384694).sum := by decide
  have hdescent : baseEnd_6384694 < baseStart_6384694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384703 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_6384703 : Nat := 118140960795 + 6384703 * 2 ^ 59
def prefixEnd_6384703 : Nat := 4983230072969 + 3 ^ 40 * 6384703 * 2
def baseEnd_6384703 : Nat := 3278421475203238553849791

theorem tailTrace_6384703 : CollatzResearch.WordTrace tailWord_6384703 prefixEnd_6384703 3278421475203238553849791 := by
  unfold tailWord_6384703
  simp only [CollatzResearch.WordTrace]
  refine ⟨232869249388318926304702763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155246166258879284203135175 232869249388318926304702763)
  ·
    refine ⟨349303874082478389457054145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232869249388318926304702763 349303874082478389457054145)
    ·
      refine ⟨261977905561858792092790609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349303874082478389457054145 261977905561858792092790609)
      ·
        refine ⟨196483429171394094069592957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261977905561858792092790609 196483429171394094069592957)
        ·
          refine ⟨73681285939272785276097359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196483429171394094069592957 73681285939272785276097359)
          ·
            refine ⟨110521928908909177914146039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73681285939272785276097359 110521928908909177914146039)
            ·
              refine ⟨165782893363363766871219059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110521928908909177914146039 165782893363363766871219059)
              ·
                refine ⟨248674340045045650306828589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165782893363363766871219059 248674340045045650306828589)
                ·
                  refine ⟨93252877516892118865060721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248674340045045650306828589 93252877516892118865060721)
                  ·
                    refine ⟨69939658137669089148795541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93252877516892118865060721 69939658137669089148795541)
                    ·
                      refine ⟨3278421475203238553849791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69939658137669089148795541 3278421475203238553849791)
                      ·
                        rfl

theorem cell23_6384703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_6384703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384703 prefixEnd_6384703 := by exact prefixLift 6384703
  have htrace : WordTrace (prefixWord ++ tailWord_6384703) baseStart_6384703 baseEnd_6384703 := by
    simpa [prefixWord, tailWord_6384703, baseEnd_6384703] using wordTrace_append hprefix tailTrace_6384703
  have hstable : (prefixWord ++ tailWord_6384703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384703).length < 2 ^ (prefixWord ++ tailWord_6384703).sum := by decide
  have hdescent : baseEnd_6384703 < baseStart_6384703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384723 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_6384723 : Nat := 118140960795 + 6384723 * 2 ^ 59
def prefixEnd_6384723 : Nat := 4983230072969 + 3 ^ 40 * 6384723 * 2
def baseEnd_6384723 : Nat := 3278431744816328475599699

theorem tailTrace_6384723 : CollatzResearch.WordTrace tailWord_6384723 prefixEnd_6384723 3278431744816328475599699 := by
  unfold tailWord_6384723
  simp only [CollatzResearch.WordTrace]
  refine ⟨232869978848246469720430823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155246652565497646480287215 232869978848246469720430823)
  ·
    refine ⟨349304968272369704580646235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232869978848246469720430823 349304968272369704580646235)
    ·
      refine ⟨523957452408554556870969353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349304968272369704580646235 523957452408554556870969353)
      ·
        refine ⟨392968089306415917653227015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523957452408554556870969353 392968089306415917653227015)
        ·
          refine ⟨589452133959623876479840523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392968089306415917653227015 589452133959623876479840523)
          ·
            refine ⟨884178200939435814719760785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589452133959623876479840523 884178200939435814719760785)
            ·
              refine ⟨663133650704576861039820589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884178200939435814719760785 663133650704576861039820589)
              ·
                refine ⟨248675119014216322889932721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663133650704576861039820589 248675119014216322889932721)
                ·
                  refine ⟨186506339260662242167449541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248675119014216322889932721 186506339260662242167449541)
                  ·
                    refine ⟨34969938611374170406396789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186506339260662242167449541 34969938611374170406396789)
                    ·
                      refine ⟨3278431744816328475599699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34969938611374170406396789 3278431744816328475599699)
                      ·
                        rfl

theorem cell23_6384723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_6384723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384723 prefixEnd_6384723 := by exact prefixLift 6384723
  have htrace : WordTrace (prefixWord ++ tailWord_6384723) baseStart_6384723 baseEnd_6384723 := by
    simpa [prefixWord, tailWord_6384723, baseEnd_6384723] using wordTrace_append hprefix tailTrace_6384723
  have hstable : (prefixWord ++ tailWord_6384723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384723).length < 2 ^ (prefixWord ++ tailWord_6384723).sum := by decide
  have hdescent : baseEnd_6384723 < baseStart_6384723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384734 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6384734 : Nat := 118140960795 + 6384734 * 2 ^ 59
def prefixEnd_6384734 : Nat := 4983230072969 + 3 ^ 40 * 6384734 * 2
def baseEnd_6384734 : Nat := 364270821455947548062461

theorem tailTrace_6384734 : CollatzResearch.WordTrace tailWord_6384734 prefixEnd_6384734 364270821455947548062461 := by
  unfold tailWord_6384734
  simp only [CollatzResearch.WordTrace]
  refine ⟨29108797506400827324885157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155246920034137745732720837 29108797506400827324885157)
  ·
    refine ⟨5457899532450155123415967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29108797506400827324885157 5457899532450155123415967)
    ·
      refine ⟨8186849298675232685123951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457899532450155123415967 8186849298675232685123951)
      ·
        refine ⟨12280273948012849027685927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8186849298675232685123951 12280273948012849027685927)
        ·
          refine ⟨18420410922019273541528891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12280273948012849027685927 18420410922019273541528891)
          ·
            refine ⟨27630616383028910312293337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18420410922019273541528891 27630616383028910312293337)
            ·
              refine ⟨20722962287271682734220003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27630616383028910312293337 20722962287271682734220003)
              ·
                refine ⟨31084443430907524101330005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20722962287271682734220003 31084443430907524101330005)
                ·
                  refine ⟨364270821455947548062461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31084443430907524101330005 364270821455947548062461)
                  ·
                    rfl

theorem cell23_6384734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6384734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384734 prefixEnd_6384734 := by exact prefixLift 6384734
  have htrace : WordTrace (prefixWord ++ tailWord_6384734) baseStart_6384734 baseEnd_6384734 := by
    simpa [prefixWord, tailWord_6384734, baseEnd_6384734] using wordTrace_append hprefix tailTrace_6384734
  have hstable : (prefixWord ++ tailWord_6384734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384734).length < 2 ^ (prefixWord ++ tailWord_6384734).sum := by decide
  have hdescent : baseEnd_6384734 < baseStart_6384734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384737 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_6384737 : Nat := 118140960795 + 6384737 * 2 ^ 59
def prefixEnd_6384737 : Nat := 4983230072969 + 3 ^ 40 * 6384737 * 2
def baseEnd_6384737 : Nat := 3278438933545491420824635

theorem tailTrace_6384737 : CollatzResearch.WordTrace tailWord_6384737 prefixEnd_6384737 3278438933545491420824635 := by
  unfold tailWord_6384737
  simp only [CollatzResearch.WordTrace]
  refine ⟨232870489470195750111440465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155246992980130500074293643 232870489470195750111440465)
  ·
    refine ⟨174652867102646812583580349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232870489470195750111440465 174652867102646812583580349)
    ·
      refine ⟨65494825163492554718842631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174652867102646812583580349 65494825163492554718842631)
      ·
        refine ⟨98242237745238832078263947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65494825163492554718842631 98242237745238832078263947)
        ·
          refine ⟨147363356617858248117395921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98242237745238832078263947 147363356617858248117395921)
          ·
            refine ⟨110522517463393686088046941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147363356617858248117395921 110522517463393686088046941)
            ·
              refine ⟨41445944048772632283017603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110522517463393686088046941 41445944048772632283017603)
              ·
                refine ⟨62168916073158948424526405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41445944048772632283017603 62168916073158948424526405)
                ·
                  refine ⟨11656671763717302829598701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62168916073158948424526405 11656671763717302829598701)
                  ·
                    refine ⟨4371251911393988561099513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11656671763717302829598701 4371251911393988561099513)
                    ·
                      refine ⟨3278438933545491420824635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371251911393988561099513 3278438933545491420824635)
                      ·
                        rfl

theorem cell23_6384737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_6384737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384737 prefixEnd_6384737 := by exact prefixLift 6384737
  have htrace : WordTrace (prefixWord ++ tailWord_6384737) baseStart_6384737 baseEnd_6384737 := by
    simpa [prefixWord, tailWord_6384737, baseEnd_6384737] using wordTrace_append hprefix tailTrace_6384737
  have hstable : (prefixWord ++ tailWord_6384737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384737).length < 2 ^ (prefixWord ++ tailWord_6384737).sum := by decide
  have hdescent : baseEnd_6384737 < baseStart_6384737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384738 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_6384738 : Nat := 118140960795 + 6384738 * 2 ^ 59
def prefixEnd_6384738 : Nat := 4983230072969 + 3 ^ 40 * 6384738 * 2
def baseEnd_6384738 : Nat := 1092813149008715305637377

theorem tailTrace_6384738 : CollatzResearch.WordTrace tailWord_6384738 prefixEnd_6384738 1092813149008715305637377 := by
  unfold tailWord_6384738
  simp only [CollatzResearch.WordTrace]
  refine ⟨58217631485798031820556717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155247017295461418188151245 58217631485798031820556717)
  ·
    refine ⟨21831611807174261932708769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58217631485798031820556717 21831611807174261932708769)
    ·
      refine ⟨16373708855380696449531577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21831611807174261932708769 16373708855380696449531577)
      ·
        refine ⟨12280281641535522337148683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16373708855380696449531577 12280281641535522337148683)
        ·
          refine ⟨18420422462303283505723025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12280281641535522337148683 18420422462303283505723025)
          ·
            refine ⟨13815316846727462629292269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18420422462303283505723025 13815316846727462629292269)
            ·
              refine ⟨5180743817522798485984601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13815316846727462629292269 5180743817522798485984601)
              ·
                refine ⟨3885557863142098864488451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180743817522798485984601 3885557863142098864488451)
                ·
                  refine ⟨5828336794713148296732677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885557863142098864488451 5828336794713148296732677)
                  ·
                    refine ⟨1092813149008715305637377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828336794713148296732677 1092813149008715305637377)
                    ·
                      rfl

theorem cell23_6384738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_6384738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384738 prefixEnd_6384738 := by exact prefixLift 6384738
  have htrace : WordTrace (prefixWord ++ tailWord_6384738) baseStart_6384738 baseEnd_6384738 := by
    simpa [prefixWord, tailWord_6384738, baseEnd_6384738] using wordTrace_append hprefix tailTrace_6384738
  have hstable : (prefixWord ++ tailWord_6384738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384738).length < 2 ^ (prefixWord ++ tailWord_6384738).sum := by decide
  have hdescent : baseEnd_6384738 < baseStart_6384738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384787 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 3]
def baseStart_6384787 : Nat := 118140960795 + 6384787 * 2 ^ 59
def prefixEnd_6384787 : Nat := 4983230072969 + 3 ^ 40 * 6384787 * 2
def baseEnd_6384787 : Nat := 3278464607578216225199405

theorem tailTrace_6384787 : CollatzResearch.WordTrace tailWord_6384787 prefixEnd_6384787 3278464607578216225199405 := by
  unfold tailWord_6384787
  simp only [CollatzResearch.WordTrace]
  refine ⟨232872313120014608650760615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155248208746676405767173743 232872313120014608650760615)
  ·
    refine ⟨349308469680021912976140923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232872313120014608650760615 349308469680021912976140923)
    ·
      refine ⟨523962704520032869464211385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349308469680021912976140923 523962704520032869464211385)
      ·
        refine ⟨392972028390024652098158539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523962704520032869464211385 392972028390024652098158539)
        ·
          refine ⟨589458042585036978147237809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392972028390024652098158539 589458042585036978147237809)
          ·
            refine ⟨442093531938777733610428357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589458042585036978147237809 442093531938777733610428357)
            ·
              refine ⟨82892537238520825051955317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442093531938777733610428357 82892537238520825051955317)
              ·
                refine ⟨7771175366111327348620811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82892537238520825051955317 7771175366111327348620811)
                ·
                  refine ⟨11656763049166991022931217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7771175366111327348620811 11656763049166991022931217)
                  ·
                    refine ⟨8742572286875243267198413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11656763049166991022931217 8742572286875243267198413)
                    ·
                      refine ⟨3278464607578216225199405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8742572286875243267198413 3278464607578216225199405)
                      ·
                        rfl

theorem cell23_6384787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_6384787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384787 prefixEnd_6384787 := by exact prefixLift 6384787
  have htrace : WordTrace (prefixWord ++ tailWord_6384787) baseStart_6384787 baseEnd_6384787 := by
    simpa [prefixWord, tailWord_6384787, baseEnd_6384787] using wordTrace_append hprefix tailTrace_6384787
  have hstable : (prefixWord ++ tailWord_6384787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384787).length < 2 ^ (prefixWord ++ tailWord_6384787).sum := by decide
  have hdescent : baseEnd_6384787 < baseStart_6384787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384794 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_6384794 : Nat := 118140960795 + 6384794 * 2 ^ 59
def prefixEnd_6384794 : Nat := 4983230072969 + 3 ^ 40 * 6384794 * 2
def baseEnd_6384794 : Nat := 1092822733980932565937291

theorem tailTrace_6384794 : CollatzResearch.WordTrace tailWord_6384794 prefixEnd_6384794 1092822733980932565937291 := by
  unfold tailWord_6384794
  simp only [CollatzResearch.WordTrace]
  refine ⟨58218142107747312211566359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155248378953992832564176957 58218142107747312211566359)
  ·
    refine ⟨87327213161620968317349539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58218142107747312211566359 87327213161620968317349539)
    ·
      refine ⟨130990819742431452476024309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87327213161620968317349539 130990819742431452476024309)
      ·
        refine ⟨12280389350852948669627279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130990819742431452476024309 12280389350852948669627279)
        ·
          refine ⟨18420584026279423004440919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12280389350852948669627279 18420584026279423004440919)
          ·
            refine ⟨27630876039419134506661379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18420584026279423004440919 27630876039419134506661379)
            ·
              refine ⟨41446314059128701759992069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27630876039419134506661379 41446314059128701759992069)
              ·
                refine ⟨7771183886086631579998513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41446314059128701759992069 7771183886086631579998513)
                ·
                  refine ⟨5828387914564973684998885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7771183886086631579998513 5828387914564973684998885)
                  ·
                    refine ⟨1092822733980932565937291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828387914564973684998885 1092822733980932565937291)
                    ·
                      rfl

theorem cell23_6384794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_6384794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384794 prefixEnd_6384794 := by exact prefixLift 6384794
  have htrace : WordTrace (prefixWord ++ tailWord_6384794) baseStart_6384794 baseEnd_6384794 := by
    simpa [prefixWord, tailWord_6384794, baseEnd_6384794] using wordTrace_append hprefix tailTrace_6384794
  have hstable : (prefixWord ++ tailWord_6384794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384794).length < 2 ^ (prefixWord ++ tailWord_6384794).sum := by decide
  have hdescent : baseEnd_6384794 < baseStart_6384794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384807 : List Nat := [1, 1, 6, 2, 1, 1, 3, 8]
def baseStart_6384807 : Nat := 118140960795 + 6384807 * 2 ^ 59
def prefixEnd_6384807 : Nat := 4983230072969 + 3 ^ 40 * 6384807 * 2
def baseEnd_6384807 : Nat := 121424995451529857294419

theorem tailTrace_6384807 : CollatzResearch.WordTrace tailWord_6384807 prefixEnd_6384807 121424995451529857294419 := by
  unfold tailWord_6384807
  simp only [CollatzResearch.WordTrace]
  refine ⟨232873042579942152066488675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155248695053294768044325783 232873042579942152066488675)
  ·
    refine ⟨349309563869913228099733013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232873042579942152066488675 349309563869913228099733013)
    ·
      refine ⟨16373885806402182567174985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 349309563869913228099733013 16373885806402182567174985)
      ·
        refine ⟨12280414354801636925381239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16373885806402182567174985 12280414354801636925381239)
        ·
          refine ⟨18420621532202455388071859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12280414354801636925381239 18420621532202455388071859)
          ·
            refine ⟨27630932298303683082107789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18420621532202455388071859 27630932298303683082107789)
            ·
              refine ⟨10361599611863881155790421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27630932298303683082107789 10361599611863881155790421)
              ·
                refine ⟨121424995451529857294419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10361599611863881155790421 121424995451529857294419)
                ·
                  rfl

theorem cell23_6384807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 8].length) (baseStart_6384807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384807 prefixEnd_6384807 := by exact prefixLift 6384807
  have htrace : WordTrace (prefixWord ++ tailWord_6384807) baseStart_6384807 baseEnd_6384807 := by
    simpa [prefixWord, tailWord_6384807, baseEnd_6384807] using wordTrace_append hprefix tailTrace_6384807
  have hstable : (prefixWord ++ tailWord_6384807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384807).length < 2 ^ (prefixWord ++ tailWord_6384807).sum := by decide
  have hdescent : baseEnd_6384807 < baseStart_6384807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384822 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6384822 : Nat := 118140960795 + 6384822 * 2 ^ 59
def prefixEnd_6384822 : Nat := 4983230072969 + 3 ^ 40 * 6384822 * 2
def baseEnd_6384822 : Nat := 3278482579401123588261745

theorem tailTrace_6384822 : CollatzResearch.WordTrace tailWord_6384822 prefixEnd_6384822 3278482579401123588261745 := by
  unfold tailWord_6384822
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554599354680488101767795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155249059783258539752189813 14554599354680488101767795)
  ·
    refine ⟨21831899032020732152651693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14554599354680488101767795 21831899032020732152651693)
    ·
      refine ⟨8186962137007774557244385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21831899032020732152651693 8186962137007774557244385)
      ·
        refine ⟨6140221602755830917933289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8186962137007774557244385 6140221602755830917933289)
        ·
          refine ⟨4605166202066873188449967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6140221602755830917933289 4605166202066873188449967)
          ·
            refine ⟨6907749303100309782674951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605166202066873188449967 6907749303100309782674951)
            ·
              refine ⟨10361623954650464674012427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907749303100309782674951 10361623954650464674012427)
              ·
                refine ⟨15542435931975697011018641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10361623954650464674012427 15542435931975697011018641)
                ·
                  refine ⟨11656826948981772758263981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15542435931975697011018641 11656826948981772758263981)
                  ·
                    refine ⟨4371310105868164784348993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11656826948981772758263981 4371310105868164784348993)
                    ·
                      refine ⟨3278482579401123588261745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371310105868164784348993 3278482579401123588261745)
                      ·
                        rfl

theorem cell23_6384822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6384822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384822 prefixEnd_6384822 := by exact prefixLift 6384822
  have htrace : WordTrace (prefixWord ++ tailWord_6384822) baseStart_6384822 baseEnd_6384822 := by
    simpa [prefixWord, tailWord_6384822, baseEnd_6384822] using wordTrace_append hprefix tailTrace_6384822
  have hstable : (prefixWord ++ tailWord_6384822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384822).length < 2 ^ (prefixWord ++ tailWord_6384822).sum := by decide
  have hdescent : baseEnd_6384822 < baseStart_6384822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384845 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6384845 : Nat := 118140960795 + 6384845 * 2 ^ 59
def prefixEnd_6384845 : Nat := 4983230072969 + 3 ^ 40 * 6384845 * 2
def baseEnd_6384845 : Nat := 1092831463152058999424713

theorem tailTrace_6384845 : CollatzResearch.WordTrace tailWord_6384845 prefixEnd_6384845 1092831463152058999424713 := by
  unfold tailWord_6384845
  simp only [CollatzResearch.WordTrace]
  refine ⟨232874428553804484556371989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155249619035869656370914659 232874428553804484556371989)
  ·
    refine ⟨10915988838459585213579937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232874428553804484556371989 10915988838459585213579937)
    ·
      refine ⟨8186991628844688910184953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10915988838459585213579937 8186991628844688910184953)
      ·
        refine ⟨6140243721633516682638715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8186991628844688910184953 6140243721633516682638715)
        ·
          refine ⟨9210365582450275023958073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6140243721633516682638715 9210365582450275023958073)
          ·
            refine ⟨6907774186837706267968555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9210365582450275023958073 6907774186837706267968555)
            ·
              refine ⟨10361661280256559401952833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907774186837706267968555 10361661280256559401952833)
              ·
                refine ⟨7771245960192419551464625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10361661280256559401952833 7771245960192419551464625)
                ·
                  refine ⟨5828434470144314663598469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7771245960192419551464625 5828434470144314663598469)
                  ·
                    refine ⟨1092831463152058999424713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828434470144314663598469 1092831463152058999424713)
                    ·
                      rfl

theorem cell23_6384845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6384845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384845 prefixEnd_6384845 := by exact prefixLift 6384845
  have htrace : WordTrace (prefixWord ++ tailWord_6384845) baseStart_6384845 baseEnd_6384845 := by
    simpa [prefixWord, tailWord_6384845, baseEnd_6384845] using wordTrace_append hprefix tailTrace_6384845
  have hstable : (prefixWord ++ tailWord_6384845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384845).length < 2 ^ (prefixWord ++ tailWord_6384845).sum := by decide
  have hdescent : baseEnd_6384845 < baseStart_6384845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384894 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6384894 : Nat := 118140960795 + 6384894 * 2 ^ 59
def prefixEnd_6384894 : Nat := 4983230072969 + 3 ^ 40 * 6384894 * 2
def baseEnd_6384894 : Nat := 3278519550008247306561413

theorem tailTrace_6384894 : CollatzResearch.WordTrace tailWord_6384894 prefixEnd_6384894 3278519550008247306561413 := by
  unfold tailWord_6384894
  simp only [CollatzResearch.WordTrace]
  refine ⟨29109526966328370740613217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155250810487084643949937157 29109526966328370740613217)
  ·
    refine ⟨21832145224746278055459913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29109526966328370740613217 21832145224746278055459913)
    ·
      refine ⟨16374108918559708541594935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21832145224746278055459913 16374108918559708541594935)
      ·
        refine ⟨24561163377839562812392403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16374108918559708541594935 24561163377839562812392403)
        ·
          refine ⟨36841745066759344218588605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24561163377839562812392403 36841745066759344218588605)
          ·
            refine ⟨13815654400034754081970727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36841745066759344218588605 13815654400034754081970727)
            ·
              refine ⟨20723481600052131122956091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13815654400034754081970727 20723481600052131122956091)
              ·
                refine ⟨31085222400078196684434137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20723481600052131122956091 31085222400078196684434137)
                ·
                  refine ⟨23313916800058647513325603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31085222400078196684434137 23313916800058647513325603)
                  ·
                    refine ⟨34970875200087971269988405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23313916800058647513325603 34970875200087971269988405)
                    ·
                      refine ⟨3278519550008247306561413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34970875200087971269988405 3278519550008247306561413)
                      ·
                        rfl

theorem cell23_6384894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6384894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384894 prefixEnd_6384894 := by exact prefixLift 6384894
  have htrace : WordTrace (prefixWord ++ tailWord_6384894) baseStart_6384894 baseEnd_6384894 := by
    simpa [prefixWord, tailWord_6384894, baseEnd_6384894] using wordTrace_append hprefix tailTrace_6384894
  have hstable : (prefixWord ++ tailWord_6384894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384894).length < 2 ^ (prefixWord ++ tailWord_6384894).sum := by decide
  have hdescent : baseEnd_6384894 < baseStart_6384894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384925 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_6384925 : Nat := 118140960795 + 6384925 * 2 ^ 59
def prefixEnd_6384925 : Nat := 4983230072969 + 3 ^ 40 * 6384925 * 2
def baseEnd_6384925 : Nat := 3278535467908536685273771

theorem tailTrace_6384925 : CollatzResearch.WordTrace tailWord_6384925 prefixEnd_6384925 3278535467908536685273771 := by
  unfold tailWord_6384925
  simp only [CollatzResearch.WordTrace]
  refine ⟨232877346393514658219284229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155251564262343105479522819 232877346393514658219284229)
  ·
    refine ⟨43664502448783998416115793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232877346393514658219284229 43664502448783998416115793)
    ·
      refine ⟨32748376836587998812086845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43664502448783998416115793 32748376836587998812086845)
      ·
        refine ⟨12280641313720499554532567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32748376836587998812086845 12280641313720499554532567)
        ·
          refine ⟨18420961970580749331798851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12280641313720499554532567 18420961970580749331798851)
          ·
            refine ⟨27631442955871123997698277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18420961970580749331798851 27631442955871123997698277)
            ·
              refine ⟨5180895554225835749568427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27631442955871123997698277 5180895554225835749568427)
              ·
                refine ⟨7771343331338753624352641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180895554225835749568427 7771343331338753624352641)
                ·
                  refine ⟨5828507498504065218264481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7771343331338753624352641 5828507498504065218264481)
                  ·
                    refine ⟨4371380623878048913698361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828507498504065218264481 4371380623878048913698361)
                    ·
                      refine ⟨3278535467908536685273771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371380623878048913698361 3278535467908536685273771)
                      ·
                        rfl

theorem cell23_6384925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_6384925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384925 prefixEnd_6384925 := by exact prefixLift 6384925
  have htrace : WordTrace (prefixWord ++ tailWord_6384925) baseStart_6384925 baseEnd_6384925 := by
    simpa [prefixWord, tailWord_6384925, baseEnd_6384925] using wordTrace_append hprefix tailTrace_6384925
  have hstable : (prefixWord ++ tailWord_6384925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384925).length < 2 ^ (prefixWord ++ tailWord_6384925).sum := by decide
  have hdescent : baseEnd_6384925 < baseStart_6384925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384974 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_6384974 : Nat := 118140960795 + 6384974 * 2 ^ 59
def prefixEnd_6384974 : Nat := 4983230072969 + 3 ^ 40 * 6384974 * 2
def baseEnd_6384974 : Nat := 1092853542820202331187015

theorem tailTrace_6384974 : CollatzResearch.WordTrace tailWord_6384974 prefixEnd_6384974 1092853542820202331187015 := by
  unfold tailWord_6384974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29109891696292142448477247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155252755713558093058545317 29109891696292142448477247)
  ·
    refine ⟨43664837544438213672715871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29109891696292142448477247 43664837544438213672715871)
    ·
      refine ⟨65497256316657320509073807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43664837544438213672715871 65497256316657320509073807)
      ·
        refine ⟨98245884474985980763610711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65497256316657320509073807 98245884474985980763610711)
        ·
          refine ⟨147368826712478971145416067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98245884474985980763610711 147368826712478971145416067)
          ·
            refine ⟨221053240068718456718124101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147368826712478971145416067 221053240068718456718124101)
            ·
              refine ⟨41447482512884710634648269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221053240068718456718124101 41447482512884710634648269)
              ·
                refine ⟨15542805942331766487993101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41447482512884710634648269 15542805942331766487993101)
                ·
                  refine ⟨5828552228374412432997413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15542805942331766487993101 5828552228374412432997413)
                  ·
                    refine ⟨1092853542820202331187015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828552228374412432997413 1092853542820202331187015)
                    ·
                      rfl

theorem cell23_6384974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_6384974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384974 prefixEnd_6384974 := by exact prefixLift 6384974
  have htrace : WordTrace (prefixWord ++ tailWord_6384974) baseStart_6384974 baseEnd_6384974 := by
    simpa [prefixWord, tailWord_6384974, baseEnd_6384974] using wordTrace_append hprefix tailTrace_6384974
  have hstable : (prefixWord ++ tailWord_6384974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384974).length < 2 ^ (prefixWord ++ tailWord_6384974).sum := by decide
  have hdescent : baseEnd_6384974 < baseStart_6384974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6384981 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_6384981 : Nat := 118140960795 + 6384981 * 2 ^ 59
def prefixEnd_6384981 : Nat := 4983230072969 + 3 ^ 40 * 6384981 * 2
def baseEnd_6384981 : Nat := 3278564222825188466173513

theorem tailTrace_6384981 : CollatzResearch.WordTrace tailWord_6384981 prefixEnd_6384981 3278564222825188466173513 := by
  unfold tailWord_6384981
  simp only [CollatzResearch.WordTrace]
  refine ⟨232879388881311779783322797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155252925920874519855548531 232879388881311779783322797)
  ·
    refine ⟨87329770830491917418746049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232879388881311779783322797 87329770830491917418746049)
    ·
      refine ⟨65497328122868938064059537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87329770830491917418746049 65497328122868938064059537)
      ·
        refine ⟨49122996092151703548044653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65497328122868938064059537 49122996092151703548044653)
        ·
          refine ⟨18421123534556888830516745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49122996092151703548044653 18421123534556888830516745)
          ·
            refine ⟨13815842650917666622887559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18421123534556888830516745 13815842650917666622887559)
            ·
              refine ⟨20723763976376499934331339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13815842650917666622887559 20723763976376499934331339)
              ·
                refine ⟨31085645964564749901497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20723763976376499934331339 31085645964564749901497009)
                ·
                  refine ⟨23314234473423562426122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31085645964564749901497009 23314234473423562426122757)
                  ·
                    refine ⟨4371418963766917954898017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23314234473423562426122757 4371418963766917954898017)
                    ·
                      refine ⟨3278564222825188466173513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371418963766917954898017 3278564222825188466173513)
                      ·
                        rfl

theorem cell23_6384981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_6384981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6384981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6384981 prefixEnd_6384981 := by exact prefixLift 6384981
  have htrace : WordTrace (prefixWord ++ tailWord_6384981) baseStart_6384981 baseEnd_6384981 := by
    simpa [prefixWord, tailWord_6384981, baseEnd_6384981] using wordTrace_append hprefix tailTrace_6384981
  have hstable : (prefixWord ++ tailWord_6384981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6384981).length < 2 ^ (prefixWord ++ tailWord_6384981).sum := by decide
  have hdescent : baseEnd_6384981 < baseStart_6384981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6384981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385031 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_6385031 : Nat := 118140960795 + 6385031 * 2 ^ 59
def prefixEnd_6385031 : Nat := 4983230072969 + 3 ^ 40 * 6385031 * 2
def baseEnd_6385031 : Nat := 3278589896857913270548283

theorem tailTrace_6385031 : CollatzResearch.WordTrace tailWord_6385031 prefixEnd_6385031 3278589896857913270548283 := by
  unfold tailWord_6385031
  simp only [CollatzResearch.WordTrace]
  refine ⟨232881212531130638322642947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155254141687420425548428631 232881212531130638322642947)
  ·
    refine ⟨349321818796695957483964421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232881212531130638322642947 349321818796695957483964421)
    ·
      refine ⟨65497841024380492028243329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349321818796695957483964421 65497841024380492028243329)
      ·
        refine ⟨49123380768285369021182497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65497841024380492028243329 49123380768285369021182497)
        ·
          refine ⟨36842535576214026765886873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49123380768285369021182497 36842535576214026765886873)
          ·
            refine ⟨27631901682160520074415155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36842535576214026765886873 27631901682160520074415155)
            ·
              refine ⟨41447852523240780111622733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27631901682160520074415155 41447852523240780111622733)
              ·
                refine ⟨15542944696215292541858525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41447852523240780111622733 15542944696215292541858525)
                ·
                  refine ⟨5828604261080734703196947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15542944696215292541858525 5828604261080734703196947)
                  ·
                    refine ⟨8742906391621102054795421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828604261080734703196947 8742906391621102054795421)
                    ·
                      refine ⟨3278589896857913270548283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8742906391621102054795421 3278589896857913270548283)
                      ·
                        rfl

theorem cell23_6385031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_6385031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385031 prefixEnd_6385031 := by exact prefixLift 6385031
  have htrace : WordTrace (prefixWord ++ tailWord_6385031) baseStart_6385031 baseEnd_6385031 := by
    simpa [prefixWord, tailWord_6385031, baseEnd_6385031] using wordTrace_append hprefix tailTrace_6385031
  have hstable : (prefixWord ++ tailWord_6385031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385031).length < 2 ^ (prefixWord ++ tailWord_6385031).sum := by decide
  have hdescent : baseEnd_6385031 < baseStart_6385031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385038 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_6385038 : Nat := 118140960795 + 6385038 * 2 ^ 59
def prefixEnd_6385038 : Nat := 4983230072969 + 3 ^ 40 * 6385038 * 2
def baseEnd_6385038 : Nat := 364288165691388304795639

theorem tailTrace_6385038 : CollatzResearch.WordTrace tailWord_6385038 prefixEnd_6385038 364288165691388304795639 := by
  unfold tailWord_6385038
  simp only [CollatzResearch.WordTrace]
  refine ⟨29110183480263159814768471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155254311894736852345431845 29110183480263159814768471)
  ·
    refine ⟨43665275220394739722152707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29110183480263159814768471 43665275220394739722152707)
    ·
      refine ⟨65497912830592109583229061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43665275220394739722152707 65497912830592109583229061)
      ·
        refine ⟨12280858655736020546855449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65497912830592109583229061 12280858655736020546855449)
        ·
          refine ⟨9210643991802015410141587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12280858655736020546855449 9210643991802015410141587)
          ·
            refine ⟨13815965987703023115212381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9210643991802015410141587 13815965987703023115212381)
            ·
              refine ⟨5180987245388633668204643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13815965987703023115212381 5180987245388633668204643)
              ·
                refine ⟨7771480868082950502306965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180987245388633668204643 7771480868082950502306965)
                ·
                  refine ⟨364288165691388304795639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7771480868082950502306965 364288165691388304795639)
                  ·
                    rfl

theorem cell23_6385038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_6385038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385038 prefixEnd_6385038 := by exact prefixLift 6385038
  have htrace : WordTrace (prefixWord ++ tailWord_6385038) baseStart_6385038 baseEnd_6385038 := by
    simpa [prefixWord, tailWord_6385038, baseEnd_6385038] using wordTrace_append hprefix tailTrace_6385038
  have hstable : (prefixWord ++ tailWord_6385038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385038).length < 2 ^ (prefixWord ++ tailWord_6385038).sum := by decide
  have hdescent : baseEnd_6385038 < baseStart_6385038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385071 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 5, 2, 2]
def baseStart_6385071 : Nat := 118140960795 + 6385071 * 2 ^ 59
def prefixEnd_6385071 : Nat := 4983230072969 + 3 ^ 40 * 6385071 * 2
def baseEnd_6385071 : Nat := 3278610436084093114048099

theorem tailTrace_6385071 : CollatzResearch.WordTrace tailWord_6385071 prefixEnd_6385071 3278610436084093114048099 := by
  unfold tailWord_6385071
  simp only [CollatzResearch.WordTrace]
  refine ⟨232882671450985725154099067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155255114300657150102732711 232882671450985725154099067)
  ·
    refine ⟨349324007176478587731148601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232882671450985725154099067 349324007176478587731148601)
    ·
      refine ⟨261993005382358940798361451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349324007176478587731148601 261993005382358940798361451)
      ·
        refine ⟨392989508073538411197542177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261993005382358940798361451 392989508073538411197542177)
        ·
          refine ⟨294742131055153808398156633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392989508073538411197542177 294742131055153808398156633)
          ·
            refine ⟨221056598291365356298617475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294742131055153808398156633 221056598291365356298617475)
            ·
              refine ⟨331584897437048034447926213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221056598291365356298617475 331584897437048034447926213)
              ·
                refine ⟨62172168269446506458986165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331584897437048034447926213 62172168269446506458986165)
                ·
                  refine ⟨5828640775260609980529953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62172168269446506458986165 5828640775260609980529953)
                  ·
                    refine ⟨4371480581445457485397465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828640775260609980529953 4371480581445457485397465)
                    ·
                      refine ⟨3278610436084093114048099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371480581445457485397465 3278610436084093114048099)
                      ·
                        rfl

theorem cell23_6385071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 2, 2].length) (baseStart_6385071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385071 prefixEnd_6385071 := by exact prefixLift 6385071
  have htrace : WordTrace (prefixWord ++ tailWord_6385071) baseStart_6385071 baseEnd_6385071 := by
    simpa [prefixWord, tailWord_6385071, baseEnd_6385071] using wordTrace_append hprefix tailTrace_6385071
  have hstable : (prefixWord ++ tailWord_6385071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385071).length < 2 ^ (prefixWord ++ tailWord_6385071).sum := by decide
  have hdescent : baseEnd_6385071 < baseStart_6385071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385088 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 3, 2, 2]
def baseStart_6385088 : Nat := 118140960795 + 6385088 * 2 ^ 59
def prefixEnd_6385088 : Nat := 4983230072969 + 3 ^ 40 * 6385088 * 2
def baseEnd_6385088 : Nat := 3278619165255219547535521

theorem tailTrace_6385088 : CollatzResearch.WordTrace tailWord_6385088 prefixEnd_6385088 3278619165255219547535521 := by
  unfold tailWord_6385088
  simp only [CollatzResearch.WordTrace]
  refine ⟨116441645745962068528733959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155255527661282758038311945 116441645745962068528733959)
  ·
    refine ⟨174662468618943102793100939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116441645745962068528733959 174662468618943102793100939)
    ·
      refine ⟨261993702928414654189651409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174662468618943102793100939 261993702928414654189651409)
      ·
        refine ⟨196495277196310990642238557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261993702928414654189651409 196495277196310990642238557)
        ·
          refine ⟨73685728948616621490839459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196495277196310990642238557 73685728948616621490839459)
          ·
            refine ⟨110528593422924932236259189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73685728948616621490839459 110528593422924932236259189)
            ·
              refine ⟨10362055633399212397149299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110528593422924932236259189 10362055633399212397149299)
              ·
                refine ⟨15543083450098818595723949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10362055633399212397149299 15543083450098818595723949)
                ·
                  refine ⟨5828656293787056973396481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15543083450098818595723949 5828656293787056973396481)
                  ·
                    refine ⟨4371492220340292730047361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828656293787056973396481 4371492220340292730047361)
                    ·
                      refine ⟨3278619165255219547535521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371492220340292730047361 3278619165255219547535521)
                      ·
                        rfl

theorem cell23_6385088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_6385088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385088 prefixEnd_6385088 := by exact prefixLift 6385088
  have htrace : WordTrace (prefixWord ++ tailWord_6385088) baseStart_6385088 baseEnd_6385088 := by
    simpa [prefixWord, tailWord_6385088, baseEnd_6385088] using wordTrace_append hprefix tailTrace_6385088
  have hstable : (prefixWord ++ tailWord_6385088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385088).length < 2 ^ (prefixWord ++ tailWord_6385088).sum := by decide
  have hdescent : baseEnd_6385088 < baseStart_6385088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385097 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_6385097 : Nat := 118140960795 + 6385097 * 2 ^ 59
def prefixEnd_6385097 : Nat := 4983230072969 + 3 ^ 40 * 6385097 * 2
def baseEnd_6385097 : Nat := 3278623786581110012322979

theorem tailTrace_6385097 : CollatzResearch.WordTrace tailWord_6385097 prefixEnd_6385097 3278623786581110012322979 := by
  unfold tailWord_6385097
  simp only [CollatzResearch.WordTrace]
  refine ⟨232883619748891531594545545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155255746499261021063030363 232883619748891531594545545)
  ·
    refine ⟨174662714811668648695909159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232883619748891531594545545 174662714811668648695909159)
    ·
      refine ⟨261994072217502973043863739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174662714811668648695909159 261994072217502973043863739)
      ·
        refine ⟨392991108326254459565795609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261994072217502973043863739 392991108326254459565795609)
        ·
          refine ⟨294743331244690844674346707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392991108326254459565795609 294743331244690844674346707)
          ·
            refine ⟨442114996867036267011520061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294743331244690844674346707 442114996867036267011520061)
            ·
              refine ⟨165793123825138600129320023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442114996867036267011520061 165793123825138600129320023)
              ·
                refine ⟨248689685737707900193980035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165793123825138600129320023 248689685737707900193980035)
                ·
                  refine ⟨373034528606561850290970053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248689685737707900193980035 373034528606561850290970053)
                  ·
                    refine ⟨69943974113730346929556885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373034528606561850290970053 69943974113730346929556885)
                    ·
                      refine ⟨3278623786581110012322979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69943974113730346929556885 3278623786581110012322979)
                      ·
                        rfl

theorem cell23_6385097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_6385097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385097 prefixEnd_6385097 := by exact prefixLift 6385097
  have htrace : WordTrace (prefixWord ++ tailWord_6385097) baseStart_6385097 baseEnd_6385097 := by
    simpa [prefixWord, tailWord_6385097, baseEnd_6385097] using wordTrace_append hprefix tailTrace_6385097
  have hstable : (prefixWord ++ tailWord_6385097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385097).length < 2 ^ (prefixWord ++ tailWord_6385097).sum := by decide
  have hdescent : baseEnd_6385097 < baseStart_6385097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385098 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_6385098 : Nat := 118140960795 + 6385098 * 2 ^ 59
def prefixEnd_6385098 : Nat := 4983230072969 + 3 ^ 40 * 6385098 * 2
def baseEnd_6385098 : Nat := 1092874766687254836136825

theorem tailTrace_6385098 : CollatzResearch.WordTrace tailWord_6385098 prefixEnd_6385098 1092874766687254836136825 := by
  unfold tailWord_6385098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58220914055471977191332987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155255770814591939176887965 58220914055471977191332987)
  ·
    refine ⟨87331371083207965786999481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58220914055471977191332987 87331371083207965786999481)
    ·
      refine ⟨65498528312405974340249611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87331371083207965786999481 65498528312405974340249611)
      ·
        refine ⟨98247792468608961510374417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65498528312405974340249611 98247792468608961510374417)
        ·
          refine ⟨73685844351456721132780813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98247792468608961510374417 73685844351456721132780813)
          ·
            refine ⟨27632191631796270424792805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73685844351456721132780813 27632191631796270424792805)
            ·
              refine ⟨5181035930961800704648651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27632191631796270424792805 5181035930961800704648651)
              ·
                refine ⟨7771553896442701056972977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181035930961800704648651 7771553896442701056972977)
                ·
                  refine ⟨5828665422332025792729733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7771553896442701056972977 5828665422332025792729733)
                  ·
                    refine ⟨1092874766687254836136825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828665422332025792729733 1092874766687254836136825)
                    ·
                      rfl

theorem cell23_6385098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_6385098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385098 prefixEnd_6385098 := by exact prefixLift 6385098
  have htrace : WordTrace (prefixWord ++ tailWord_6385098) baseStart_6385098 baseEnd_6385098 := by
    simpa [prefixWord, tailWord_6385098, baseEnd_6385098] using wordTrace_append hprefix tailTrace_6385098
  have hstable : (prefixWord ++ tailWord_6385098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385098).length < 2 ^ (prefixWord ++ tailWord_6385098).sum := by decide
  have hdescent : baseEnd_6385098 < baseStart_6385098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385108 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_6385108 : Nat := 118140960795 + 6385108 * 2 ^ 59
def prefixEnd_6385108 : Nat := 4983230072969 + 3 ^ 40 * 6385108 * 2
def baseEnd_6385108 : Nat := 3278629434868309469285429

theorem tailTrace_6385108 : CollatzResearch.WordTrace tailWord_6385108 prefixEnd_6385108 3278629434868309469285429 := by
  unfold tailWord_6385108
  simp only [CollatzResearch.WordTrace]
  refine ⟨116442010475925840236597989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155256013967901120315463985 116442010475925840236597989)
  ·
    refine ⟨21832876964236095044362123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116442010475925840236597989 21832876964236095044362123)
    ·
      refine ⟨32749315446354142566543185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21832876964236095044362123 32749315446354142566543185)
      ·
        refine ⟨24561986584765606924907389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32749315446354142566543185 24561986584765606924907389)
        ·
          refine ⟨9210744969287102596840271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24561986584765606924907389 9210744969287102596840271)
          ·
            refine ⟨13816117453930653895260407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9210744969287102596840271 13816117453930653895260407)
            ·
              refine ⟨20724176180895980842890611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13816117453930653895260407 20724176180895980842890611)
              ·
                refine ⟨31086264271343971264335917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20724176180895980842890611 31086264271343971264335917)
                ·
                  refine ⟨11657349101753989224125969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31086264271343971264335917 11657349101753989224125969)
                  ·
                    refine ⟨8743011826315491918094477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11657349101753989224125969 8743011826315491918094477)
                    ·
                      refine ⟨3278629434868309469285429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743011826315491918094477 3278629434868309469285429)
                      ·
                        rfl

theorem cell23_6385108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_6385108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385108 prefixEnd_6385108 := by exact prefixLift 6385108
  have htrace : WordTrace (prefixWord ++ tailWord_6385108) baseStart_6385108 baseEnd_6385108 := by
    simpa [prefixWord, tailWord_6385108, baseEnd_6385108] using wordTrace_append hprefix tailTrace_6385108
  have hstable : (prefixWord ++ tailWord_6385108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385108).length < 2 ^ (prefixWord ++ tailWord_6385108).sum := by decide
  have hdescent : baseEnd_6385108 < baseStart_6385108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385121 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_6385121 : Nat := 118140960795 + 6385121 * 2 ^ 59
def prefixEnd_6385121 : Nat := 4983230072969 + 3 ^ 40 * 6385121 * 2
def baseEnd_6385121 : Nat := 3278636110116817918422869

theorem tailTrace_6385121 : CollatzResearch.WordTrace tailWord_6385121 prefixEnd_6385121 3278636110116817918422869 := by
  unfold tailWord_6385121
  simp only [CollatzResearch.WordTrace]
  refine ⟨232884495100804583693419217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155256330067203055795612811 232884495100804583693419217)
  ·
    refine ⟨174663371325603437770064413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232884495100804583693419217 174663371325603437770064413)
    ·
      refine ⟨65498764247101289163774155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174663371325603437770064413 65498764247101289163774155)
      ·
        refine ⟨98248146370651933745661233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65498764247101289163774155 98248146370651933745661233)
        ·
          refine ⟨73686109777988950309245925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98248146370651933745661233 73686109777988950309245925)
          ·
            refine ⟨13816145583372928182983611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73686109777988950309245925 13816145583372928182983611)
            ·
              refine ⟨20724218375059392274475417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13816145583372928182983611 20724218375059392274475417)
              ·
                refine ⟨15543163781294544205856563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20724218375059392274475417 15543163781294544205856563)
                ·
                  refine ⟨23314745671941816308784845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15543163781294544205856563 23314745671941816308784845)
                  ·
                    refine ⟨8743029626978181115794317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23314745671941816308784845 8743029626978181115794317)
                    ·
                      refine ⟨3278636110116817918422869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743029626978181115794317 3278636110116817918422869)
                      ·
                        rfl

theorem cell23_6385121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_6385121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385121 prefixEnd_6385121 := by exact prefixLift 6385121
  have htrace : WordTrace (prefixWord ++ tailWord_6385121) baseStart_6385121 baseEnd_6385121 := by
    simpa [prefixWord, tailWord_6385121, baseEnd_6385121] using wordTrace_append hprefix tailTrace_6385121
  have hstable : (prefixWord ++ tailWord_6385121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385121).length < 2 ^ (prefixWord ++ tailWord_6385121).sum := by decide
  have hdescent : baseEnd_6385121 < baseStart_6385121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385125 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6385125 : Nat := 118140960795 + 6385125 * 2 ^ 59
def prefixEnd_6385125 : Nat := 4983230072969 + 3 ^ 40 * 6385125 * 2
def baseEnd_6385125 : Nat := 3278638164039435902772851

theorem tailTrace_6385125 : CollatzResearch.WordTrace tailWord_6385125 prefixEnd_6385125 3278638164039435902772851 := by
  unfold tailWord_6385125
  simp only [CollatzResearch.WordTrace]
  refine ⟨232884640992790092376564829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155256427328526728251043219 232884640992790092376564829)
  ·
    refine ⟨87331740372296284641211811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232884640992790092376564829 87331740372296284641211811)
    ·
      refine ⟨130997610558444426961817717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87331740372296284641211811 130997610558444426961817717)
      ·
        refine ⟨12281025989854165027670411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130997610558444426961817717 12281025989854165027670411)
        ·
          refine ⟨18421538984781247541505617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12281025989854165027670411 18421538984781247541505617)
          ·
            refine ⟨13816154238585935656129213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18421538984781247541505617 13816154238585935656129213)
            ·
              refine ⟨5181057839469725871048455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13816154238585935656129213 5181057839469725871048455)
              ·
                refine ⟨7771586759204588806572683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181057839469725871048455 7771586759204588806572683)
                ·
                  refine ⟨11657380138806883209859025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7771586759204588806572683 11657380138806883209859025)
                  ·
                    refine ⟨8743035104105162407394269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11657380138806883209859025 8743035104105162407394269)
                    ·
                      refine ⟨3278638164039435902772851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743035104105162407394269 3278638164039435902772851)
                      ·
                        rfl

theorem cell23_6385125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6385125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385125 prefixEnd_6385125 := by exact prefixLift 6385125
  have htrace : WordTrace (prefixWord ++ tailWord_6385125) baseStart_6385125 baseEnd_6385125 := by
    simpa [prefixWord, tailWord_6385125, baseEnd_6385125] using wordTrace_append hprefix tailTrace_6385125
  have hstable : (prefixWord ++ tailWord_6385125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385125).length < 2 ^ (prefixWord ++ tailWord_6385125).sum := by decide
  have hdescent : baseEnd_6385125 < baseStart_6385125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385141 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6385141 : Nat := 118140960795 + 6385141 * 2 ^ 59
def prefixEnd_6385141 : Nat := 4983230072969 + 3 ^ 40 * 6385141 * 2
def baseEnd_6385141 : Nat := 1092882126576635946724259

theorem tailTrace_6385141 : CollatzResearch.WordTrace tailWord_6385141 prefixEnd_6385141 1092882126576635946724259 := by
  unfold tailWord_6385141
  simp only [CollatzResearch.WordTrace]
  refine ⟨232885224560732127109147277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155256816373821418072764851 232885224560732127109147277)
  ·
    refine ⟨87331959210274547665930229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232885224560732127109147277 87331959210274547665930229)
    ·
      refine ⟨8187371175963238843680959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87331959210274547665930229 8187371175963238843680959)
      ·
        refine ⟨12281056763944858265521439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8187371175963238843680959 12281056763944858265521439)
        ·
          refine ⟨18421585145917287398282159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12281056763944858265521439 18421585145917287398282159)
          ·
            refine ⟨27632377718875931097423239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18421585145917287398282159 27632377718875931097423239)
            ·
              refine ⟨41448566578313896646134859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27632377718875931097423239 41448566578313896646134859)
              ·
                refine ⟨62172849867470844969202289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41448566578313896646134859 62172849867470844969202289)
                ·
                  refine ⟨46629637400603133726901717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62172849867470844969202289 46629637400603133726901717)
                  ·
                    refine ⟨1092882126576635946724259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46629637400603133726901717 1092882126576635946724259)
                    ·
                      rfl

theorem cell23_6385141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6385141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385141 prefixEnd_6385141 := by exact prefixLift 6385141
  have htrace : WordTrace (prefixWord ++ tailWord_6385141) baseStart_6385141 baseEnd_6385141 := by
    simpa [prefixWord, tailWord_6385141, baseEnd_6385141] using wordTrace_append hprefix tailTrace_6385141
  have hstable : (prefixWord ++ tailWord_6385141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385141).length < 2 ^ (prefixWord ++ tailWord_6385141).sum := by decide
  have hdescent : baseEnd_6385141 < baseStart_6385141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385144 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_6385144 : Nat := 118140960795 + 6385144 * 2 ^ 59
def prefixEnd_6385144 : Nat := 4983230072969 + 3 ^ 40 * 6385144 * 2
def baseEnd_6385144 : Nat := 3278647920171871328435263

theorem tailTrace_6385144 : CollatzResearch.WordTrace tailWord_6385144 prefixEnd_6385144 3278647920171871328435263 := by
  unfold tailWord_6385144
  simp only [CollatzResearch.WordTrace]
  refine ⟨116442666989860629310753243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155256889319814172414337657 116442666989860629310753243)
  ·
    refine ⟨174664000484790943966129865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116442666989860629310753243 174664000484790943966129865)
    ·
      refine ⟨130998000363593207974597399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174664000484790943966129865 130998000363593207974597399)
      ·
        refine ⟨196497000545389811961896099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130998000363593207974597399 196497000545389811961896099)
        ·
          refine ⟨294745500818084717942844149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196497000545389811961896099 294745500818084717942844149)
          ·
            refine ⟨27632390701695442307141639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294745500818084717942844149 27632390701695442307141639)
            ·
              refine ⟨41448586052543163460712459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27632390701695442307141639 41448586052543163460712459)
              ·
                refine ⟨62172879078814745191068689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41448586052543163460712459 62172879078814745191068689)
                ·
                  refine ⟨46629659309111058893301517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62172879078814745191068689 46629659309111058893301517)
                  ·
                    refine ⟨17486122240916647084988069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46629659309111058893301517 17486122240916647084988069)
                    ·
                      refine ⟨3278647920171871328435263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17486122240916647084988069 3278647920171871328435263)
                      ·
                        rfl

theorem cell23_6385144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_6385144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385144 prefixEnd_6385144 := by exact prefixLift 6385144
  have htrace : WordTrace (prefixWord ++ tailWord_6385144) baseStart_6385144 baseEnd_6385144 := by
    simpa [prefixWord, tailWord_6385144, baseEnd_6385144] using wordTrace_append hprefix tailTrace_6385144
  have hstable : (prefixWord ++ tailWord_6385144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385144).length < 2 ^ (prefixWord ++ tailWord_6385144).sum := by decide
  have hdescent : baseEnd_6385144 < baseStart_6385144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385178 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2]
def baseStart_6385178 : Nat := 118140960795 + 6385178 * 2 ^ 59
def prefixEnd_6385178 : Nat := 4983230072969 + 3 ^ 40 * 6385178 * 2
def baseEnd_6385178 : Nat := 3278665378514124195410107

theorem tailTrace_6385178 : CollatzResearch.WordTrace tailWord_6385178 prefixEnd_6385178 3278665378514124195410107 := by
  unfold tailWord_6385178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58221643515399520607061047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155257716041065388285496125 58221643515399520607061047)
  ·
    refine ⟨87332465273099280910591571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58221643515399520607061047 87332465273099280910591571)
    ·
      refine ⟨130998697909648921365887357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87332465273099280910591571 130998697909648921365887357)
      ·
        refine ⟨49124511716118345512207759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130998697909648921365887357 49124511716118345512207759)
        ·
          refine ⟨73686767574177518268311639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49124511716118345512207759 73686767574177518268311639)
          ·
            refine ⟨110530151361266277402467459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73686767574177518268311639 110530151361266277402467459)
            ·
              refine ⟨165795227041899416103701189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110530151361266277402467459 165795227041899416103701189)
              ·
                refine ⟨31086605070356140519443973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165795227041899416103701189 31086605070356140519443973)
                ·
                  refine ⟨5828738450691776347395745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31086605070356140519443973 5828738450691776347395745)
                  ·
                    refine ⟨4371553838018832260546809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828738450691776347395745 4371553838018832260546809)
                    ·
                      refine ⟨3278665378514124195410107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371553838018832260546809 3278665378514124195410107)
                      ·
                        rfl

theorem cell23_6385178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_6385178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385178 prefixEnd_6385178 := by exact prefixLift 6385178
  have htrace : WordTrace (prefixWord ++ tailWord_6385178) baseStart_6385178 baseEnd_6385178 := by
    simpa [prefixWord, tailWord_6385178, baseEnd_6385178] using wordTrace_append hprefix tailTrace_6385178
  have hstable : (prefixWord ++ tailWord_6385178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385178).length < 2 ^ (prefixWord ++ tailWord_6385178).sum := by decide
  have hdescent : baseEnd_6385178 < baseStart_6385178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385212 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_6385212 : Nat := 118140960795 + 6385212 * 2 ^ 59
def prefixEnd_6385212 : Nat := 4983230072969 + 3 ^ 40 * 6385212 * 2
def baseEnd_6385212 : Nat := 3278682836856377062384951

theorem tailTrace_6385212 : CollatzResearch.WordTrace tailWord_6385212 prefixEnd_6385212 3278682836856377062384951 := by
  unfold tailWord_6385212
  simp only [CollatzResearch.WordTrace]
  refine ⟨116443907071737453117490945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155258542762316604156654593 116443907071737453117490945)
  ·
    refine ⟨87332930303803089838118209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116443907071737453117490945 87332930303803089838118209)
    ·
      refine ⟨65499697727852317378588657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87332930303803089838118209 65499697727852317378588657)
      ·
        refine ⟨49124773295889238033941493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65499697727852317378588657 49124773295889238033941493)
        ·
          refine ⟨4605447496489616065682015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49124773295889238033941493 4605447496489616065682015)
          ·
            refine ⟨6908171244734424098523023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605447496489616065682015 6908171244734424098523023)
            ·
              refine ⟨10362256867101636147784535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908171244734424098523023 10362256867101636147784535)
              ·
                refine ⟨15543385300652454221676803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10362256867101636147784535 15543385300652454221676803)
                ·
                  refine ⟨23315077950978681332515205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15543385300652454221676803 23315077950978681332515205)
                  ·
                    refine ⟨4371577115808502749846601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23315077950978681332515205 4371577115808502749846601)
                    ·
                      refine ⟨3278682836856377062384951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371577115808502749846601 3278682836856377062384951)
                      ·
                        rfl

theorem cell23_6385212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_6385212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385212 prefixEnd_6385212 := by exact prefixLift 6385212
  have htrace : WordTrace (prefixWord ++ tailWord_6385212) baseStart_6385212 baseEnd_6385212 := by
    simpa [prefixWord, tailWord_6385212, baseEnd_6385212] using wordTrace_append hprefix tailTrace_6385212
  have hstable : (prefixWord ++ tailWord_6385212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385212).length < 2 ^ (prefixWord ++ tailWord_6385212).sum := by decide
  have hdescent : baseEnd_6385212 < baseStart_6385212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385224 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_6385224 : Nat := 118140960795 + 6385224 * 2 ^ 59
def prefixEnd_6385224 : Nat := 4983230072969 + 3 ^ 40 * 6385224 * 2
def baseEnd_6385224 : Nat := 3278688998624231015434895

theorem tailTrace_6385224 : CollatzResearch.WordTrace tailWord_6385224 prefixEnd_6385224 3278688998624231015434895 := by
  unfold tailWord_6385224
  simp only [CollatzResearch.WordTrace]
  refine ⟨116444125909715716142209363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155258834546287621522945817 116444125909715716142209363)
  ·
    refine ⟨174666188864573574213314045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116444125909715716142209363 174666188864573574213314045)
    ·
      refine ⟨65499820824215090329992767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174666188864573574213314045 65499820824215090329992767)
      ·
        refine ⟨98249731236322635494989151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65499820824215090329992767 98249731236322635494989151)
        ·
          refine ⟨147374596854483953242483727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98249731236322635494989151 147374596854483953242483727)
          ·
            refine ⟨221061895281725929863725591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147374596854483953242483727 221061895281725929863725591)
            ·
              refine ⟨331592842922588894795588387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221061895281725929863725591 331592842922588894795588387)
              ·
                refine ⟨497389264383883342193382581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331592842922588894795588387 497389264383883342193382581)
                ·
                  refine ⟨46630243535989063330629617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497389264383883342193382581 46630243535989063330629617)
                  ·
                    refine ⟨34972682651991797497972213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46630243535989063330629617 34972682651991797497972213)
                    ·
                      refine ⟨3278688998624231015434895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34972682651991797497972213 3278688998624231015434895)
                      ·
                        rfl

theorem cell23_6385224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_6385224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385224 prefixEnd_6385224 := by exact prefixLift 6385224
  have htrace : WordTrace (prefixWord ++ tailWord_6385224) baseStart_6385224 baseEnd_6385224 := by
    simpa [prefixWord, tailWord_6385224, baseEnd_6385224] using wordTrace_append hprefix tailTrace_6385224
  have hstable : (prefixWord ++ tailWord_6385224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385224).length < 2 ^ (prefixWord ++ tailWord_6385224).sum := by decide
  have hdescent : baseEnd_6385224 < baseStart_6385224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385251 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 4]
def baseStart_6385251 : Nat := 118140960795 + 6385251 * 2 ^ 59
def prefixEnd_6385251 : Nat := 4983230072969 + 3 ^ 40 * 6385251 * 2
def baseEnd_6385251 : Nat := 3278702862601902409797271

theorem tailTrace_6385251 : CollatzResearch.WordTrace tailWord_6385251 prefixEnd_6385251 3278702862601902409797271 := by
  unfold tailWord_6385251
  simp only [CollatzResearch.WordTrace]
  refine ⟨232889236590333615895651607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155259491060222410597101071 232889236590333615895651607)
  ·
    refine ⟨349333854885500423843477411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232889236590333615895651607 349333854885500423843477411)
    ·
      refine ⟨524000782328250635765216117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349333854885500423843477411 524000782328250635765216117)
      ·
        refine ⟨49125073343273497102989011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 524000782328250635765216117 49125073343273497102989011)
        ·
          refine ⟨73687610014910245654483517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49125073343273497102989011 73687610014910245654483517)
          ·
            refine ⟨27632853755591342120431319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73687610014910245654483517 27632853755591342120431319)
            ·
              refine ⟨41449280633387013180646979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27632853755591342120431319 41449280633387013180646979)
              ·
                refine ⟨62173920950080519770970469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41449280633387013180646979 62173920950080519770970469)
                ·
                  refine ⟨11657610178140097457056963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62173920950080519770970469 11657610178140097457056963)
                  ·
                    refine ⟨17486415267210146185585445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11657610178140097457056963 17486415267210146185585445)
                    ·
                      refine ⟨3278702862601902409797271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17486415267210146185585445 3278702862601902409797271)
                      ·
                        rfl

theorem cell23_6385251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_6385251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385251 prefixEnd_6385251 := by exact prefixLift 6385251
  have htrace : WordTrace (prefixWord ++ tailWord_6385251) baseStart_6385251 baseEnd_6385251 := by
    simpa [prefixWord, tailWord_6385251, baseEnd_6385251] using wordTrace_append hprefix tailTrace_6385251
  have hstable : (prefixWord ++ tailWord_6385251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385251).length < 2 ^ (prefixWord ++ tailWord_6385251).sum := by decide
  have hdescent : baseEnd_6385251 < baseStart_6385251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385271 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_6385271 : Nat := 118140960795 + 6385271 * 2 ^ 59
def prefixEnd_6385271 : Nat := 4983230072969 + 3 ^ 40 * 6385271 * 2
def baseEnd_6385271 : Nat := 3278713132214992331547179

theorem tailTrace_6385271 : CollatzResearch.WordTrace tailWord_6385271 prefixEnd_6385271 3278713132214992331547179 := by
  unfold tailWord_6385271
  simp only [CollatzResearch.WordTrace]
  refine ⟨232889966050261159311379667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155259977366840772874253111 232889966050261159311379667)
  ·
    refine ⟨349334949075391738967069501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232889966050261159311379667 349334949075391738967069501)
    ·
      refine ⟨131000605903271902112651063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349334949075391738967069501 131000605903271902112651063)
      ·
        refine ⟨196500908854907853168976595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131000605903271902112651063 196500908854907853168976595)
        ·
          refine ⟨294751363282361779753464893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196500908854907853168976595 294751363282361779753464893)
          ·
            refine ⟨110531761230885667407549335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294751363282361779753464893 110531761230885667407549335)
            ·
              refine ⟨165797641846328501111324003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110531761230885667407549335 165797641846328501111324003)
              ·
                refine ⟨248696462769492751666986005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165797641846328501111324003 248696462769492751666986005)
                ·
                  refine ⟨11657646692319972734389969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248696462769492751666986005 11657646692319972734389969)
                  ·
                    refine ⟨8743235019239979550792477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11657646692319972734389969 8743235019239979550792477)
                    ·
                      refine ⟨3278713132214992331547179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743235019239979550792477 3278713132214992331547179)
                      ·
                        rfl

theorem cell23_6385271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_6385271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385271 prefixEnd_6385271 := by exact prefixLift 6385271
  have htrace : WordTrace (prefixWord ++ tailWord_6385271) baseStart_6385271 baseEnd_6385271 := by
    simpa [prefixWord, tailWord_6385271, baseEnd_6385271] using wordTrace_append hprefix tailTrace_6385271
  have hstable : (prefixWord ++ tailWord_6385271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385271).length < 2 ^ (prefixWord ++ tailWord_6385271).sum := by decide
  have hdescent : baseEnd_6385271 < baseStart_6385271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385274 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_6385274 : Nat := 118140960795 + 6385274 * 2 ^ 59
def prefixEnd_6385274 : Nat := 4983230072969 + 3 ^ 40 * 6385274 * 2
def baseEnd_6385274 : Nat := 364301630295217313312185

theorem tailTrace_6385274 : CollatzResearch.WordTrace tailWord_6385274 prefixEnd_6385274 364301630295217313312185 := by
  unfold tailWord_6385274
  simp only [CollatzResearch.WordTrace]
  refine ⟨58222518867312572705934719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155260050312833527215825917 58222518867312572705934719)
  ·
    refine ⟨87333778300968859058902079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58222518867312572705934719 87333778300968859058902079)
    ·
      refine ⟨131000667451453288588353119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87333778300968859058902079 131000667451453288588353119)
      ·
        refine ⟨196501001177179932882529679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131000667451453288588353119 196501001177179932882529679)
        ·
          refine ⟨294751501765769899323794519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196501001177179932882529679 294751501765769899323794519)
          ·
            refine ⟨442127252648654848985691779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294751501765769899323794519 442127252648654848985691779)
            ·
              refine ⟨663190878972982273478537669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442127252648654848985691779 663190878972982273478537669)
              ·
                refine ⟨124348289807434176277225813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 663190878972982273478537669 124348289807434176277225813)
                ·
                  refine ⟨364301630295217313312185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124348289807434176277225813 364301630295217313312185)
                  ·
                    rfl

theorem cell23_6385274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_6385274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385274 prefixEnd_6385274 := by exact prefixLift 6385274
  have htrace : WordTrace (prefixWord ++ tailWord_6385274) baseStart_6385274 baseEnd_6385274 := by
    simpa [prefixWord, tailWord_6385274, baseEnd_6385274] using wordTrace_append hprefix tailTrace_6385274
  have hstable : (prefixWord ++ tailWord_6385274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385274).length < 2 ^ (prefixWord ++ tailWord_6385274).sum := by decide
  have hdescent : baseEnd_6385274 < baseStart_6385274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385312 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 1, 4]
def baseStart_6385312 : Nat := 118140960795 + 6385312 * 2 ^ 59
def prefixEnd_6385312 : Nat := 4983230072969 + 3 ^ 40 * 6385312 * 2
def baseEnd_6385312 : Nat := 1092911394973942223711497

theorem tailTrace_6385312 : CollatzResearch.WordTrace tailWord_6385312 prefixEnd_6385312 1092911394973942223711497 := by
  unfold tailWord_6385312
  simp only [CollatzResearch.WordTrace]
  refine ⟨116445730721556311656811095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155260974295408415542414793 116445730721556311656811095)
  ·
    refine ⟨174668596082334467485216643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116445730721556311656811095 174668596082334467485216643)
    ·
      refine ⟨262002894123501701227824965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174668596082334467485216643 262002894123501701227824965)
      ·
        refine ⟨49125542648156568980217181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262002894123501701227824965 49125542648156568980217181)
        ·
          refine ⟨18422078493058713367581443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49125542648156568980217181 18422078493058713367581443)
          ·
            refine ⟨27633117739588070051372165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18422078493058713367581443 27633117739588070051372165)
            ·
              refine ⟨5181209576172763134632281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27633117739588070051372165 5181209576172763134632281)
              ·
                refine ⟨3885907182129572350974211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181209576172763134632281 3885907182129572350974211)
                ·
                  refine ⟨5828860773194358526461317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885907182129572350974211 5828860773194358526461317)
                  ·
                    refine ⟨1092911394973942223711497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828860773194358526461317 1092911394973942223711497)
                    ·
                      rfl

theorem cell23_6385312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 4].length) (baseStart_6385312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385312 prefixEnd_6385312 := by exact prefixLift 6385312
  have htrace : WordTrace (prefixWord ++ tailWord_6385312) baseStart_6385312 baseEnd_6385312 := by
    simpa [prefixWord, tailWord_6385312, baseEnd_6385312] using wordTrace_append hprefix tailTrace_6385312
  have hstable : (prefixWord ++ tailWord_6385312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385312).length < 2 ^ (prefixWord ++ tailWord_6385312).sum := by decide
  have hdescent : baseEnd_6385312 < baseStart_6385312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385328 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 4, 3, 2]
def baseStart_6385328 : Nat := 118140960795 + 6385328 * 2 ^ 59
def prefixEnd_6385328 : Nat := 4983230072969 + 3 ^ 40 * 6385328 * 2
def baseEnd_6385328 : Nat := 3278742400612298608534417

theorem tailTrace_6385328 : CollatzResearch.WordTrace tailWord_6385328 prefixEnd_6385328 3278742400612298608534417 := by
  unfold tailWord_6385328
  simp only [CollatzResearch.WordTrace]
  refine ⟨116446022505527329023102319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155261363340703105364136425 116446022505527329023102319)
  ·
    refine ⟨174669033758290993534653479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116446022505527329023102319 174669033758290993534653479)
    ·
      refine ⟨262003550637436490301980219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174669033758290993534653479 262003550637436490301980219)
      ·
        refine ⟨393005325956154735452970329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262003550637436490301980219 393005325956154735452970329)
        ·
          refine ⟨294753994467116051589727747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393005325956154735452970329 294753994467116051589727747)
          ·
            refine ⟨442130991700674077384591621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294753994467116051589727747 442130991700674077384591621)
            ·
              refine ⟨82899560943876389509610929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442130991700674077384591621 82899560943876389509610929)
              ·
                refine ⟨62174670707907292132208197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82899560943876389509610929 62174670707907292132208197)
                ·
                  refine ⟨11657750757732617274789037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62174670707907292132208197 11657750757732617274789037)
                  ·
                    refine ⟨4371656534149731478045889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11657750757732617274789037 4371656534149731478045889)
                    ·
                      refine ⟨3278742400612298608534417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371656534149731478045889 3278742400612298608534417)
                      ·
                        rfl

theorem cell23_6385328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 3, 2].length) (baseStart_6385328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385328 prefixEnd_6385328 := by exact prefixLift 6385328
  have htrace : WordTrace (prefixWord ++ tailWord_6385328) baseStart_6385328 baseEnd_6385328 := by
    simpa [prefixWord, tailWord_6385328, baseEnd_6385328] using wordTrace_append hprefix tailTrace_6385328
  have hstable : (prefixWord ++ tailWord_6385328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385328).length < 2 ^ (prefixWord ++ tailWord_6385328).sum := by decide
  have hdescent : baseEnd_6385328 < baseStart_6385328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385335 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_6385335 : Nat := 118140960795 + 6385335 * 2 ^ 59
def prefixEnd_6385335 : Nat := 4983230072969 + 3 ^ 40 * 6385335 * 2
def baseEnd_6385335 : Nat := 3278745994976880081146885

theorem tailTrace_6385335 : CollatzResearch.WordTrace tailWord_6385335 prefixEnd_6385335 3278745994976880081146885 := by
  unfold tailWord_6385335
  simp only [CollatzResearch.WordTrace]
  refine ⟨232892300322029298241709459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155261533548019532161139639 232892300322029298241709459)
  ·
    refine ⟨349338450483043947362564189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232892300322029298241709459 349338450483043947362564189)
    ·
      refine ⟨131001918931141480260961571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349338450483043947362564189 131001918931141480260961571)
      ·
        refine ⟨196502878396712220391442357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131001918931141480260961571 196502878396712220391442357)
        ·
          refine ⟨18422144849691770661697721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196502878396712220391442357 18422144849691770661697721)
          ·
            refine ⟨13816608637268827996273291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18422144849691770661697721 13816608637268827996273291)
            ·
              refine ⟨20724912955903241994409937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13816608637268827996273291 20724912955903241994409937)
              ·
                refine ⟨15543684716927431495807453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20724912955903241994409937 15543684716927431495807453)
                ·
                  refine ⟨5828881768847786810927795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15543684716927431495807453 5828881768847786810927795)
                  ·
                    refine ⟨8743322653271680216391693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828881768847786810927795 8743322653271680216391693)
                    ·
                      refine ⟨3278745994976880081146885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743322653271680216391693 3278745994976880081146885)
                      ·
                        rfl

theorem cell23_6385335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_6385335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385335 prefixEnd_6385335 := by exact prefixLift 6385335
  have htrace : WordTrace (prefixWord ++ tailWord_6385335) baseStart_6385335 baseEnd_6385335 := by
    simpa [prefixWord, tailWord_6385335, baseEnd_6385335] using wordTrace_append hprefix tailTrace_6385335
  have hstable : (prefixWord ++ tailWord_6385335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385335).length < 2 ^ (prefixWord ++ tailWord_6385335).sum := by decide
  have hdescent : baseEnd_6385335 < baseStart_6385335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385351 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 1, 6]
def baseStart_6385351 : Nat := 118140960795 + 6385351 * 2 ^ 59
def prefixEnd_6385351 : Nat := 4983230072969 + 3 ^ 40 * 6385351 * 2
def baseEnd_6385351 : Nat := 1092918070222450672848937

theorem tailTrace_6385351 : CollatzResearch.WordTrace tailWord_6385351 prefixEnd_6385351 1092918070222450672848937 := by
  unfold tailWord_6385351
  simp only [CollatzResearch.WordTrace]
  refine ⟨232892883889971332974291907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155261922593314221982861271 232892883889971332974291907)
  ·
    refine ⟨349339325834956999461437861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232892883889971332974291907 349339325834956999461437861)
    ·
      refine ⟨65501123594054437399019599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349339325834956999461437861 65501123594054437399019599)
      ·
        refine ⟨98251685391081656098529399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65501123594054437399019599 98251685391081656098529399)
        ·
          refine ⟨147377528086622484147794099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98251685391081656098529399 147377528086622484147794099)
          ·
            refine ⟨221066292129933726221691149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147377528086622484147794099 221066292129933726221691149)
            ·
              refine ⟨82899859548725147333134181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221066292129933726221691149 82899859548725147333134181)
              ·
                refine ⟨15543723665385965124962659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82899859548725147333134181 15543723665385965124962659)
                ·
                  refine ⟨23315585498078947687443989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15543723665385965124962659 23315585498078947687443989)
                  ·
                    refine ⟨1092918070222450672848937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23315585498078947687443989 1092918070222450672848937)
                    ·
                      rfl

theorem cell23_6385351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_6385351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385351 prefixEnd_6385351 := by exact prefixLift 6385351
  have htrace : WordTrace (prefixWord ++ tailWord_6385351) baseStart_6385351 baseEnd_6385351 := by
    simpa [prefixWord, tailWord_6385351, baseEnd_6385351] using wordTrace_append hprefix tailTrace_6385351
  have hstable : (prefixWord ++ tailWord_6385351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385351).length < 2 ^ (prefixWord ++ tailWord_6385351).sum := by decide
  have hdescent : baseEnd_6385351 < baseStart_6385351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385352 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_6385352 : Nat := 118140960795 + 6385352 * 2 ^ 59
def prefixEnd_6385352 : Nat := 4983230072969 + 3 ^ 40 * 6385352 * 2
def baseEnd_6385352 : Nat := 3278754724148006514634307

theorem tailTrace_6385352 : CollatzResearch.WordTrace tailWord_6385352 prefixEnd_6385352 3278754724148006514634307 := by
  unfold tailWord_6385352
  simp only [CollatzResearch.WordTrace]
  refine ⟨116446460181483855072539155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155261946908645140096718873 116446460181483855072539155)
  ·
    refine ⟨174669690272225782608808733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116446460181483855072539155 174669690272225782608808733)
    ·
      refine ⟨65501133852084668478303275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174669690272225782608808733 65501133852084668478303275)
      ·
        refine ⟨98251700778127002717454913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65501133852084668478303275 98251700778127002717454913)
        ·
          refine ⟨73688775583595252038091185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98251700778127002717454913 73688775583595252038091185)
          ·
            refine ⟨55266581687696439028568389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73688775583595252038091185 55266581687696439028568389)
            ·
              refine ⟨10362484066443082317856573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55266581687696439028568389 10362484066443082317856573)
              ·
                refine ⟨3885931524916155869196215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10362484066443082317856573 3885931524916155869196215)
                ·
                  refine ⟨5828897287374233803794323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885931524916155869196215 5828897287374233803794323)
                  ·
                    refine ⟨8743345931061350705691485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828897287374233803794323 8743345931061350705691485)
                    ·
                      refine ⟨3278754724148006514634307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743345931061350705691485 3278754724148006514634307)
                      ·
                        rfl

theorem cell23_6385352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_6385352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385352 prefixEnd_6385352 := by exact prefixLift 6385352
  have htrace : WordTrace (prefixWord ++ tailWord_6385352) baseStart_6385352 baseEnd_6385352 := by
    simpa [prefixWord, tailWord_6385352, baseEnd_6385352] using wordTrace_append hprefix tailTrace_6385352
  have hstable : (prefixWord ++ tailWord_6385352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385352).length < 2 ^ (prefixWord ++ tailWord_6385352).sum := by decide
  have hdescent : baseEnd_6385352 < baseStart_6385352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385368 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 4, 4]
def baseStart_6385368 : Nat := 118140960795 + 6385368 * 2 ^ 59
def prefixEnd_6385368 : Nat := 4983230072969 + 3 ^ 40 * 6385368 * 2
def baseEnd_6385368 : Nat := 1092920979946159484011411

theorem tailTrace_6385368 : CollatzResearch.WordTrace tailWord_6385368 prefixEnd_6385368 1092920979946159484011411 := by
  unfold tailWord_6385368
  simp only [CollatzResearch.WordTrace]
  refine ⟨116446751965454872438830379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155262335953939829918440505 116446751965454872438830379)
  ·
    refine ⟨174670127948182308658245569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116446751965454872438830379 174670127948182308658245569)
    ·
      refine ⟨131002595961136731493684177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174670127948182308658245569 131002595961136731493684177)
      ·
        refine ⟨98251946970852548620263133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131002595961136731493684177 98251946970852548620263133)
        ·
          refine ⟨36844480114069705732598675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98251946970852548620263133 36844480114069705732598675)
          ·
            refine ⟨55266720171104558598898013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36844480114069705732598675 55266720171104558598898013)
            ·
              refine ⟨20725020064164209474586755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55266720171104558598898013 20725020064164209474586755)
              ·
                refine ⟨31087530096246314211880133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20725020064164209474586755 31087530096246314211880133)
                ·
                  refine ⟨5828911893046183914727525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31087530096246314211880133 5828911893046183914727525)
                  ·
                    refine ⟨1092920979946159484011411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5828911893046183914727525 1092920979946159484011411)
                    ·
                      rfl

theorem cell23_6385368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_6385368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385368 prefixEnd_6385368 := by exact prefixLift 6385368
  have htrace : WordTrace (prefixWord ++ tailWord_6385368) baseStart_6385368 baseEnd_6385368 := by
    simpa [prefixWord, tailWord_6385368, baseEnd_6385368] using wordTrace_append hprefix tailTrace_6385368
  have hstable : (prefixWord ++ tailWord_6385368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385368).length < 2 ^ (prefixWord ++ tailWord_6385368).sum := by decide
  have hdescent : baseEnd_6385368 < baseStart_6385368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385381 : List Nat := [1, 3, 1, 4, 1, 1, 2, 10]
def baseStart_6385381 : Nat := 118140960795 + 6385381 * 2 ^ 59
def prefixEnd_6385381 : Nat := 4983230072969 + 3 ^ 40 * 6385381 * 2
def baseEnd_6385381 : Nat := 121435911669888403747099

theorem tailTrace_6385381 : CollatzResearch.WordTrace tailWord_6385381 prefixEnd_6385381 121435911669888403747099 := by
  unfold tailWord_6385381
  simp only [CollatzResearch.WordTrace]
  refine ⟨232893978079862648097883997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155262652053241765398589331 232893978079862648097883997)
  ·
    refine ⟨87335241779948493036706499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232893978079862648097883997 87335241779948493036706499)
    ·
      refine ⟨131002862669922739555059749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87335241779948493036706499 131002862669922739555059749)
      ·
        refine ⟨24563036750610513666573703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131002862669922739555059749 24563036750610513666573703)
        ·
          refine ⟨36844555125915770499860555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24563036750610513666573703 36844555125915770499860555)
          ·
            refine ⟨55266832688873655749790833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36844555125915770499860555 55266832688873655749790833)
            ·
              refine ⟨41450124516655241812343125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55266832688873655749790833 41450124516655241812343125)
              ·
                refine ⟨121435911669888403747099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41450124516655241812343125 121435911669888403747099)
                ·
                  rfl

theorem cell23_6385381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 10].length) (baseStart_6385381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385381 prefixEnd_6385381 := by exact prefixLift 6385381
  have htrace : WordTrace (prefixWord ++ tailWord_6385381) baseStart_6385381 baseEnd_6385381 := by
    simpa [prefixWord, tailWord_6385381, baseEnd_6385381] using wordTrace_append hprefix tailTrace_6385381
  have hstable : (prefixWord ++ tailWord_6385381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385381).length < 2 ^ (prefixWord ++ tailWord_6385381).sum := by decide
  have hdescent : baseEnd_6385381 < baseStart_6385381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385388 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_6385388 : Nat := 118140960795 + 6385388 * 2 ^ 59
def prefixEnd_6385388 : Nat := 4983230072969 + 3 ^ 40 * 6385388 * 2
def baseEnd_6385388 : Nat := 3278773209451568373784141

theorem tailTrace_6385388 : CollatzResearch.WordTrace tailWord_6385388 prefixEnd_6385388 3278773209451568373784141 := by
  unfold tailWord_6385388
  simp only [CollatzResearch.WordTrace]
  refine ⟨116447116695418644146694409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155262822260558192195592545 116447116695418644146694409)
  ·
    refine ⟨87335337521563983110020807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116447116695418644146694409 87335337521563983110020807)
    ·
      refine ⟨131003006282345974665031211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87335337521563983110020807 131003006282345974665031211)
      ·
        refine ⟨196504509423518961997546817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131003006282345974665031211 196504509423518961997546817)
        ·
          refine ⟨147378382067639221498160113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196504509423518961997546817 147378382067639221498160113)
          ·
            refine ⟨110533786550729416123620085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147378382067639221498160113 110533786550729416123620085)
            ·
              refine ⟨10362542489130882761589383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110533786550729416123620085 10362542489130882761589383)
              ·
                refine ⟨15543813733696324142384075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10362542489130882761589383 15543813733696324142384075)
                ·
                  refine ⟨23315720600544486213576113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15543813733696324142384075 23315720600544486213576113)
                  ·
                    refine ⟨17486790450408364660182085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23315720600544486213576113 17486790450408364660182085)
                    ·
                      refine ⟨3278773209451568373784141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17486790450408364660182085 3278773209451568373784141)
                      ·
                        rfl

theorem cell23_6385388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_6385388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385388 prefixEnd_6385388 := by exact prefixLift 6385388
  have htrace : WordTrace (prefixWord ++ tailWord_6385388) baseStart_6385388 baseEnd_6385388 := by
    simpa [prefixWord, tailWord_6385388, baseEnd_6385388] using wordTrace_append hprefix tailTrace_6385388
  have hstable : (prefixWord ++ tailWord_6385388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385388).length < 2 ^ (prefixWord ++ tailWord_6385388).sum := by decide
  have hdescent : baseEnd_6385388 < baseStart_6385388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385398 : List Nat := [5, 1, 1, 1, 1, 4, 1, 9]
def baseStart_6385398 : Nat := 118140960795 + 6385398 * 2 ^ 59
def prefixEnd_6385398 : Nat := 4983230072969 + 3 ^ 40 * 6385398 * 2
def baseEnd_6385398 : Nat := 121436234972522716098485

theorem tailTrace_6385398 : CollatzResearch.WordTrace tailWord_6385398 prefixEnd_6385398 121436234972522716098485 := by
  unfold tailWord_6385398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555912382550066250078303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155263065413867373334168565 14555912382550066250078303)
  ·
    refine ⟨21833868573825099375117455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14555912382550066250078303 21833868573825099375117455)
    ·
      refine ⟨32750802860737649062676183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21833868573825099375117455 32750802860737649062676183)
      ·
        refine ⟨49126204291106473594014275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32750802860737649062676183 49126204291106473594014275)
        ·
          refine ⟨73689306436659710391021413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49126204291106473594014275 73689306436659710391021413)
          ·
            refine ⟨13816744956873695698316515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73689306436659710391021413 13816744956873695698316515)
            ·
              refine ⟨20725117435310543547474773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13816744956873695698316515 20725117435310543547474773)
              ·
                refine ⟨121436234972522716098485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20725117435310543547474773 121436234972522716098485)
                ·
                  rfl

theorem cell23_6385398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_6385398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385398 prefixEnd_6385398 := by exact prefixLift 6385398
  have htrace : WordTrace (prefixWord ++ tailWord_6385398) baseStart_6385398 baseEnd_6385398 := by
    simpa [prefixWord, tailWord_6385398, baseEnd_6385398] using wordTrace_append hprefix tailTrace_6385398
  have hstable : (prefixWord ++ tailWord_6385398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385398).length < 2 ^ (prefixWord ++ tailWord_6385398).sum := by decide
  have hdescent : baseEnd_6385398 < baseStart_6385398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385409 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_6385409 : Nat := 118140960795 + 6385409 * 2 ^ 59
def prefixEnd_6385409 : Nat := 4983230072969 + 3 ^ 40 * 6385409 * 2
def baseEnd_6385409 : Nat := 3278783992545312791621545

theorem tailTrace_6385409 : CollatzResearch.WordTrace tailWord_6385409 prefixEnd_6385409 3278783992545312791621545 := by
  unfold tailWord_6385409
  simp only [CollatzResearch.WordTrace]
  refine ⟨232894999323761208879903281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155263332882507472586602187 232894999323761208879903281)
  ·
    refine ⟨174671249492820906659927461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232894999323761208879903281 174671249492820906659927461)
    ·
      refine ⟨32750859279903919998736399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174671249492820906659927461 32750859279903919998736399)
      ·
        refine ⟨49126288919855879998104599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32750859279903919998736399 49126288919855879998104599)
        ·
          refine ⟨73689433379783819997156899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49126288919855879998104599 73689433379783819997156899)
          ·
            refine ⟨110534150069675729995735349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73689433379783819997156899 110534150069675729995735349)
            ·
              refine ⟨10362576569032099687100189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110534150069675729995735349 10362576569032099687100189)
              ·
                refine ⟨3885966213387037382662571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10362576569032099687100189 3885966213387037382662571)
                ·
                  refine ⟨5828949320080556073993857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885966213387037382662571 5828949320080556073993857)
                  ·
                    refine ⟨4371711990060417055495393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828949320080556073993857 4371711990060417055495393)
                    ·
                      refine ⟨3278783992545312791621545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371711990060417055495393 3278783992545312791621545)
                      ·
                        rfl

theorem cell23_6385409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_6385409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385409 prefixEnd_6385409 := by exact prefixLift 6385409
  have htrace : WordTrace (prefixWord ++ tailWord_6385409) baseStart_6385409 baseEnd_6385409 := by
    simpa [prefixWord, tailWord_6385409, baseEnd_6385409] using wordTrace_append hprefix tailTrace_6385409
  have hstable : (prefixWord ++ tailWord_6385409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385409).length < 2 ^ (prefixWord ++ tailWord_6385409).sum := by decide
  have hdescent : baseEnd_6385409 < baseStart_6385409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385415 : List Nat := [1, 1, 4, 4, 3, 1, 9]
def baseStart_6385415 : Nat := 118140960795 + 6385415 * 2 ^ 59
def prefixEnd_6385415 : Nat := 4983230072969 + 3 ^ 40 * 6385415 * 2
def baseEnd_6385415 : Nat := 40478852758385676149957

theorem tailTrace_6385415 : CollatzResearch.WordTrace tailWord_6385415 prefixEnd_6385415 40478852758385676149957 := by
  unfold tailWord_6385415
  simp only [CollatzResearch.WordTrace]
  refine ⟨232895218161739471904621699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155263478774492981269747799 232895218161739471904621699)
  ·
    refine ⟨349342827242609207856932549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232895218161739471904621699 349342827242609207856932549)
    ·
      refine ⟨65501780107989226473174853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349342827242609207856932549 65501780107989226473174853)
      ·
        refine ⟨12281583770247979963720285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65501780107989226473174853 12281583770247979963720285)
        ·
          refine ⟨4605593913842992486395107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12281583770247979963720285 4605593913842992486395107)
          ·
            refine ⟨6908390870764488729592661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605593913842992486395107 6908390870764488729592661)
            ·
              refine ⟨40478852758385676149957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6908390870764488729592661 40478852758385676149957)
              ·
                rfl

theorem cell23_6385415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 9].length) (baseStart_6385415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385415 prefixEnd_6385415 := by exact prefixLift 6385415
  have htrace : WordTrace (prefixWord ++ tailWord_6385415) baseStart_6385415 baseEnd_6385415 := by
    simpa [prefixWord, tailWord_6385415, baseEnd_6385415] using wordTrace_append hprefix tailTrace_6385415
  have hstable : (prefixWord ++ tailWord_6385415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385415).length < 2 ^ (prefixWord ++ tailWord_6385415).sum := by decide
  have hdescent : baseEnd_6385415 < baseStart_6385415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385425 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_6385425 : Nat := 118140960795 + 6385425 * 2 ^ 59
def prefixEnd_6385425 : Nat := 4983230072969 + 3 ^ 40 * 6385425 * 2
def baseEnd_6385425 : Nat := 3278792208235784729021471

theorem tailTrace_6385425 : CollatzResearch.WordTrace tailWord_6385425 prefixEnd_6385425 3278792208235784729021471 := by
  unfold tailWord_6385425
  simp only [CollatzResearch.WordTrace]
  refine ⟨232895582891703243612485729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155263721927802162408323819 232895582891703243612485729)
  ·
    refine ⟨174671687168777432709364297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232895582891703243612485729 174671687168777432709364297)
    ·
      refine ⟨131003765376583074532023223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174671687168777432709364297 131003765376583074532023223)
      ·
        refine ⟨196505648064874611798034835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131003765376583074532023223 196505648064874611798034835)
        ·
          refine ⟨294758472097311917697052253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196505648064874611798034835 294758472097311917697052253)
          ·
            refine ⟨110534427036491969136394595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294758472097311917697052253 110534427036491969136394595)
            ·
              refine ⟨165801640554737953704591893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110534427036491969136394595 165801640554737953704591893)
              ·
                refine ⟨7771951901003341579902745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165801640554737953704591893 7771951901003341579902745)
                ·
                  refine ⟨5828963925752506184927059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7771951901003341579902745 5828963925752506184927059)
                  ·
                    refine ⟨8743445888628759277390589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828963925752506184927059 8743445888628759277390589)
                    ·
                      refine ⟨3278792208235784729021471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743445888628759277390589 3278792208235784729021471)
                      ·
                        rfl

theorem cell23_6385425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_6385425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385425 prefixEnd_6385425 := by exact prefixLift 6385425
  have htrace : WordTrace (prefixWord ++ tailWord_6385425) baseStart_6385425 baseEnd_6385425 := by
    simpa [prefixWord, tailWord_6385425, baseEnd_6385425] using wordTrace_append hprefix tailTrace_6385425
  have hstable : (prefixWord ++ tailWord_6385425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385425).length < 2 ^ (prefixWord ++ tailWord_6385425).sum := by decide
  have hdescent : baseEnd_6385425 < baseStart_6385425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385426 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6385426 : Nat := 118140960795 + 6385426 * 2 ^ 59
def prefixEnd_6385426 : Nat := 4983230072969 + 3 ^ 40 * 6385426 * 2
def baseEnd_6385426 : Nat := 3278792721716439225108967

theorem tailTrace_6385426 : CollatzResearch.WordTrace tailWord_6385426 prefixEnd_6385426 3278792721716439225108967 := by
  unfold tailWord_6385426
  simp only [CollatzResearch.WordTrace]
  refine ⟨58223904841174905195818033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155263746243133080522181421 58223904841174905195818033)
  ·
    refine ⟨43667928630881178896863525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58223904841174905195818033 43667928630881178896863525)
    ·
      refine ⟨8187736618290221043161911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43667928630881178896863525 8187736618290221043161911)
      ·
        refine ⟨12281604927435331564742867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8187736618290221043161911 12281604927435331564742867)
        ·
          refine ⟨18422407391152997347114301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12281604927435331564742867 18422407391152997347114301)
          ·
            refine ⟨6908402771682374005167863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18422407391152997347114301 6908402771682374005167863)
            ·
              refine ⟨10362604157523561007751795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908402771682374005167863 10362604157523561007751795)
              ·
                refine ⟨15543906236285341511627693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10362604157523561007751795 15543906236285341511627693)
                ·
                  refine ⟨5828964838607003066860385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15543906236285341511627693 5828964838607003066860385)
                  ·
                    refine ⟨4371723628955252300145289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828964838607003066860385 4371723628955252300145289)
                    ·
                      refine ⟨3278792721716439225108967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371723628955252300145289 3278792721716439225108967)
                      ·
                        rfl

theorem cell23_6385426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6385426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385426 prefixEnd_6385426 := by exact prefixLift 6385426
  have htrace : WordTrace (prefixWord ++ tailWord_6385426) baseStart_6385426 baseEnd_6385426 := by
    simpa [prefixWord, tailWord_6385426, baseEnd_6385426] using wordTrace_append hprefix tailTrace_6385426
  have hstable : (prefixWord ++ tailWord_6385426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385426).length < 2 ^ (prefixWord ++ tailWord_6385426).sum := by decide
  have hdescent : baseEnd_6385426 < baseStart_6385426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385442 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_6385442 : Nat := 118140960795 + 6385442 * 2 ^ 59
def prefixEnd_6385442 : Nat := 4983230072969 + 3 ^ 40 * 6385442 * 2
def baseEnd_6385442 : Nat := 3278800937406911162508893

theorem tailTrace_6385442 : CollatzResearch.WordTrace tailWord_6385442 prefixEnd_6385442 3278800937406911162508893 := by
  unfold tailWord_6385442
  simp only [CollatzResearch.WordTrace]
  refine ⟨58224050733160413878963645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155264135288427770343903053 58224050733160413878963645)
  ·
    refine ⟨21834019024935155204611367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58224050733160413878963645 21834019024935155204611367)
    ·
      refine ⟨32751028537402732806917051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21834019024935155204611367 32751028537402732806917051)
      ·
        refine ⟨49126542806104099210375577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32751028537402732806917051 49126542806104099210375577)
        ·
          refine ⟨36844907104578074407781683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49126542806104099210375577 36844907104578074407781683)
          ·
            refine ⟨55267360656867111611672525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36844907104578074407781683 55267360656867111611672525)
            ·
              refine ⟨20725260246325166854377197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55267360656867111611672525 20725260246325166854377197)
              ·
                refine ⟨7771972592371937570391449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20725260246325166854377197 7771972592371937570391449)
                ·
                  refine ⟨5828979444278953177793587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7771972592371937570391449 5828979444278953177793587)
                  ·
                    refine ⟨8743469166418429766690381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828979444278953177793587 8743469166418429766690381)
                    ·
                      refine ⟨3278800937406911162508893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743469166418429766690381 3278800937406911162508893)
                      ·
                        rfl

theorem cell23_6385442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_6385442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385442 prefixEnd_6385442 := by exact prefixLift 6385442
  have htrace : WordTrace (prefixWord ++ tailWord_6385442) baseStart_6385442 baseEnd_6385442 := by
    simpa [prefixWord, tailWord_6385442, baseEnd_6385442] using wordTrace_append hprefix tailTrace_6385442
  have hstable : (prefixWord ++ tailWord_6385442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385442).length < 2 ^ (prefixWord ++ tailWord_6385442).sum := by decide
  have hdescent : baseEnd_6385442 < baseStart_6385442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385452 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 1, 3, 2]
def baseStart_6385452 : Nat := 118140960795 + 6385452 * 2 ^ 59
def prefixEnd_6385452 : Nat := 4983230072969 + 3 ^ 40 * 6385452 * 2
def baseEnd_6385452 : Nat := 3278806072213456123383847

theorem tailTrace_6385452 : CollatzResearch.WordTrace tailWord_6385452 prefixEnd_6385452 3278806072213456123383847 := by
  unfold tailWord_6385452
  simp only [CollatzResearch.WordTrace]
  refine ⟨116448283831302713611859305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155264378441736951482479073 116448283831302713611859305)
  ·
    refine ⟨87336212873477035208894479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116448283831302713611859305 87336212873477035208894479)
    ·
      refine ⟨131004319310215552813341719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87336212873477035208894479 131004319310215552813341719)
      ·
        refine ⟨196506478965323329220012579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131004319310215552813341719 196506478965323329220012579)
        ·
          refine ⟨294759718447984993830018869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196506478965323329220012579 294759718447984993830018869)
          ·
            refine ⟨27633723604498593171564269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294759718447984993830018869 27633723604498593171564269)
            ·
              refine ⟨10362646351686972439336601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27633723604498593171564269 10362646351686972439336601)
              ·
                refine ⟨7771984763765229329502451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10362646351686972439336601 7771984763765229329502451)
                ·
                  refine ⟨11657977145647843994253677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7771984763765229329502451 11657977145647843994253677)
                  ·
                    refine ⟨4371741429617941497845129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11657977145647843994253677 4371741429617941497845129)
                    ·
                      refine ⟨3278806072213456123383847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371741429617941497845129 3278806072213456123383847)
                      ·
                        rfl

theorem cell23_6385452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_6385452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385452 prefixEnd_6385452 := by exact prefixLift 6385452
  have htrace : WordTrace (prefixWord ++ tailWord_6385452) baseStart_6385452 baseEnd_6385452 := by
    simpa [prefixWord, tailWord_6385452, baseEnd_6385452] using wordTrace_append hprefix tailTrace_6385452
  have hstable : (prefixWord ++ tailWord_6385452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385452).length < 2 ^ (prefixWord ++ tailWord_6385452).sum := by decide
  have hdescent : baseEnd_6385452 < baseStart_6385452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385468 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_6385468 : Nat := 118140960795 + 6385468 * 2 ^ 59
def prefixEnd_6385468 : Nat := 4983230072969 + 3 ^ 40 * 6385468 * 2
def baseEnd_6385468 : Nat := 3278814287903928060783773

theorem tailTrace_6385468 : CollatzResearch.WordTrace tailWord_6385468 prefixEnd_6385468 3278814287903928060783773 := by
  unfold tailWord_6385468
  simp only [CollatzResearch.WordTrace]
  refine ⟨116448575615273730978150529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155264767487031641304200705 116448575615273730978150529)
  ·
    refine ⟨87336431711455298233612897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116448575615273730978150529 87336431711455298233612897)
    ·
      refine ⟨65502323783591473675209673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87336431711455298233612897 65502323783591473675209673)
      ·
        refine ⟨49126742837693605256407255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65502323783591473675209673 49126742837693605256407255)
        ·
          refine ⟨73690114256540407884610883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49126742837693605256407255 73690114256540407884610883)
          ·
            refine ⟨110535171384810611826916325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73690114256540407884610883 110535171384810611826916325)
            ·
              refine ⟨20725344634651989717546811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110535171384810611826916325 20725344634651989717546811)
              ·
                refine ⟨31088016951977984576320217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20725344634651989717546811 31088016951977984576320217)
                ·
                  refine ⟨23316012713983488432240163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31088016951977984576320217 23316012713983488432240163)
                  ·
                    refine ⟨34974019070975232648360245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23316012713983488432240163 34974019070975232648360245)
                    ·
                      refine ⟨3278814287903928060783773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34974019070975232648360245 3278814287903928060783773)
                      ·
                        rfl

theorem cell23_6385468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_6385468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385468 prefixEnd_6385468 := by exact prefixLift 6385468
  have htrace : WordTrace (prefixWord ++ tailWord_6385468) baseStart_6385468 baseEnd_6385468 := by
    simpa [prefixWord, tailWord_6385468, baseEnd_6385468] using wordTrace_append hprefix tailTrace_6385468
  have hstable : (prefixWord ++ tailWord_6385468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385468).length < 2 ^ (prefixWord ++ tailWord_6385468).sum := by decide
  have hdescent : baseEnd_6385468 < baseStart_6385468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385491 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_6385491 : Nat := 118140960795 + 6385491 * 2 ^ 59
def prefixEnd_6385491 : Nat := 4983230072969 + 3 ^ 40 * 6385491 * 2
def baseEnd_6385491 : Nat := 3278826097958981470796167

theorem tailTrace_6385491 : CollatzResearch.WordTrace tailWord_6385491 prefixEnd_6385491 3278826097958981470796167 := by
  unfold tailWord_6385491
  simp only [CollatzResearch.WordTrace]
  refine ⟨232897990109464136884388327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155265326739642757922925551 232897990109464136884388327)
  ·
    refine ⟨349346985164196205326582491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232897990109464136884388327 349346985164196205326582491)
    ·
      refine ⟨524020477746294307989873737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349346985164196205326582491 524020477746294307989873737)
      ·
        refine ⟨393015358309720730992405303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524020477746294307989873737 393015358309720730992405303)
        ·
          refine ⟨589523037464581096488607955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393015358309720730992405303 589523037464581096488607955)
          ·
            refine ⟨884284556196871644732911933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589523037464581096488607955 884284556196871644732911933)
            ·
              refine ⟨331606708573826866774841975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884284556196871644732911933 331606708573826866774841975)
              ·
                refine ⟨497410062860740300162262963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331606708573826866774841975 497410062860740300162262963)
                ·
                  refine ⟨746115094291110450243394445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497410062860740300162262963 746115094291110450243394445)
                  ·
                    refine ⟨279793160359166418841272917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746115094291110450243394445 279793160359166418841272917)
                    ·
                      refine ⟨3278826097958981470796167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 279793160359166418841272917 3278826097958981470796167)
                      ·
                        rfl

theorem cell23_6385491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_6385491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385491 prefixEnd_6385491 := by exact prefixLift 6385491
  have htrace : WordTrace (prefixWord ++ tailWord_6385491) baseStart_6385491 baseEnd_6385491 := by
    simpa [prefixWord, tailWord_6385491, baseEnd_6385491] using wordTrace_append hprefix tailTrace_6385491
  have hstable : (prefixWord ++ tailWord_6385491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385491).length < 2 ^ (prefixWord ++ tailWord_6385491).sum := by decide
  have hdescent : baseEnd_6385491 < baseStart_6385491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385495 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_6385495 : Nat := 118140960795 + 6385495 * 2 ^ 59
def prefixEnd_6385495 : Nat := 4983230072969 + 3 ^ 40 * 6385495 * 2
def baseEnd_6385495 : Nat := 3278828151881599455146149

theorem tailTrace_6385495 : CollatzResearch.WordTrace tailWord_6385495 prefixEnd_6385495 3278828151881599455146149 := by
  unfold tailWord_6385495
  simp only [CollatzResearch.WordTrace]
  refine ⟨232898136001449645567533939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155265424000966430378355959 232898136001449645567533939)
  ·
    refine ⟨349347204002174468351300909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232898136001449645567533939 349347204002174468351300909)
    ·
      refine ⟨131005201500815425631737841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349347204002174468351300909 131005201500815425631737841)
      ·
        refine ⟨98253901125611569223803381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131005201500815425631737841 98253901125611569223803381)
        ·
          refine ⟨9211303230526084614731567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98253901125611569223803381 9211303230526084614731567)
          ·
            refine ⟨13816954845789126922097351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9211303230526084614731567 13816954845789126922097351)
            ·
              refine ⟨20725432268683690383146027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13816954845789126922097351 20725432268683690383146027)
              ·
                refine ⟨31088148403025535574719041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20725432268683690383146027 31088148403025535574719041)
                ·
                  refine ⟨23316111302269151681039281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31088148403025535574719041 23316111302269151681039281)
                  ·
                    refine ⟨17487083476701863760779461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23316111302269151681039281 17487083476701863760779461)
                    ·
                      refine ⟨3278828151881599455146149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17487083476701863760779461 3278828151881599455146149)
                      ·
                        rfl

theorem cell23_6385495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_6385495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385495 prefixEnd_6385495 := by exact prefixLift 6385495
  have htrace : WordTrace (prefixWord ++ tailWord_6385495) baseStart_6385495 baseEnd_6385495 := by
    simpa [prefixWord, tailWord_6385495, baseEnd_6385495] using wordTrace_append hprefix tailTrace_6385495
  have hstable : (prefixWord ++ tailWord_6385495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385495).length < 2 ^ (prefixWord ++ tailWord_6385495).sum := by decide
  have hdescent : baseEnd_6385495 < baseStart_6385495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385568 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6385568 : Nat := 118140960795 + 6385568 * 2 ^ 59
def prefixEnd_6385568 : Nat := 4983230072969 + 3 ^ 40 * 6385568 * 2
def baseEnd_6385568 : Nat := 3278865635969377669533313

theorem tailTrace_6385568 : CollatzResearch.WordTrace tailWord_6385568 prefixEnd_6385568 3278865635969377669533313 := by
  unfold tailWord_6385568
  simp only [CollatzResearch.WordTrace]
  refine ⟨116450399265092589517470679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155267199020123452689960905 116450399265092589517470679)
  ·
    refine ⟨174675598897638884276206019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116450399265092589517470679 174675598897638884276206019)
    ·
      refine ⟨262013398346458326414309029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174675598897638884276206019 262013398346458326414309029)
      ·
        refine ⟨49127512189960936202682943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262013398346458326414309029 49127512189960936202682943)
        ·
          refine ⟨73691268284941404304024415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49127512189960936202682943 73691268284941404304024415)
          ·
            refine ⟨110536902427412106456036623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73691268284941404304024415 110536902427412106456036623)
            ·
              refine ⟨165805353641118159684054935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110536902427412106456036623 165805353641118159684054935)
              ·
                refine ⟨248708030461677239526082403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165805353641118159684054935 248708030461677239526082403)
                ·
                  refine ⟨373062045692515859289123605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248708030461677239526082403 373062045692515859289123605)
                  ·
                    refine ⟨17487283391836680904177669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 373062045692515859289123605 17487283391836680904177669)
                    ·
                      refine ⟨3278865635969377669533313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17487283391836680904177669 3278865635969377669533313)
                      ·
                        rfl

theorem cell23_6385568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6385568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385568 prefixEnd_6385568 := by exact prefixLift 6385568
  have htrace : WordTrace (prefixWord ++ tailWord_6385568) baseStart_6385568 baseEnd_6385568 := by
    simpa [prefixWord, tailWord_6385568, baseEnd_6385568] using wordTrace_append hprefix tailTrace_6385568
  have hstable : (prefixWord ++ tailWord_6385568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385568).length < 2 ^ (prefixWord ++ tailWord_6385568).sum := by decide
  have hdescent : baseEnd_6385568 < baseStart_6385568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385599 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 1, 4]
def baseStart_6385599 : Nat := 118140960795 + 6385599 * 2 ^ 59
def prefixEnd_6385599 : Nat := 4983230072969 + 3 ^ 40 * 6385599 * 2
def baseEnd_6385599 : Nat := 1092960517956555682748557

theorem tailTrace_6385599 : CollatzResearch.WordTrace tailWord_6385599 prefixEnd_6385599 1092960517956555682748557 := by
  unfold tailWord_6385599
  simp only [CollatzResearch.WordTrace]
  refine ⟨232901929193072871329319851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155267952795381914219546567 232901929193072871329319851)
  ·
    refine ⟨349352893789609306993979777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232901929193072871329319851 349352893789609306993979777)
    ·
      refine ⟨262014670342206980245484833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349352893789609306993979777 262014670342206980245484833)
      ·
        refine ⟨196511002756655235184113625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262014670342206980245484833 196511002756655235184113625)
        ·
          refine ⟨147383252067491426388085219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196511002756655235184113625 147383252067491426388085219)
          ·
            refine ⟨221074878101237139582127829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147383252067491426388085219 221074878101237139582127829)
            ·
              refine ⟨5181442455497745458956121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 221074878101237139582127829 5181442455497745458956121)
              ·
                refine ⟨3886081841623309094217091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181442455497745458956121 3886081841623309094217091)
                ·
                  refine ⟨5829122762434963641325637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886081841623309094217091 5829122762434963641325637)
                  ·
                    refine ⟨1092960517956555682748557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5829122762434963641325637 1092960517956555682748557)
                    ·
                      rfl

theorem cell23_6385599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 4].length) (baseStart_6385599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385599 prefixEnd_6385599 := by exact prefixLift 6385599
  have htrace : WordTrace (prefixWord ++ tailWord_6385599) baseStart_6385599 baseEnd_6385599 := by
    simpa [prefixWord, tailWord_6385599, baseEnd_6385599] using wordTrace_append hprefix tailTrace_6385599
  have hstable : (prefixWord ++ tailWord_6385599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385599).length < 2 ^ (prefixWord ++ tailWord_6385599).sum := by decide
  have hdescent : baseEnd_6385599 < baseStart_6385599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385612 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 6]
def baseStart_6385612 : Nat := 118140960795 + 6385612 * 2 ^ 59
def prefixEnd_6385612 : Nat := 4983230072969 + 3 ^ 40 * 6385612 * 2
def baseEnd_6385612 : Nat := 364320914346463944153679

theorem tailTrace_6385612 : CollatzResearch.WordTrace tailWord_6385612 prefixEnd_6385612 364320914346463944153679 := by
  unfold tailWord_6385612
  simp only [CollatzResearch.WordTrace]
  refine ⟨116451201671012887274771545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155268268894683849699695393 116451201671012887274771545)
  ·
    refine ⟨87338401253259665456078659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116451201671012887274771545 87338401253259665456078659)
    ·
      refine ⟨131007601879889498184117989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87338401253259665456078659 131007601879889498184117989)
      ·
        refine ⟨24563925352479280909522123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131007601879889498184117989 24563925352479280909522123)
        ·
          refine ⟨36845888028718921364283185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24563925352479280909522123 36845888028718921364283185)
          ·
            refine ⟨27634416021539191023212389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36845888028718921364283185 27634416021539191023212389)
            ·
              refine ⟨5181453004038598316852323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27634416021539191023212389 5181453004038598316852323)
              ·
                refine ⟨7772179506057897475278485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181453004038598316852323 7772179506057897475278485)
                ·
                  refine ⟨364320914346463944153679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772179506057897475278485 364320914346463944153679)
                  ·
                    rfl

theorem cell23_6385612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_6385612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385612 prefixEnd_6385612 := by exact prefixLift 6385612
  have htrace : WordTrace (prefixWord ++ tailWord_6385612) baseStart_6385612 baseEnd_6385612 := by
    simpa [prefixWord, tailWord_6385612, baseEnd_6385612] using wordTrace_append hprefix tailTrace_6385612
  have hstable : (prefixWord ++ tailWord_6385612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385612).length < 2 ^ (prefixWord ++ tailWord_6385612).sum := by decide
  have hdescent : baseEnd_6385612 < baseStart_6385612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385656 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 1, 1, 3]
def baseStart_6385656 : Nat := 118140960795 + 6385656 * 2 ^ 59
def prefixEnd_6385656 : Nat := 4983230072969 + 3 ^ 40 * 6385656 * 2
def baseEnd_6385656 : Nat := 3278910822266973325232909

theorem tailTrace_6385656 : CollatzResearch.WordTrace tailWord_6385656 prefixEnd_6385656 3278910822266973325232909 := by
  unfold tailWord_6385656
  simp only [CollatzResearch.WordTrace]
  refine ⟨116452004076933185032072411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155269338769244246709429881 116452004076933185032072411)
  ·
    refine ⟨174678006115399777548108617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116452004076933185032072411 174678006115399777548108617)
    ·
      refine ⟨131008504586549833161081463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174678006115399777548108617 131008504586549833161081463)
      ·
        refine ⟨196512756879824749741622195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131008504586549833161081463 196512756879824749741622195)
        ·
          refine ⟨294769135319737124612433293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196512756879824749741622195 294769135319737124612433293)
          ·
            refine ⟨110538425744901421729662485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294769135319737124612433293 110538425744901421729662485)
            ·
              refine ⟨5181488706792254143577929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110538425744901421729662485 5181488706792254143577929)
              ·
                refine ⟨3886116530094190607683447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181488706792254143577929 3886116530094190607683447)
                ·
                  refine ⟨5829174795141285911525171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886116530094190607683447 5829174795141285911525171)
                  ·
                    refine ⟨8743762192711928867287757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5829174795141285911525171 8743762192711928867287757)
                    ·
                      refine ⟨3278910822266973325232909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743762192711928867287757 3278910822266973325232909)
                      ·
                        rfl

theorem cell23_6385656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_6385656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385656 prefixEnd_6385656 := by exact prefixLift 6385656
  have htrace : WordTrace (prefixWord ++ tailWord_6385656) baseStart_6385656 baseEnd_6385656 := by
    simpa [prefixWord, tailWord_6385656, baseEnd_6385656] using wordTrace_append hprefix tailTrace_6385656
  have hstable : (prefixWord ++ tailWord_6385656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385656).length < 2 ^ (prefixWord ++ tailWord_6385656).sum := by decide
  have hdescent : baseEnd_6385656 < baseStart_6385656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385665 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_6385665 : Nat := 118140960795 + 6385665 * 2 ^ 59
def prefixEnd_6385665 : Nat := 4983230072969 + 3 ^ 40 * 6385665 * 2
def baseEnd_6385665 : Nat := 3278915443592863790020367

theorem tailTrace_6385665 : CollatzResearch.WordTrace tailWord_6385665 prefixEnd_6385665 3278915443592863790020367 := by
  unfold tailWord_6385665
  simp only [CollatzResearch.WordTrace]
  refine ⟨232904336410833764601222449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155269557607222509734148299 232904336410833764601222449)
  ·
    refine ⟨174678252308125323450916837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232904336410833764601222449 174678252308125323450916837)
    ·
      refine ⟨32752172307773498147046907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174678252308125323450916837 32752172307773498147046907)
      ·
        refine ⟨49128258461660247220570361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32752172307773498147046907 49128258461660247220570361)
        ·
          refine ⟨36846193846245185415427771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49128258461660247220570361 36846193846245185415427771)
          ·
            refine ⟨55269290769367778123141657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36846193846245185415427771 55269290769367778123141657)
            ·
              refine ⟨41451968077025833592356243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55269290769367778123141657 41451968077025833592356243)
              ·
                refine ⟨62177952115538750388534365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41451968077025833592356243 62177952115538750388534365)
                ·
                  refine ⟨23316732043327031395700387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62177952115538750388534365 23316732043327031395700387)
                  ·
                    refine ⟨34975098064990547093550581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23316732043327031395700387 34975098064990547093550581)
                    ·
                      refine ⟨3278915443592863790020367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34975098064990547093550581 3278915443592863790020367)
                      ·
                        rfl

theorem cell23_6385665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_6385665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385665 prefixEnd_6385665 := by exact prefixLift 6385665
  have htrace : WordTrace (prefixWord ++ tailWord_6385665) baseStart_6385665 baseEnd_6385665 := by
    simpa [prefixWord, tailWord_6385665, baseEnd_6385665] using wordTrace_append hprefix tailTrace_6385665
  have hstable : (prefixWord ++ tailWord_6385665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385665).length < 2 ^ (prefixWord ++ tailWord_6385665).sum := by decide
  have hdescent : baseEnd_6385665 < baseStart_6385665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385672 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 2, 4]
def baseStart_6385672 : Nat := 118140960795 + 6385672 * 2 ^ 59
def prefixEnd_6385672 : Nat := 4983230072969 + 3 ^ 40 * 6385672 * 2
def baseEnd_6385672 : Nat := 1092973012652481754210945

theorem tailTrace_6385672 : CollatzResearch.WordTrace tailWord_6385672 prefixEnd_6385672 1092973012652481754210945 := by
  unfold tailWord_6385672
  simp only [CollatzResearch.WordTrace]
  refine ⟨116452295860904202398363635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155269727814538936531151513 116452295860904202398363635)
  ·
    refine ⟨174678443791356303597545453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116452295860904202398363635 174678443791356303597545453)
    ·
      refine ⟨65504416421758613849079545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174678443791356303597545453 65504416421758613849079545)
      ·
        refine ⟨49128312316318960386809659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65504416421758613849079545 49128312316318960386809659)
        ·
          refine ⟨73692468474478440580214489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49128312316318960386809659 73692468474478440580214489)
          ·
            refine ⟨55269351355858830435160867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73692468474478440580214489 55269351355858830435160867)
            ·
              refine ⟨82904027033788245652741301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55269351355858830435160867 82904027033788245652741301)
              ·
                refine ⟨7772252534417648029944497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82904027033788245652741301 7772252534417648029944497)
                ·
                  refine ⟨5829189400813236022458373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7772252534417648029944497 5829189400813236022458373)
                  ·
                    refine ⟨1092973012652481754210945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5829189400813236022458373 1092973012652481754210945)
                    ·
                      rfl

theorem cell23_6385672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_6385672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385672 prefixEnd_6385672 := by exact prefixLift 6385672
  have htrace : WordTrace (prefixWord ++ tailWord_6385672) baseStart_6385672 baseEnd_6385672 := by
    simpa [prefixWord, tailWord_6385672, baseEnd_6385672] using wordTrace_append hprefix tailTrace_6385672
  have hstable : (prefixWord ++ tailWord_6385672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385672).length < 2 ^ (prefixWord ++ tailWord_6385672).sum := by decide
  have hdescent : baseEnd_6385672 < baseStart_6385672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385692 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6385692 : Nat := 118140960795 + 6385692 * 2 ^ 59
def prefixEnd_6385692 : Nat := 4983230072969 + 3 ^ 40 * 6385692 * 2
def baseEnd_6385692 : Nat := 3278929307570535184382743

theorem tailTrace_6385692 : CollatzResearch.WordTrace tailWord_6385692 prefixEnd_6385692 3278929307570535184382743 := by
  unfold tailWord_6385692
  simp only [CollatzResearch.WordTrace]
  refine ⟨116452660590867974106227665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155270214121157298808303553 116452660590867974106227665)
  ·
    refine ⟨87339495443150980579670749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116452660590867974106227665 87339495443150980579670749)
    ·
      refine ⟨32752310791181617717376531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87339495443150980579670749 32752310791181617717376531)
      ·
        refine ⟨49128466186772426576064797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32752310791181617717376531 49128466186772426576064797)
        ·
          refine ⟨18423174820039659966024299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49128466186772426576064797 18423174820039659966024299)
          ·
            refine ⟨27634762230059489949036449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18423174820039659966024299 27634762230059489949036449)
            ·
              refine ⟨20726071672544617461777337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27634762230059489949036449 20726071672544617461777337)
              ·
                refine ⟨15544553754408463096333003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20726071672544617461777337 15544553754408463096333003)
                ·
                  refine ⟨23316830631612694644499505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15544553754408463096333003 23316830631612694644499505)
                  ·
                    refine ⟨17487622973709520983374629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23316830631612694644499505 17487622973709520983374629)
                    ·
                      refine ⟨3278929307570535184382743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17487622973709520983374629 3278929307570535184382743)
                      ·
                        rfl

theorem cell23_6385692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6385692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385692 prefixEnd_6385692 := by exact prefixLift 6385692
  have htrace : WordTrace (prefixWord ++ tailWord_6385692) baseStart_6385692 baseEnd_6385692 := by
    simpa [prefixWord, tailWord_6385692, baseEnd_6385692] using wordTrace_append hprefix tailTrace_6385692
  have hstable : (prefixWord ++ tailWord_6385692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385692).length < 2 ^ (prefixWord ++ tailWord_6385692).sum := by decide
  have hdescent : baseEnd_6385692 < baseStart_6385692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385706 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_6385706 : Nat := 118140960795 + 6385706 * 2 ^ 59
def prefixEnd_6385706 : Nat := 4983230072969 + 3 ^ 40 * 6385706 * 2
def baseEnd_6385706 : Nat := 1092978832099899376535893

theorem tailTrace_6385706 : CollatzResearch.WordTrace tailWord_6385706 prefixEnd_6385706 1092978832099899376535893 := by
  unfold tailWord_6385706
  simp only [CollatzResearch.WordTrace]
  refine ⟨58226457950921307150866243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155270554535790152402309981 58226457950921307150866243)
  ·
    refine ⟨87339686926381960726299365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58226457950921307150866243 87339686926381960726299365)
    ·
      refine ⟨16376191298696617636181131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87339686926381960726299365 16376191298696617636181131)
      ·
        refine ⟨24564286948044926454271697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376191298696617636181131 24564286948044926454271697)
        ·
          refine ⟨18423215211033694840703773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24564286948044926454271697 18423215211033694840703773)
          ·
            refine ⟨6908705704137635565263915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18423215211033694840703773 6908705704137635565263915)
            ·
              refine ⟨10363058556206453347895873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908705704137635565263915 10363058556206453347895873)
              ·
                refine ⟨7772293917154840010921905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10363058556206453347895873 7772293917154840010921905)
                ·
                  refine ⟨5829220437866130008191429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7772293917154840010921905 5829220437866130008191429)
                  ·
                    refine ⟨1092978832099899376535893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5829220437866130008191429 1092978832099899376535893)
                    ·
                      rfl

theorem cell23_6385706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_6385706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385706 prefixEnd_6385706 := by exact prefixLift 6385706
  have htrace : WordTrace (prefixWord ++ tailWord_6385706) baseStart_6385706 baseEnd_6385706 := by
    simpa [prefixWord, tailWord_6385706, baseEnd_6385706] using wordTrace_append hprefix tailTrace_6385706
  have hstable : (prefixWord ++ tailWord_6385706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385706).length < 2 ^ (prefixWord ++ tailWord_6385706).sum := by decide
  have hdescent : baseEnd_6385706 < baseStart_6385706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385726 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6385726 : Nat := 118140960795 + 6385726 * 2 ^ 59
def prefixEnd_6385726 : Nat := 4983230072969 + 3 ^ 40 * 6385726 * 2
def baseEnd_6385726 : Nat := 3278946765912788051357587

theorem tailTrace_6385726 : CollatzResearch.WordTrace tailWord_6385726 prefixEnd_6385726 3278946765912788051357587 := by
  unfold tailWord_6385726
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113320157951596502399129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155271040842408514679462021 29113320157951596502399129)
  ·
    refine ⟨21834990118463697376799347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29113320157951596502399129 21834990118463697376799347)
    ·
      refine ⟨32752485177695546065199021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21834990118463697376799347 32752485177695546065199021)
      ·
        refine ⟨12282181941635829774449633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32752485177695546065199021 12282181941635829774449633)
        ·
          refine ⟨9211636456226872330837225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12282181941635829774449633 9211636456226872330837225)
          ·
            refine ⟨6908727342170154248127919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9211636456226872330837225 6908727342170154248127919)
            ·
              refine ⟨10363091013255231372191879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908727342170154248127919 10363091013255231372191879)
              ·
                refine ⟨15544636519882847058287819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363091013255231372191879 15544636519882847058287819)
                ·
                  refine ⟨23316954779824270587431729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15544636519882847058287819 23316954779824270587431729)
                  ·
                    refine ⟨17487716084868202940573797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23316954779824270587431729 17487716084868202940573797)
                    ·
                      refine ⟨3278946765912788051357587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17487716084868202940573797 3278946765912788051357587)
                      ·
                        rfl

theorem cell23_6385726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6385726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385726 prefixEnd_6385726 := by exact prefixLift 6385726
  have htrace : WordTrace (prefixWord ++ tailWord_6385726) baseStart_6385726 baseEnd_6385726 := by
    simpa [prefixWord, tailWord_6385726, baseEnd_6385726] using wordTrace_append hprefix tailTrace_6385726
  have hstable : (prefixWord ++ tailWord_6385726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385726).length < 2 ^ (prefixWord ++ tailWord_6385726).sum := by decide
  have hdescent : baseEnd_6385726 < baseStart_6385726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385729 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6385729 : Nat := 118140960795 + 6385729 * 2 ^ 59
def prefixEnd_6385729 : Nat := 4983230072969 + 3 ^ 40 * 6385729 * 2
def baseEnd_6385729 : Nat := 3278948306354751539620073

theorem tailTrace_6385729 : CollatzResearch.WordTrace tailWord_6385729 prefixEnd_6385729 3278948306354751539620073 := by
  unfold tailWord_6385729
  simp only [CollatzResearch.WordTrace]
  refine ⟨232906670682601903531552241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155271113788401269021034827 232906670682601903531552241)
  ·
    refine ⟨174680003011951427648664181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232906670682601903531552241 174680003011951427648664181)
    ·
      refine ⟨16376250282370446342062267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174680003011951427648664181 16376250282370446342062267)
      ·
        refine ⟨24564375423555669513093401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376250282370446342062267 24564375423555669513093401)
        ·
          refine ⟨18423281567666752134820051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24564375423555669513093401 18423281567666752134820051)
          ·
            refine ⟨27634922351500128202230077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18423281567666752134820051 27634922351500128202230077)
            ·
              refine ⟨10363095881812548075836279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27634922351500128202230077 10363095881812548075836279)
              ·
                refine ⟨15544643822718822113754419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363095881812548075836279 15544643822718822113754419)
                ·
                  refine ⟨23316965734078233170631629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15544643822718822113754419 23316965734078233170631629)
                  ·
                    refine ⟨8743862150279337438986861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23316965734078233170631629 8743862150279337438986861)
                    ·
                      refine ⟨3278948306354751539620073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743862150279337438986861 3278948306354751539620073)
                      ·
                        rfl

theorem cell23_6385729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6385729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385729 prefixEnd_6385729 := by exact prefixLift 6385729
  have htrace : WordTrace (prefixWord ++ tailWord_6385729) baseStart_6385729 baseEnd_6385729 := by
    simpa [prefixWord, tailWord_6385729, baseEnd_6385729] using wordTrace_append hprefix tailTrace_6385729
  have hstable : (prefixWord ++ tailWord_6385729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385729).length < 2 ^ (prefixWord ++ tailWord_6385729).sum := by decide
  have hdescent : baseEnd_6385729 < baseStart_6385729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385756 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_6385756 : Nat := 118140960795 + 6385756 * 2 ^ 59
def prefixEnd_6385756 : Nat := 4983230072969 + 3 ^ 40 * 6385756 * 2
def baseEnd_6385756 : Nat := 3278962170332422933982449

theorem tailTrace_6385756 : CollatzResearch.WordTrace tailWord_6385756 prefixEnd_6385756 3278962170332422933982449 := by
  unfold tailWord_6385756
  simp only [CollatzResearch.WordTrace]
  refine ⟨116453827726752043571392561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155271770302336058095190081 116453827726752043571392561)
  ·
    refine ⟨87340370795064032678544421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116453827726752043571392561 87340370795064032678544421)
    ·
      refine ⟨16376319524074506127227079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87340370795064032678544421 16376319524074506127227079)
      ·
        refine ⟨24564479286111759190840619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376319524074506127227079 24564479286111759190840619)
        ·
          refine ⟨36846718929167638786260929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24564479286111759190840619 36846718929167638786260929)
          ·
            refine ⟨27635039196875729089695697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36846718929167638786260929 27635039196875729089695697)
            ·
              refine ⟨20726279397656796817271773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27635039196875729089695697 20726279397656796817271773)
              ·
                refine ⟨7772354774121298806476915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20726279397656796817271773 7772354774121298806476915)
                ·
                  refine ⟨11658532161181948209715373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7772354774121298806476915 11658532161181948209715373)
                  ·
                    refine ⟨4371949560443230578643265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11658532161181948209715373 4371949560443230578643265)
                    ·
                      refine ⟨3278962170332422933982449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371949560443230578643265 3278962170332422933982449)
                      ·
                        rfl

theorem cell23_6385756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_6385756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385756 prefixEnd_6385756 := by exact prefixLift 6385756
  have htrace : WordTrace (prefixWord ++ tailWord_6385756) baseStart_6385756 baseEnd_6385756 := by
    simpa [prefixWord, tailWord_6385756, baseEnd_6385756] using wordTrace_append hprefix tailTrace_6385756
  have hstable : (prefixWord ++ tailWord_6385756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385756).length < 2 ^ (prefixWord ++ tailWord_6385756).sum := by decide
  have hdescent : baseEnd_6385756 < baseStart_6385756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385769 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 4, 2, 2]
def baseStart_6385769 : Nat := 118140960795 + 6385769 * 2 ^ 59
def prefixEnd_6385769 : Nat := 4983230072969 + 3 ^ 40 * 6385769 * 2
def baseEnd_6385769 : Nat := 3278968845580931383119889

theorem tailTrace_6385769 : CollatzResearch.WordTrace tailWord_6385769 prefixEnd_6385769 3278968845580931383119889 := by
  unfold tailWord_6385769
  simp only [CollatzResearch.WordTrace]
  refine ⟨232908129602456990363008361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155272086401637993575338907 232908129602456990363008361)
  ·
    refine ⟨174681097201842742772256271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232908129602456990363008361 174681097201842742772256271)
    ·
      refine ⟨262021645802764114158384407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174681097201842742772256271 262021645802764114158384407)
      ·
        refine ⟨393032468704146171237576611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262021645802764114158384407 393032468704146171237576611)
        ·
          refine ⟨589548703056219256856364917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393032468704146171237576611 589548703056219256856364917)
          ·
            refine ⟨55270190911520555330284211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 589548703056219256856364917 55270190911520555330284211)
            ·
              refine ⟨82905286367280832995426317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55270190911520555330284211 82905286367280832995426317)
              ·
                refine ⟨31089482387730312373284869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82905286367280832995426317 31089482387730312373284869)
                ·
                  refine ⟨5829277947699433569990913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31089482387730312373284869 5829277947699433569990913)
                  ·
                    refine ⟨4371958460774575177493185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5829277947699433569990913 4371958460774575177493185)
                    ·
                      refine ⟨3278968845580931383119889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4371958460774575177493185 3278968845580931383119889)
                      ·
                        rfl

theorem cell23_6385769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 2, 2].length) (baseStart_6385769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385769 prefixEnd_6385769 := by exact prefixLift 6385769
  have htrace : WordTrace (prefixWord ++ tailWord_6385769) baseStart_6385769 baseEnd_6385769 := by
    simpa [prefixWord, tailWord_6385769, baseEnd_6385769] using wordTrace_append hprefix tailTrace_6385769
  have hstable : (prefixWord ++ tailWord_6385769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385769).length < 2 ^ (prefixWord ++ tailWord_6385769).sum := by decide
  have hdescent : baseEnd_6385769 < baseStart_6385769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385814 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6385814 : Nat := 118140960795 + 6385814 * 2 ^ 59
def prefixEnd_6385814 : Nat := 4983230072969 + 3 ^ 40 * 6385814 * 2
def baseEnd_6385814 : Nat := 3278991952210383707057183

theorem tailTrace_6385814 : CollatzResearch.WordTrace tailWord_6385814 prefixEnd_6385814 3278991952210383707057183 := by
  unfold tailWord_6385814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14556860680455872690524781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155273180591529308698930997 14556860680455872690524781)
  ·
    refine ⟨5458822755170952258946793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14556860680455872690524781 5458822755170952258946793)
    ·
      refine ⟨4094117066378214194210095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5458822755170952258946793 4094117066378214194210095)
      ·
        refine ⟨6141175599567321291315143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094117066378214194210095 6141175599567321291315143)
        ·
          refine ⟨9211763399350981936972715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141175599567321291315143 9211763399350981936972715)
          ·
            refine ⟨13817645099026472905459073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9211763399350981936972715 13817645099026472905459073)
            ·
              refine ⟨10363233824269854679094305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13817645099026472905459073 10363233824269854679094305)
              ·
                refine ⟨7772425368202391009320729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10363233824269854679094305 7772425368202391009320729)
                ·
                  refine ⟨5829319026151793256990547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7772425368202391009320729 5829319026151793256990547)
                  ·
                    refine ⟨8743978539227689885485821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5829319026151793256990547 8743978539227689885485821)
                    ·
                      refine ⟨3278991952210383707057183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8743978539227689885485821 3278991952210383707057183)
                      ·
                        rfl

theorem cell23_6385814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6385814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385814 prefixEnd_6385814 := by exact prefixLift 6385814
  have htrace : WordTrace (prefixWord ++ tailWord_6385814) baseStart_6385814 baseEnd_6385814 := by
    simpa [prefixWord, tailWord_6385814, baseEnd_6385814] using wordTrace_append hprefix tailTrace_6385814
  have hstable : (prefixWord ++ tailWord_6385814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385814).length < 2 ^ (prefixWord ++ tailWord_6385814).sum := by decide
  have hdescent : baseEnd_6385814 < baseStart_6385814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385826 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_6385826 : Nat := 118140960795 + 6385826 * 2 ^ 59
def prefixEnd_6385826 : Nat := 4983230072969 + 3 ^ 40 * 6385826 * 2
def baseEnd_6385826 : Nat := 364333123775359740011903

theorem tailTrace_6385826 : CollatzResearch.WordTrace tailWord_6385826 prefixEnd_6385826 364333123775359740011903 := by
  unfold tailWord_6385826
  simp only [CollatzResearch.WordTrace]
  refine ⟨58227552140812622274458333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155273472375500326065222221 58227552140812622274458333)
  ·
    refine ⟨21835332052804733352921875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58227552140812622274458333 21835332052804733352921875)
    ·
      refine ⟨32752998079207100029382813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21835332052804733352921875 32752998079207100029382813)
      ·
        refine ⟨12282374279702662511018555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32752998079207100029382813 12282374279702662511018555)
        ·
          refine ⟨18423561419553993766527833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12282374279702662511018555 18423561419553993766527833)
          ·
            refine ⟨13817671064665495324895875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18423561419553993766527833 13817671064665495324895875)
            ·
              refine ⟨20726506596998242987343813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13817671064665495324895875 20726506596998242987343813)
              ·
                refine ⟨3886219986937170560126965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20726506596998242987343813 3886219986937170560126965)
                ·
                  refine ⟨364333123775359740011903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3886219986937170560126965 364333123775359740011903)
                  ·
                    rfl

theorem cell23_6385826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_6385826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385826 prefixEnd_6385826 := by exact prefixLift 6385826
  have htrace : WordTrace (prefixWord ++ tailWord_6385826) baseStart_6385826 baseEnd_6385826 := by
    simpa [prefixWord, tailWord_6385826, baseEnd_6385826] using wordTrace_append hprefix tailTrace_6385826
  have hstable : (prefixWord ++ tailWord_6385826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385826).length < 2 ^ (prefixWord ++ tailWord_6385826).sum := by decide
  have hdescent : baseEnd_6385826 < baseStart_6385826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385842 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6385842 : Nat := 118140960795 + 6385842 * 2 ^ 59
def prefixEnd_6385842 : Nat := 4983230072969 + 3 ^ 40 * 6385842 * 2
def baseEnd_6385842 : Nat := 3279006329668709597507053

theorem tailTrace_6385842 : CollatzResearch.WordTrace tailWord_6385842 prefixEnd_6385842 3279006329668709597507053 := by
  unfold tailWord_6385842
  simp only [CollatzResearch.WordTrace]
  refine ⟨58227698032798130957603945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155273861420795015886943853 58227698032798130957603945)
  ·
    refine ⟨43670773524598598218202959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58227698032798130957603945 43670773524598598218202959)
    ·
      refine ⟨65506160286897897327304439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43670773524598598218202959 65506160286897897327304439)
      ·
        refine ⟨98259240430346845990956659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65506160286897897327304439 98259240430346845990956659)
        ·
          refine ⟨147388860645520268986434989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98259240430346845990956659 147388860645520268986434989)
          ·
            refine ⟨55270822742070100869913121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147388860645520268986434989 55270822742070100869913121)
            ·
              refine ⟨41453117056552575652434841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55270822742070100869913121 41453117056552575652434841)
              ·
                refine ⟨31089837792414431739326131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41453117056552575652434841 31089837792414431739326131)
                ·
                  refine ⟨46634756688621647608989197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31089837792414431739326131 46634756688621647608989197)
                  ·
                    refine ⟨17488033758233117853370949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46634756688621647608989197 17488033758233117853370949)
                    ·
                      refine ⟨3279006329668709597507053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17488033758233117853370949 3279006329668709597507053)
                      ·
                        rfl

theorem cell23_6385842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6385842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385842 prefixEnd_6385842 := by exact prefixLift 6385842
  have htrace : WordTrace (prefixWord ++ tailWord_6385842) baseStart_6385842 baseEnd_6385842 := by
    simpa [prefixWord, tailWord_6385842, baseEnd_6385842] using wordTrace_append hprefix tailTrace_6385842
  have hstable : (prefixWord ++ tailWord_6385842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385842).length < 2 ^ (prefixWord ++ tailWord_6385842).sum := by decide
  have hdescent : baseEnd_6385842 < baseStart_6385842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385899 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 6]
def baseStart_6385899 : Nat := 118140960795 + 6385899 * 2 ^ 59
def prefixEnd_6385899 : Nat := 4983230072969 + 3 ^ 40 * 6385899 * 2
def baseEnd_6385899 : Nat := 364337288674001763832699

theorem tailTrace_6385899 : CollatzResearch.WordTrace tailWord_6385899 prefixEnd_6385899 364337288674001763832699 := by
  unfold tailWord_6385899
  simp only [CollatzResearch.WordTrace]
  refine ⟨232912871091986022565240751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155275247394657348376827167 232912871091986022565240751)
  ·
    refine ⟨349369306637979033847861127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232912871091986022565240751 349369306637979033847861127)
    ·
      refine ⟨524053959956968550771791691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349369306637979033847861127 524053959956968550771791691)
      ·
        refine ⟨786080939935452826157687537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524053959956968550771791691 786080939935452826157687537)
        ·
          refine ⟨589560704951589619618265653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786080939935452826157687537 589560704951589619618265653)
          ·
            refine ⟨55271316089211526839212405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 589560704951589619618265653 55271316089211526839212405)
            ·
              refine ⟨5181685883363580641176163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55271316089211526839212405 5181685883363580641176163)
              ·
                refine ⟨7772528825045370961764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181685883363580641176163 7772528825045370961764245)
                ·
                  refine ⟨364337288674001763832699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772528825045370961764245 364337288674001763832699)
                  ·
                    rfl

theorem cell23_6385899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 6].length) (baseStart_6385899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385899 prefixEnd_6385899 := by exact prefixLift 6385899
  have htrace : WordTrace (prefixWord ++ tailWord_6385899) baseStart_6385899 baseEnd_6385899 := by
    simpa [prefixWord, tailWord_6385899, baseEnd_6385899] using wordTrace_append hprefix tailTrace_6385899
  have hstable : (prefixWord ++ tailWord_6385899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385899).length < 2 ^ (prefixWord ++ tailWord_6385899).sum := by decide
  have hdescent : baseEnd_6385899 < baseStart_6385899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385902 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6385902 : Nat := 118140960795 + 6385902 * 2 ^ 59
def prefixEnd_6385902 : Nat := 4983230072969 + 3 ^ 40 * 6385902 * 2
def baseEnd_6385902 : Nat := 3279037138507979362756777

theorem tailTrace_6385902 : CollatzResearch.WordTrace tailWord_6385902 prefixEnd_6385902 3279037138507979362756777 := by
  unfold tailWord_6385902
  simp only [CollatzResearch.WordTrace]
  refine ⟨29114122563871894259699995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155275320340650102718399973 29114122563871894259699995)
  ·
    refine ⟨43671183845807841389549993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29114122563871894259699995 43671183845807841389549993)
    ·
      refine ⟨32753387884355881042162495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43671183845807841389549993 32753387884355881042162495)
      ·
        refine ⟨49130081826533821563243743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32753387884355881042162495 49130081826533821563243743)
        ·
          refine ⟨73695122739800732344865615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49130081826533821563243743 73695122739800732344865615)
          ·
            refine ⟨110542684109701098517298423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73695122739800732344865615 110542684109701098517298423)
            ·
              refine ⟨165814026164551647775947635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110542684109701098517298423 165814026164551647775947635)
              ·
                refine ⟨248721039246827471663921453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165814026164551647775947635 248721039246827471663921453)
                ·
                  refine ⟨93270389717560301873970545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248721039246827471663921453 93270389717560301873970545)
                  ·
                    refine ⟨69952792288170226405477909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93270389717560301873970545 69952792288170226405477909)
                    ·
                      refine ⟨3279037138507979362756777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69952792288170226405477909 3279037138507979362756777)
                      ·
                        rfl

theorem cell23_6385902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6385902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385902 prefixEnd_6385902 := by exact prefixLift 6385902
  have htrace : WordTrace (prefixWord ++ tailWord_6385902) baseStart_6385902 baseEnd_6385902 := by
    simpa [prefixWord, tailWord_6385902, baseEnd_6385902] using wordTrace_append hprefix tailTrace_6385902
  have hstable : (prefixWord ++ tailWord_6385902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385902).length < 2 ^ (prefixWord ++ tailWord_6385902).sum := by decide
  have hdescent : baseEnd_6385902 < baseStart_6385902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385912 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_6385912 : Nat := 118140960795 + 6385912 * 2 ^ 59
def prefixEnd_6385912 : Nat := 4983230072969 + 3 ^ 40 * 6385912 * 2
def baseEnd_6385912 : Nat := 1093014091104841441210577

theorem tailTrace_6385912 : CollatzResearch.WordTrace tailWord_6385912 prefixEnd_6385912 1093014091104841441210577 := by
  unfold tailWord_6385912
  simp only [CollatzResearch.WordTrace]
  refine ⟨116456672620469462892731995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155275563493959283856975993 116456672620469462892731995)
  ·
    refine ⟨174685008930704194339097993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116456672620469462892731995 174685008930704194339097993)
    ·
      refine ⟨131013756698028145754323495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174685008930704194339097993 131013756698028145754323495)
      ·
        refine ⟨196520635047042218631485243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131013756698028145754323495 196520635047042218631485243)
        ·
          refine ⟨294780952570563327947227865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196520635047042218631485243 294780952570563327947227865)
          ·
            refine ⟨221085714427922495960420899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294780952570563327947227865 221085714427922495960420899)
            ·
              refine ⟨331628571641883743940631349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221085714427922495960420899 331628571641883743940631349)
              ·
                refine ⟨31090178591426600994434189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 331628571641883743940631349 31090178591426600994434189)
                ·
                  refine ⟨11658816971784975372912821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31090178591426600994434189 11658816971784975372912821)
                  ·
                    refine ⟨1093014091104841441210577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11658816971784975372912821 1093014091104841441210577)
                    ·
                      rfl

theorem cell23_6385912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_6385912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385912 prefixEnd_6385912 := by exact prefixLift 6385912
  have htrace : WordTrace (prefixWord ++ tailWord_6385912) baseStart_6385912 baseEnd_6385912 := by
    simpa [prefixWord, tailWord_6385912, baseEnd_6385912] using wordTrace_append hprefix tailTrace_6385912
  have hstable : (prefixWord ++ tailWord_6385912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385912).length < 2 ^ (prefixWord ++ tailWord_6385912).sum := by decide
  have hdescent : baseEnd_6385912 < baseStart_6385912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385919 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 1, 5, 2]
def baseStart_6385919 : Nat := 118140960795 + 6385919 * 2 ^ 59
def prefixEnd_6385919 : Nat := 4983230072969 + 3 ^ 40 * 6385919 * 2
def baseEnd_6385919 : Nat := 3279045867679105796244199

theorem tailTrace_6385919 : CollatzResearch.WordTrace tailWord_6385919 prefixEnd_6385919 3279045867679105796244199 := by
  unfold tailWord_6385919
  simp only [CollatzResearch.WordTrace]
  refine ⟨232913600551913565980968811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155275733701275710653979207 232913600551913565980968811)
  ·
    refine ⟨349370400827870348971453217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232913600551913565980968811 349370400827870348971453217)
    ·
      refine ⟨262027800620902761728589913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349370400827870348971453217 262027800620902761728589913)
      ·
        refine ⟨196520850465677071296442435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262027800620902761728589913 196520850465677071296442435)
        ·
          refine ⟨294781275698515606944663653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196520850465677071296442435 294781275698515606944663653)
          ·
            refine ⟨55271489193471676302124435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294781275698515606944663653 55271489193471676302124435)
            ·
              refine ⟨82907233790207514453186653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55271489193471676302124435 82907233790207514453186653)
              ·
                refine ⟨31090212671327817919944995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82907233790207514453186653 31090212671327817919944995)
                ·
                  refine ⟨46635319006991726879917493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31090212671327817919944995 46635319006991726879917493)
                  ·
                    refine ⟨4372061156905474394992265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46635319006991726879917493 4372061156905474394992265)
                    ·
                      refine ⟨3279045867679105796244199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372061156905474394992265 3279045867679105796244199)
                      ·
                        rfl

theorem cell23_6385919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_6385919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385919 prefixEnd_6385919 := by exact prefixLift 6385919
  have htrace : WordTrace (prefixWord ++ tailWord_6385919) baseStart_6385919 baseEnd_6385919 := by
    simpa [prefixWord, tailWord_6385919, baseEnd_6385919] using wordTrace_append hprefix tailTrace_6385919
  have hstable : (prefixWord ++ tailWord_6385919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385919).length < 2 ^ (prefixWord ++ tailWord_6385919).sum := by decide
  have hdescent : baseEnd_6385919 < baseStart_6385919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385929 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 1, 5]
def baseStart_6385929 : Nat := 118140960795 + 6385929 * 2 ^ 59
def prefixEnd_6385929 : Nat := 4983230072969 + 3 ^ 40 * 6385929 * 2
def baseEnd_6385929 : Nat := 1093017000828550252373051

theorem tailTrace_6385929 : CollatzResearch.WordTrace tailWord_6385929 prefixEnd_6385929 1093017000828550252373051 := by
  unfold tailWord_6385929
  simp only [CollatzResearch.WordTrace]
  refine ⟨232913965281877337688832841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155275976854584891792555227 232913965281877337688832841)
  ·
    refine ⟨174685473961408003266624631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232913965281877337688832841 174685473961408003266624631)
    ·
      refine ⟨262028210942112004899936947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174685473961408003266624631 262028210942112004899936947)
      ·
        refine ⟨393042316413168007349905421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262028210942112004899936947 393042316413168007349905421)
        ·
          refine ⟨147390868654938002756214533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393042316413168007349905421 147390868654938002756214533)
          ·
            refine ⟨27635787872800875516790225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147390868654938002756214533 27635787872800875516790225)
            ·
              refine ⟨20726840904600656637592669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27635787872800875516790225 20726840904600656637592669)
              ·
                refine ⟨7772565339225246239097251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20726840904600656637592669 7772565339225246239097251)
                ·
                  refine ⟨11658848008837869358645877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7772565339225246239097251 11658848008837869358645877)
                  ·
                    refine ⟨1093017000828550252373051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11658848008837869358645877 1093017000828550252373051)
                    ·
                      rfl

theorem cell23_6385929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_6385929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385929 prefixEnd_6385929 := by exact prefixLift 6385929
  have htrace : WordTrace (prefixWord ++ tailWord_6385929) baseStart_6385929 baseEnd_6385929 := by
    simpa [prefixWord, tailWord_6385929, baseEnd_6385929] using wordTrace_append hprefix tailTrace_6385929
  have hstable : (prefixWord ++ tailWord_6385929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385929).length < 2 ^ (prefixWord ++ tailWord_6385929).sum := by decide
  have hdescent : baseEnd_6385929 < baseStart_6385929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385943 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_6385943 : Nat := 118140960795 + 6385943 * 2 ^ 59
def prefixEnd_6385943 : Nat := 4983230072969 + 3 ^ 40 * 6385943 * 2
def baseEnd_6385943 : Nat := 3279058191214813702344089

theorem tailTrace_6385943 : CollatzResearch.WordTrace tailWord_6385943 prefixEnd_6385943 3279058191214813702344089 := by
  unfold tailWord_6385943
  simp only [CollatzResearch.WordTrace]
  refine ⟨232914475903826618079842483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155276317269217745386561655 232914475903826618079842483)
  ·
    refine ⟨349371713855739927119763725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232914475903826618079842483 349371713855739927119763725)
    ·
      refine ⟨131014392695902472669911397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349371713855739927119763725 131014392695902472669911397)
      ·
        refine ⟨24565198630481713625608387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131014392695902472669911397 24565198630481713625608387)
        ·
          refine ⟨36847797945722570438412581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24565198630481713625608387 36847797945722570438412581)
          ·
            refine ⟨6908962114822981957202359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36847797945722570438412581 6908962114822981957202359)
            ·
              refine ⟨10363443172234472935803539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6908962114822981957202359 10363443172234472935803539)
              ·
                refine ⟨15545164758351709403705309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363443172234472935803539 15545164758351709403705309)
                ·
                  refine ⟨5829436784381891026389491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15545164758351709403705309 5829436784381891026389491)
                  ·
                    refine ⟨8744155176572836539584237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5829436784381891026389491 8744155176572836539584237)
                    ·
                      refine ⟨3279058191214813702344089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8744155176572836539584237 3279058191214813702344089)
                      ·
                        rfl

theorem cell23_6385943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_6385943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385943 prefixEnd_6385943 := by exact prefixLift 6385943
  have htrace : WordTrace (prefixWord ++ tailWord_6385943) baseStart_6385943 baseEnd_6385943 := by
    simpa [prefixWord, tailWord_6385943, baseEnd_6385943] using wordTrace_append hprefix tailTrace_6385943
  have hstable : (prefixWord ++ tailWord_6385943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385943).length < 2 ^ (prefixWord ++ tailWord_6385943).sum := by decide
  have hdescent : baseEnd_6385943 < baseStart_6385943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385950 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_6385950 : Nat := 118140960795 + 6385950 * 2 ^ 59
def prefixEnd_6385950 : Nat := 4983230072969 + 3 ^ 40 * 6385950 * 2
def baseEnd_6385950 : Nat := 364340198397710574995173

theorem tailTrace_6385950 : CollatzResearch.WordTrace tailWord_6385950 prefixEnd_6385950 364340198397710574995173 := by
  unfold tailWord_6385950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29114341401850157284418413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155276487476534172183564869 29114341401850157284418413)
  ·
    refine ⟨10917878025693808981656905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29114341401850157284418413 10917878025693808981656905)
    ·
      refine ⟨8188408519270356736242679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10917878025693808981656905 8188408519270356736242679)
      ·
        refine ⟨12282612778905535104364019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8188408519270356736242679 12282612778905535104364019)
        ·
          refine ⟨18423919168358302656546029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12282612778905535104364019 18423919168358302656546029)
          ·
            refine ⟨6908969688134363496204761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18423919168358302656546029 6908969688134363496204761)
            ·
              refine ⟨5181727266100772622153571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6908969688134363496204761 5181727266100772622153571)
              ·
                refine ⟨7772590899151158933230357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181727266100772622153571 7772590899151158933230357)
                ·
                  refine ⟨364340198397710574995173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772590899151158933230357 364340198397710574995173)
                  ·
                    rfl

theorem cell23_6385950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_6385950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6385950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6385950 prefixEnd_6385950 := by exact prefixLift 6385950
  have htrace : WordTrace (prefixWord ++ tailWord_6385950) baseStart_6385950 baseEnd_6385950 := by
    simpa [prefixWord, tailWord_6385950, baseEnd_6385950] using wordTrace_append hprefix tailTrace_6385950
  have hstable : (prefixWord ++ tailWord_6385950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385950).length < 2 ^ (prefixWord ++ tailWord_6385950).sum := by decide
  have hdescent : baseEnd_6385950 < baseStart_6385950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386000 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 1, 2, 2]
def baseStart_6386000 : Nat := 118140960795 + 6386000 * 2 ^ 59
def prefixEnd_6386000 : Nat := 4983230072969 + 3 ^ 40 * 6386000 * 2
def baseEnd_6386000 : Nat := 3279087459612119979331327

theorem tailTrace_6386000 : CollatzResearch.WordTrace tailWord_6386000 prefixEnd_6386000 3279087459612119979331327 := by
  unfold tailWord_6386000
  simp only [CollatzResearch.WordTrace]
  refine ⟨116458277432310058407333727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155277703243080077876444969 116458277432310058407333727)
  ·
    refine ⟨174687416148465087611000591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116458277432310058407333727 174687416148465087611000591)
    ·
      refine ⟨262031124222697631416500887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174687416148465087611000591 262031124222697631416500887)
      ·
        refine ⟨393046686334046447124751331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262031124222697631416500887 393046686334046447124751331)
        ·
          refine ⟨589570029501069670687126997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393046686334046447124751331 589570029501069670687126997)
          ·
            refine ⟨13818047566431320406729539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 589570029501069670687126997 13818047566431320406729539)
            ·
              refine ⟨20727071349646980610094309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818047566431320406729539 20727071349646980610094309)
              ·
                refine ⟨3886325878058808864392683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20727071349646980610094309 3886325878058808864392683)
                ·
                  refine ⟨5829488817088213296589025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886325878058808864392683 5829488817088213296589025)
                  ·
                    refine ⟨4372116612816159972441769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5829488817088213296589025 4372116612816159972441769)
                    ·
                      refine ⟨3279087459612119979331327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372116612816159972441769 3279087459612119979331327)
                      ·
                        rfl

theorem cell23_6386000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 2, 2].length) (baseStart_6386000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386000 prefixEnd_6386000 := by exact prefixLift 6386000
  have htrace : WordTrace (prefixWord ++ tailWord_6386000) baseStart_6386000 baseEnd_6386000 := by
    simpa [prefixWord, tailWord_6386000, baseEnd_6386000] using wordTrace_append hprefix tailTrace_6386000
  have hstable : (prefixWord ++ tailWord_6386000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386000).length < 2 ^ (prefixWord ++ tailWord_6386000).sum := by decide
  have hdescent : baseEnd_6386000 < baseStart_6386000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386029 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6386029 : Nat := 118140960795 + 6386029 * 2 ^ 59
def prefixEnd_6386029 : Nat := 4983230072969 + 3 ^ 40 * 6386029 * 2
def baseEnd_6386029 : Nat := 3279102350551100365868693

theorem tailTrace_6386029 : CollatzResearch.WordTrace tailWord_6386029 prefixEnd_6386029 3279102350551100365868693 := by
  unfold tailWord_6386029
  simp only [CollatzResearch.WordTrace]
  refine ⟨232917612581515054767473141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155278408387676703178315427 232917612581515054767473141)
  ·
    refine ⟨21836026179517036384450607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232917612581515054767473141 21836026179517036384450607)
    ·
      refine ⟨32754039269275554576675911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21836026179517036384450607 32754039269275554576675911)
      ·
        refine ⟨49131058903913331865013867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32754039269275554576675911 49131058903913331865013867)
        ·
          refine ⟨73696588355869997797520801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49131058903913331865013867 73696588355869997797520801)
          ·
            refine ⟨55272441266902498348140601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73696588355869997797520801 55272441266902498348140601)
            ·
              refine ⟨41454330950176873761105451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55272441266902498348140601 41454330950176873761105451)
              ·
                refine ⟨62181496425265310641658177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41454330950176873761105451 62181496425265310641658177)
                ·
                  refine ⟨46636122318948982981243633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62181496425265310641658177 46636122318948982981243633)
                  ·
                    refine ⟨34977091739211737235932725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46636122318948982981243633 34977091739211737235932725)
                    ·
                      refine ⟨3279102350551100365868693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34977091739211737235932725 3279102350551100365868693)
                      ·
                        rfl

theorem cell23_6386029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6386029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386029 prefixEnd_6386029 := by exact prefixLift 6386029
  have htrace : WordTrace (prefixWord ++ tailWord_6386029) baseStart_6386029 baseEnd_6386029 := by
    simpa [prefixWord, tailWord_6386029, baseEnd_6386029] using wordTrace_append hprefix tailTrace_6386029
  have hstable : (prefixWord ++ tailWord_6386029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386029).length < 2 ^ (prefixWord ++ tailWord_6386029).sum := by decide
  have hdescent : baseEnd_6386029 < baseStart_6386029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386043 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 1, 3, 2]
def baseStart_6386043 : Nat := 118140960795 + 6386043 * 2 ^ 59
def prefixEnd_6386043 : Nat := 4983230072969 + 3 ^ 40 * 6386043 * 2
def baseEnd_6386043 : Nat := 3279109539280263311093629

theorem tailTrace_6386043 : CollatzResearch.WordTrace tailWord_6386043 prefixEnd_6386043 3279109539280263311093629 := by
  unfold tailWord_6386043
  simp only [CollatzResearch.WordTrace]
  refine ⟨232918123203464335158482783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155278748802309556772321855 232918123203464335158482783)
  ·
    refine ⟨349377184805196502737724175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232918123203464335158482783 349377184805196502737724175)
    ·
      refine ⟨524065777207794754106586263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349377184805196502737724175 524065777207794754106586263)
      ·
        refine ⟨786098665811692131159879395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524065777207794754106586263 786098665811692131159879395)
        ·
          refine ⟨1179147998717538196739819093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786098665811692131159879395 1179147998717538196739819093)
          ·
            refine ⟨13818140609971150743044755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1179147998717538196739819093 13818140609971150743044755)
            ·
              refine ⟨20727210914956726114567133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818140609971150743044755 20727210914956726114567133)
              ·
                refine ⟨7772704093108772292962675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20727210914956726114567133 7772704093108772292962675)
                ·
                  refine ⟨11659056139663158439444013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7772704093108772292962675 11659056139663158439444013)
                  ·
                    refine ⟨4372146052373684414791505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11659056139663158439444013 4372146052373684414791505)
                    ·
                      refine ⟨3279109539280263311093629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372146052373684414791505 3279109539280263311093629)
                      ·
                        rfl

theorem cell23_6386043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 3, 2].length) (baseStart_6386043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386043 prefixEnd_6386043 := by exact prefixLift 6386043
  have htrace : WordTrace (prefixWord ++ tailWord_6386043) baseStart_6386043 baseEnd_6386043 := by
    simpa [prefixWord, tailWord_6386043, baseEnd_6386043] using wordTrace_append hprefix tailTrace_6386043
  have hstable : (prefixWord ++ tailWord_6386043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386043).length < 2 ^ (prefixWord ++ tailWord_6386043).sum := by decide
  have hdescent : baseEnd_6386043 < baseStart_6386043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386079 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 7]
def baseStart_6386079 : Nat := 118140960795 + 6386079 * 2 ^ 59
def prefixEnd_6386079 : Nat := 4983230072969 + 3 ^ 40 * 6386079 * 2
def baseEnd_6386079 : Nat := 364347558287091685582607

theorem tailTrace_6386079 : CollatzResearch.WordTrace tailWord_6386079 prefixEnd_6386079 364347558287091685582607 := by
  unfold tailWord_6386079
  simp only [CollatzResearch.WordTrace]
  refine ⟨232919436231333913306793291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155279624154222608871195527 232919436231333913306793291)
  ·
    refine ⟨349379154347000869960189937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232919436231333913306793291 349379154347000869960189937)
    ·
      refine ⟨262034365760250652470142453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349379154347000869960189937 262034365760250652470142453)
      ·
        refine ⟨24565721790023498669075855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262034365760250652470142453 24565721790023498669075855)
        ·
          refine ⟨36848582685035248003613783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24565721790023498669075855 36848582685035248003613783)
          ·
            refine ⟨55272874027552872005420675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36848582685035248003613783 55272874027552872005420675)
            ·
              refine ⟨82909311041329308008131013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55272874027552872005420675 82909311041329308008131013)
              ·
                refine ⟨15545495820249245251524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82909311041329308008131013 15545495820249245251524565)
                ·
                  refine ⟨364347558287091685582607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15545495820249245251524565 364347558287091685582607)
                  ·
                    rfl

theorem cell23_6386079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 7].length) (baseStart_6386079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386079 prefixEnd_6386079 := by exact prefixLift 6386079
  have htrace : WordTrace (prefixWord ++ tailWord_6386079) baseStart_6386079 baseEnd_6386079 := by
    simpa [prefixWord, tailWord_6386079, baseEnd_6386079] using wordTrace_append hprefix tailTrace_6386079
  have hstable : (prefixWord ++ tailWord_6386079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386079).length < 2 ^ (prefixWord ++ tailWord_6386079).sum := by decide
  have hdescent : baseEnd_6386079 < baseStart_6386079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386089 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_6386089 : Nat := 118140960795 + 6386089 * 2 ^ 59
def prefixEnd_6386089 : Nat := 4983230072969 + 3 ^ 40 * 6386089 * 2
def baseEnd_6386089 : Nat := 3279133159390370131118417

theorem tailTrace_6386089 : CollatzResearch.WordTrace tailWord_6386089 prefixEnd_6386089 3279133159390370131118417 := by
  unfold tailWord_6386089
  simp only [CollatzResearch.WordTrace]
  refine ⟨232919800961297685014657321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155279867307531790009771547 232919800961297685014657321)
  ·
    refine ⟨174689850720973263760992991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232919800961297685014657321 174689850720973263760992991)
    ·
      refine ⟨262034776081459895641489487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174689850720973263760992991 262034776081459895641489487)
      ·
        refine ⟨393052164122189843462234231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262034776081459895641489487 393052164122189843462234231)
        ·
          refine ⟨589578246183284765193351347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393052164122189843462234231 589578246183284765193351347)
          ·
            refine ⟨884367369274927147790027021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589578246183284765193351347 884367369274927147790027021)
            ·
              refine ⟨331637763478097680421260133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884367369274927147790027021 331637763478097680421260133)
              ·
                refine ⟨62182080652143315078986275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331637763478097680421260133 62182080652143315078986275)
                ·
                  refine ⟨93273120978214972618479413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62182080652143315078986275 93273120978214972618479413)
                  ·
                    refine ⟨8744355091707653682982445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93273120978214972618479413 8744355091707653682982445)
                    ·
                      refine ⟨3279133159390370131118417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8744355091707653682982445 3279133159390370131118417)
                      ·
                        rfl

theorem cell23_6386089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_6386089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386089 prefixEnd_6386089 := by exact prefixLift 6386089
  have htrace : WordTrace (prefixWord ++ tailWord_6386089) baseStart_6386089 baseEnd_6386089 := by
    simpa [prefixWord, tailWord_6386089, baseEnd_6386089] using wordTrace_append hprefix tailTrace_6386089
  have hstable : (prefixWord ++ tailWord_6386089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386089).length < 2 ^ (prefixWord ++ tailWord_6386089).sum := by decide
  have hdescent : baseEnd_6386089 < baseStart_6386089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386093 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6386093 : Nat := 118140960795 + 6386093 * 2 ^ 59
def prefixEnd_6386093 : Nat := 4983230072969 + 3 ^ 40 * 6386093 * 2
def baseEnd_6386093 : Nat := 3279135213312988115468399

theorem tailTrace_6386093 : CollatzResearch.WordTrace tailWord_6386093 prefixEnd_6386093 3279135213312988115468399 := by
  unfold tailWord_6386093
  simp only [CollatzResearch.WordTrace]
  refine ⟨232919946853283193697802933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155279964568855462465201955 232919946853283193697802933)
  ·
    refine ⟨21836245017495299409169025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232919946853283193697802933 21836245017495299409169025)
    ·
      refine ⟨16377183763121474556876769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21836245017495299409169025 16377183763121474556876769)
      ·
        refine ⟨12282887822341105917657577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16377183763121474556876769 12282887822341105917657577)
        ·
          refine ⟨9212165866755829438243183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12282887822341105917657577 9212165866755829438243183)
          ·
            refine ⟨13818248800133744157364775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212165866755829438243183 13818248800133744157364775)
            ·
              refine ⟨20727373200200616236047163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818248800133744157364775 20727373200200616236047163)
              ·
                refine ⟨31091059800300924354070745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20727373200200616236047163 31091059800300924354070745)
                ·
                  refine ⟨23318294850225693265553059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31091059800300924354070745 23318294850225693265553059)
                  ·
                    refine ⟨34977442275338539898329589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23318294850225693265553059 34977442275338539898329589)
                    ·
                      refine ⟨3279135213312988115468399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34977442275338539898329589 3279135213312988115468399)
                      ·
                        rfl

theorem cell23_6386093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6386093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386093 prefixEnd_6386093 := by exact prefixLift 6386093
  have htrace : WordTrace (prefixWord ++ tailWord_6386093) baseStart_6386093 baseEnd_6386093 := by
    simpa [prefixWord, tailWord_6386093, baseEnd_6386093] using wordTrace_append hprefix tailTrace_6386093
  have hstable : (prefixWord ++ tailWord_6386093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386093).length < 2 ^ (prefixWord ++ tailWord_6386093).sum := by decide
  have hdescent : baseEnd_6386093 < baseStart_6386093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386119 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_6386119 : Nat := 118140960795 + 6386119 * 2 ^ 59
def prefixEnd_6386119 : Nat := 4983230072969 + 3 ^ 40 * 6386119 * 2
def baseEnd_6386119 : Nat := 3279148563810005013743279

theorem tailTrace_6386119 : CollatzResearch.WordTrace tailWord_6386119 prefixEnd_6386119 3279148563810005013743279 := by
  unfold tailWord_6386119
  simp only [CollatzResearch.WordTrace]
  refine ⟨232920895151189000138249411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155280596767459333425499607 232920895151189000138249411)
  ·
    refine ⟨349381342726783500207374117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232920895151189000138249411 349381342726783500207374117)
    ·
      refine ⟨65509001761271906288882647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349381342726783500207374117 65509001761271906288882647)
      ·
        refine ⟨98263502641907859433323971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65509001761271906288882647 98263502641907859433323971)
        ·
          refine ⟨147395253962861789149985957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98263502641907859433323971 147395253962861789149985957)
          ·
            refine ⟨27636610118036585465622367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147395253962861789149985957 27636610118036585465622367)
            ·
              refine ⟨41454915177054878198433551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27636610118036585465622367 41454915177054878198433551)
              ·
                refine ⟨62182372765582317297650327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41454915177054878198433551 62182372765582317297650327)
                ·
                  refine ⟨93273559148373475946475491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62182372765582317297650327 93273559148373475946475491)
                  ·
                    refine ⟨139910338722560213919713237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93273559148373475946475491 139910338722560213919713237)
                    ·
                      refine ⟨3279148563810005013743279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139910338722560213919713237 3279148563810005013743279)
                      ·
                        rfl

theorem cell23_6386119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_6386119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386119 prefixEnd_6386119 := by exact prefixLift 6386119
  have htrace : WordTrace (prefixWord ++ tailWord_6386119) baseStart_6386119 baseEnd_6386119 := by
    simpa [prefixWord, tailWord_6386119, baseEnd_6386119] using wordTrace_append hprefix tailTrace_6386119
  have hstable : (prefixWord ++ tailWord_6386119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386119).length < 2 ^ (prefixWord ++ tailWord_6386119).sum := by decide
  have hdescent : baseEnd_6386119 < baseStart_6386119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386124 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6386124 : Nat := 118140960795 + 6386124 * 2 ^ 59
def prefixEnd_6386124 : Nat := 4983230072969 + 3 ^ 40 * 6386124 * 2
def baseEnd_6386124 : Nat := 3279151131213277494180757

theorem tailTrace_6386124 : CollatzResearch.WordTrace tailWord_6386124 prefixEnd_6386124 3279151131213277494180757 := by
  unfold tailWord_6386124
  simp only [CollatzResearch.WordTrace]
  refine ⟨116460538758085442996090713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155280718344113923994787617 116460538758085442996090713)
  ·
    refine ⟨87345404068564082247068035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116460538758085442996090713 87345404068564082247068035)
    ·
      refine ⟨131018106102846123370602053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87345404068564082247068035 131018106102846123370602053)
      ·
        refine ⟨24565894894283648131987885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131018106102846123370602053 24565894894283648131987885)
        ·
          refine ⟨9212210585356368049495457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24565894894283648131987885 9212210585356368049495457)
          ·
            refine ⟨6909157939017276037121593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9212210585356368049495457 6909157939017276037121593)
            ·
              refine ⟨5181868454262957027841195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6909157939017276037121593 5181868454262957027841195)
              ·
                refine ⟨7772802681394435541761793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181868454262957027841195 7772802681394435541761793)
                ·
                  refine ⟨5829602011045826656321345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7772802681394435541761793 5829602011045826656321345)
                  ·
                    refine ⟨4372201508284369992241009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5829602011045826656321345 4372201508284369992241009)
                    ·
                      refine ⟨3279151131213277494180757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372201508284369992241009 3279151131213277494180757)
                      ·
                        rfl

theorem cell23_6386124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6386124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386124 prefixEnd_6386124 := by exact prefixLift 6386124
  have htrace : WordTrace (prefixWord ++ tailWord_6386124) baseStart_6386124 baseEnd_6386124 := by
    simpa [prefixWord, tailWord_6386124, baseEnd_6386124] using wordTrace_append hprefix tailTrace_6386124
  have hstable : (prefixWord ++ tailWord_6386124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386124).length < 2 ^ (prefixWord ++ tailWord_6386124).sum := by decide
  have hdescent : baseEnd_6386124 < baseStart_6386124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386129 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_6386129 : Nat := 118140960795 + 6386129 * 2 ^ 59
def prefixEnd_6386129 : Nat := 4983230072969 + 3 ^ 40 * 6386129 * 2
def baseEnd_6386129 : Nat := 3279153698616549974618233

theorem tailTrace_6386129 : CollatzResearch.WordTrace tailWord_6386129 prefixEnd_6386129 3279153698616549974618233 := by
  unfold tailWord_6386129
  simp only [CollatzResearch.WordTrace]
  refine ⟨232921259881152771846113441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155280839920768514564075627 232921259881152771846113441)
  ·
    refine ⟨174690944910864578884585081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232921259881152771846113441 174690944910864578884585081)
    ·
      refine ⟨131018208683148434163438811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174690944910864578884585081 131018208683148434163438811)
      ·
        refine ⟨196527313024722651245158217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131018208683148434163438811 196527313024722651245158217)
        ·
          refine ⟨147395484768541988433868663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196527313024722651245158217 147395484768541988433868663)
          ·
            refine ⟨221093227152812982650802995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147395484768541988433868663 221093227152812982650802995)
            ·
              refine ⟨331639840729219473976204493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221093227152812982650802995 331639840729219473976204493)
              ·
                refine ⟨124364940273457302741076685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331639840729219473976204493 124364940273457302741076685)
                ·
                  refine ⟨46636852602546488527903757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124364940273457302741076685 46636852602546488527903757)
                  ·
                    refine ⟨17488819725954933197963909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46636852602546488527903757 17488819725954933197963909)
                    ·
                      refine ⟨3279153698616549974618233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17488819725954933197963909 3279153698616549974618233)
                      ·
                        rfl

theorem cell23_6386129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_6386129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386129 prefixEnd_6386129 := by exact prefixLift 6386129
  have htrace : WordTrace (prefixWord ++ tailWord_6386129) baseStart_6386129 baseEnd_6386129 := by
    simpa [prefixWord, tailWord_6386129, baseEnd_6386129] using wordTrace_append hprefix tailTrace_6386129
  have hstable : (prefixWord ++ tailWord_6386129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386129).length < 2 ^ (prefixWord ++ tailWord_6386129).sum := by decide
  have hdescent : baseEnd_6386129 < baseStart_6386129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386159 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_6386159 : Nat := 118140960795 + 6386159 * 2 ^ 59
def prefixEnd_6386159 : Nat := 4983230072969 + 3 ^ 40 * 6386159 * 2
def baseEnd_6386159 : Nat := 3279169103036184857243095

theorem tailTrace_6386159 : CollatzResearch.WordTrace tailWord_6386159 prefixEnd_6386159 3279169103036184857243095 := by
  unfold tailWord_6386159
  simp only [CollatzResearch.WordTrace]
  refine ⟨232922354071044086969705531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155281569380696057979803687 232922354071044086969705531)
  ·
    refine ⟨349383531106566130454558297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232922354071044086969705531 349383531106566130454558297)
    ·
      refine ⟨262037648329924597840918723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349383531106566130454558297 262037648329924597840918723)
      ·
        refine ⟨393056472494886896761378085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262037648329924597840918723 393056472494886896761378085)
        ·
          refine ⟨73698088592791293142758391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393056472494886896761378085 73698088592791293142758391)
          ·
            refine ⟨110547132889186939714137587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73698088592791293142758391 110547132889186939714137587)
            ·
              refine ⟨165820699333780409571206381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110547132889186939714137587 165820699333780409571206381)
              ·
                refine ⟨62182762250167653589202393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165820699333780409571206381 62182762250167653589202393)
                ·
                  refine ⟨46637071687625740191901795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62182762250167653589202393 46637071687625740191901795)
                  ·
                    refine ⟨69955607531438610287852693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46637071687625740191901795 69955607531438610287852693)
                    ·
                      refine ⟨3279169103036184857243095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69955607531438610287852693 3279169103036184857243095)
                      ·
                        rfl

theorem cell23_6386159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_6386159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386159 prefixEnd_6386159 := by exact prefixLift 6386159
  have htrace : WordTrace (prefixWord ++ tailWord_6386159) baseStart_6386159 baseEnd_6386159 := by
    simpa [prefixWord, tailWord_6386159, baseEnd_6386159] using wordTrace_append hprefix tailTrace_6386159
  have hstable : (prefixWord ++ tailWord_6386159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386159).length < 2 ^ (prefixWord ++ tailWord_6386159).sum := by decide
  have hdescent : baseEnd_6386159 < baseStart_6386159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386166 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6386166 : Nat := 118140960795 + 6386166 * 2 ^ 59
def prefixEnd_6386166 : Nat := 4983230072969 + 3 ^ 40 * 6386166 * 2
def baseEnd_6386166 : Nat := 3279172697400766329855563

theorem tailTrace_6386166 : CollatzResearch.WordTrace tailWord_6386166 prefixEnd_6386166 3279172697400766329855563 := by
  unfold tailWord_6386166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14557663086376170447825647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155281739588012484776806901 14557663086376170447825647)
  ·
    refine ⟨21836494629564255671738471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14557663086376170447825647 21836494629564255671738471)
    ·
      refine ⟨32754741944346383507607707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21836494629564255671738471 32754741944346383507607707)
      ·
        refine ⟨49132112916519575261411561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32754741944346383507607707 49132112916519575261411561)
        ·
          refine ⟨36849084687389681446058671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49132112916519575261411561 36849084687389681446058671)
          ·
            refine ⟨55273627031084522169088007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36849084687389681446058671 55273627031084522169088007)
            ·
              refine ⟨82910440546626783253632011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55273627031084522169088007 82910440546626783253632011)
              ·
                refine ⟨124365660819940174880448017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82910440546626783253632011 124365660819940174880448017)
                ·
                  refine ⟨93274245614955131160336013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124365660819940174880448017 93274245614955131160336013)
                  ·
                    refine ⟨34977842105608174185126005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93274245614955131160336013 34977842105608174185126005)
                    ·
                      refine ⟨3279172697400766329855563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34977842105608174185126005 3279172697400766329855563)
                      ·
                        rfl

theorem cell23_6386166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6386166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386166 prefixEnd_6386166 := by exact prefixLift 6386166
  have htrace : WordTrace (prefixWord ++ tailWord_6386166) baseStart_6386166 baseEnd_6386166 := by
    simpa [prefixWord, tailWord_6386166, baseEnd_6386166] using wordTrace_append hprefix tailTrace_6386166
  have hstable : (prefixWord ++ tailWord_6386166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386166).length < 2 ^ (prefixWord ++ tailWord_6386166).sum := by decide
  have hdescent : baseEnd_6386166 < baseStart_6386166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386169 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 8]
def baseStart_6386169 : Nat := 118140960795 + 6386169 * 2 ^ 59
def prefixEnd_6386169 : Nat := 4983230072969 + 3 ^ 40 * 6386169 * 2
def baseEnd_6386169 : Nat := 364352693093636646457561

theorem tailTrace_6386169 : CollatzResearch.WordTrace tailWord_6386169 prefixEnd_6386169 364352693093636646457561 := by
  unfold tailWord_6386169
  simp only [CollatzResearch.WordTrace]
  refine ⟨232922718801007858677569561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155281812534005239118379707 232922718801007858677569561)
  ·
    refine ⟨174692039100755894008177171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232922718801007858677569561 174692039100755894008177171)
    ·
      refine ⟨262038058651133841012265757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174692039100755894008177171 262038058651133841012265757)
      ·
        refine ⟨98264271994175190379599659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262038058651133841012265757 98264271994175190379599659)
        ·
          refine ⟨147396407991262785569399489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98264271994175190379599659 147396407991262785569399489)
          ·
            refine ⟨110547305993447089177049617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147396407991262785569399489 110547305993447089177049617)
            ·
              refine ⟨82910479495085316882787213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110547305993447089177049617 82910479495085316882787213)
              ·
                refine ⟨31091429810656993831045205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82910479495085316882787213 31091429810656993831045205)
                ·
                  refine ⟨364352693093636646457561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31091429810656993831045205 364352693093636646457561)
                  ·
                    rfl

theorem cell23_6386169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_6386169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386169 prefixEnd_6386169 := by exact prefixLift 6386169
  have htrace : WordTrace (prefixWord ++ tailWord_6386169) baseStart_6386169 baseEnd_6386169 := by
    simpa [prefixWord, tailWord_6386169, baseEnd_6386169] using wordTrace_append hprefix tailTrace_6386169
  have hstable : (prefixWord ++ tailWord_6386169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386169).length < 2 ^ (prefixWord ++ tailWord_6386169).sum := by decide
  have hdescent : baseEnd_6386169 < baseStart_6386169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386180 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6386180 : Nat := 118140960795 + 6386180 * 2 ^ 59
def prefixEnd_6386180 : Nat := 4983230072969 + 3 ^ 40 * 6386180 * 2
def baseEnd_6386180 : Nat := 3279179886129929275080499

theorem tailTrace_6386180 : CollatzResearch.WordTrace tailWord_6386180 prefixEnd_6386180 3279179886129929275080499 := by
  unfold tailWord_6386180
  simp only [CollatzResearch.WordTrace]
  refine ⟨116461560001984003778109997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155282080002645338370813329 116461560001984003778109997)
  ·
    refine ⟨43673085000744001416791249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116461560001984003778109997 43673085000744001416791249)
    ·
      refine ⟨32754813750558001062593437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43673085000744001416791249 32754813750558001062593437)
      ·
        refine ⟨12283055156459250398472539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32754813750558001062593437 12283055156459250398472539)
        ·
          refine ⟨18424582734688875597708809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12283055156459250398472539 18424582734688875597708809)
          ·
            refine ⟨13818437051016656698281607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18424582734688875597708809 13818437051016656698281607)
            ·
              refine ⟨20727655576524985047422411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818437051016656698281607 20727655576524985047422411)
              ·
                refine ⟨31091483364787477571133617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20727655576524985047422411 31091483364787477571133617)
                ·
                  refine ⟨23318612523590608178350213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31091483364787477571133617 23318612523590608178350213)
                  ·
                    refine ⟨4372239848173239033440665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23318612523590608178350213 4372239848173239033440665)
                    ·
                      refine ⟨3279179886129929275080499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372239848173239033440665 3279179886129929275080499)
                      ·
                        rfl

theorem cell23_6386180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6386180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386180 prefixEnd_6386180 := by exact prefixLift 6386180
  have htrace : WordTrace (prefixWord ++ tailWord_6386180) baseStart_6386180 baseEnd_6386180 := by
    simpa [prefixWord, tailWord_6386180, baseEnd_6386180] using wordTrace_append hprefix tailTrace_6386180
  have hstable : (prefixWord ++ tailWord_6386180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386180).length < 2 ^ (prefixWord ++ tailWord_6386180).sum := by decide
  have hdescent : baseEnd_6386180 < baseStart_6386180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386186 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_6386186 : Nat := 118140960795 + 6386186 * 2 ^ 59
def prefixEnd_6386186 : Nat := 4983230072969 + 3 ^ 40 * 6386186 * 2
def baseEnd_6386186 : Nat := 364353663001539583511719

theorem tailTrace_6386186 : CollatzResearch.WordTrace tailWord_6386186 prefixEnd_6386186 364353663001539583511719 := by
  unfold tailWord_6386186
  simp only [CollatzResearch.WordTrace]
  refine ⟨58230834710486567645234603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155282225894630847053958941 58230834710486567645234603)
  ·
    refine ⟨87346252065729851467851905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58230834710486567645234603 87346252065729851467851905)
    ·
      refine ⟨65509689049297388600888929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87346252065729851467851905 65509689049297388600888929)
      ·
        refine ⟨49132266786973041450666697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65509689049297388600888929 49132266786973041450666697)
        ·
          refine ⟨36849200090229781088000023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49132266786973041450666697 36849200090229781088000023)
          ·
            refine ⟨55273800135344671632000035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36849200090229781088000023 55273800135344671632000035)
            ·
              refine ⟨82910700203017007448000053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55273800135344671632000035 82910700203017007448000053)
              ·
                refine ⟨7772878144032844448250005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82910700203017007448000053 7772878144032844448250005)
                ·
                  refine ⟨364353663001539583511719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7772878144032844448250005 364353663001539583511719)
                  ·
                    rfl

theorem cell23_6386186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_6386186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386186 prefixEnd_6386186 := by exact prefixLift 6386186
  have htrace : WordTrace (prefixWord ++ tailWord_6386186) baseStart_6386186 baseEnd_6386186 := by
    simpa [prefixWord, tailWord_6386186, baseEnd_6386186] using wordTrace_append hprefix tailTrace_6386186
  have hstable : (prefixWord ++ tailWord_6386186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386186).length < 2 ^ (prefixWord ++ tailWord_6386186).sum := by decide
  have hdescent : baseEnd_6386186 < baseStart_6386186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386200 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_6386200 : Nat := 118140960795 + 6386200 * 2 ^ 59
def prefixEnd_6386200 : Nat := 4983230072969 + 3 ^ 40 * 6386200 * 2
def baseEnd_6386200 : Nat := 3279190155743019196830407

theorem tailTrace_6386200 : CollatzResearch.WordTrace tailWord_6386200 prefixEnd_6386200 3279190155743019196830407 := by
  unfold tailWord_6386200
  simp only [CollatzResearch.WordTrace]
  refine ⟨116461924731947775485974027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155282566309263700647965369 116461924731947775485974027)
  ·
    refine ⟨174692887097921663228961041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116461924731947775485974027 174692887097921663228961041)
    ·
      refine ⟨131019665323441247421720781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174692887097921663228961041 131019665323441247421720781)
      ·
        refine ⟨49132374496290467783145293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131019665323441247421720781 49132374496290467783145293)
        ·
          refine ⟨18424640436108925418679485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49132374496290467783145293 18424640436108925418679485)
          ·
            refine ⟨6909240163540847032004807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18424640436108925418679485 6909240163540847032004807)
            ·
              refine ⟨10363860245311270548007211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6909240163540847032004807 10363860245311270548007211)
              ·
                refine ⟨15545790367966905822010817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363860245311270548007211 15545790367966905822010817)
                ·
                  refine ⟨11659342775975179366508113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15545790367966905822010817 11659342775975179366508113)
                  ·
                    refine ⟨8744507081981384524881085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11659342775975179366508113 8744507081981384524881085)
                    ·
                      refine ⟨3279190155743019196830407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8744507081981384524881085 3279190155743019196830407)
                      ·
                        rfl

theorem cell23_6386200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_6386200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386200 prefixEnd_6386200 := by exact prefixLift 6386200
  have htrace : WordTrace (prefixWord ++ tailWord_6386200) baseStart_6386200 baseEnd_6386200 := by
    simpa [prefixWord, tailWord_6386200, baseEnd_6386200] using wordTrace_append hprefix tailTrace_6386200
  have hstable : (prefixWord ++ tailWord_6386200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386200).length < 2 ^ (prefixWord ++ tailWord_6386200).sum := by decide
  have hdescent : baseEnd_6386200 < baseStart_6386200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386273 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_6386273 : Nat := 118140960795 + 6386273 * 2 ^ 59
def prefixEnd_6386273 : Nat := 4983230072969 + 3 ^ 40 * 6386273 * 2
def baseEnd_6386273 : Nat := 3279227639830797411217571

theorem tailTrace_6386273 : CollatzResearch.WordTrace tailWord_6386273 prefixEnd_6386273 3279227639830797411217571 := by
  unfold tailWord_6386273
  simp only [CollatzResearch.WordTrace]
  refine ⟨232926511992631084439355473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155284341328420722959570315 232926511992631084439355473)
  ·
    refine ⟨174694883994473313329516605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232926511992631084439355473 174694883994473313329516605)
    ·
      refine ⟨65510581497927492498568727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174694883994473313329516605 65510581497927492498568727)
      ·
        refine ⟨98265872246891238747853091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65510581497927492498568727 98265872246891238747853091)
        ·
          refine ⟨147398808370336858121779637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98265872246891238747853091 147398808370336858121779637)
          ·
            refine ⟨13818638284719080448916841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147398808370336858121779637 13818638284719080448916841)
            ·
              refine ⟨10363978713539310336687631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13818638284719080448916841 10363978713539310336687631)
              ·
                refine ⟨15545968070308965505031447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363978713539310336687631 15545968070308965505031447)
                ·
                  refine ⟨23318952105463448257547171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15545968070308965505031447 23318952105463448257547171)
                  ·
                    refine ⟨34978428158195172386320757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23318952105463448257547171 34978428158195172386320757)
                    ·
                      refine ⟨3279227639830797411217571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34978428158195172386320757 3279227639830797411217571)
                      ·
                        rfl

theorem cell23_6386273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_6386273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386273 prefixEnd_6386273 := by exact prefixLift 6386273
  have htrace : WordTrace (prefixWord ++ tailWord_6386273) baseStart_6386273 baseEnd_6386273 := by
    simpa [prefixWord, tailWord_6386273, baseEnd_6386273] using wordTrace_append hprefix tailTrace_6386273
  have hstable : (prefixWord ++ tailWord_6386273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386273).length < 2 ^ (prefixWord ++ tailWord_6386273).sum := by decide
  have hdescent : baseEnd_6386273 < baseStart_6386273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386274 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6386274 : Nat := 118140960795 + 6386274 * 2 ^ 59
def prefixEnd_6386274 : Nat := 4983230072969 + 3 ^ 40 * 6386274 * 2
def baseEnd_6386274 : Nat := 3279228153311451907305067

theorem tailTrace_6386274 : CollatzResearch.WordTrace tailWord_6386274 prefixEnd_6386274 3279228153311451907305067 := by
  unfold tailWord_6386274
  simp only [CollatzResearch.WordTrace]
  refine ⟨58231637116406865402535469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155284365643751641073427917 58231637116406865402535469)
  ·
    refine ⟨21836863918652574525950801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58231637116406865402535469 21836863918652574525950801)
    ·
      refine ⟨16377647938989430894463101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21836863918652574525950801 16377647938989430894463101)
      ·
        refine ⟨6141617977121036585423663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16377647938989430894463101 6141617977121036585423663)
        ·
          refine ⟨9212426965681554878135495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6141617977121036585423663 9212426965681554878135495)
          ·
            refine ⟨13818640448522332317203243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212426965681554878135495 13818640448522332317203243)
            ·
              refine ⟨20727960672783498475804865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818640448522332317203243 20727960672783498475804865)
              ·
                refine ⟨15545970504587623856853649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20727960672783498475804865 15545970504587623856853649)
                ·
                  refine ⟨11659477878440717892640237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15545970504587623856853649 11659477878440717892640237)
                  ·
                    refine ⟨4372304204415269209740089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11659477878440717892640237 4372304204415269209740089)
                    ·
                      refine ⟨3279228153311451907305067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372304204415269209740089 3279228153311451907305067)
                      ·
                        rfl

theorem cell23_6386274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6386274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386274 prefixEnd_6386274 := by exact prefixLift 6386274
  have htrace : WordTrace (prefixWord ++ tailWord_6386274) baseStart_6386274 baseEnd_6386274 := by
    simpa [prefixWord, tailWord_6386274, baseEnd_6386274] using wordTrace_append hprefix tailTrace_6386274
  have hstable : (prefixWord ++ tailWord_6386274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386274).length < 2 ^ (prefixWord ++ tailWord_6386274).sum := by decide
  have hdescent : baseEnd_6386274 < baseStart_6386274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386287 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 1, 2, 2]
def baseStart_6386287 : Nat := 118140960795 + 6386287 * 2 ^ 59
def prefixEnd_6386287 : Nat := 4983230072969 + 3 ^ 40 * 6386287 * 2
def baseEnd_6386287 : Nat := 3279234828559960356442507

theorem tailTrace_6386287 : CollatzResearch.WordTrace tailWord_6386287 prefixEnd_6386287 3279234828559960356442507 := by
  unfold tailWord_6386287
  simp only [CollatzResearch.WordTrace]
  refine ⟨232927022614580364830365115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155284681743053576553576743 232927022614580364830365115)
  ·
    refine ⟨349390533921870547245547673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232927022614580364830365115 349390533921870547245547673)
    ·
      refine ⟨262042900441402910434160755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349390533921870547245547673 262042900441402910434160755)
      ·
        refine ⟨393064350662104365651241133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262042900441402910434160755 393064350662104365651241133)
        ·
          refine ⟨147399131498289137119215425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393064350662104365651241133 147399131498289137119215425)
          ·
            refine ⟨110549348623716852839411569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147399131498289137119215425 110549348623716852839411569)
            ·
              refine ⟨82912011467787639629558677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110549348623716852839411569 82912011467787639629558677)
              ·
                refine ⟨3886500537552545607635563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82912011467787639629558677 3886500537552545607635563)
                ·
                  refine ⟨5829750806328818411453345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886500537552545607635563 5829750806328818411453345)
                  ·
                    refine ⟨4372313104746613808590009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5829750806328818411453345 4372313104746613808590009)
                    ·
                      refine ⟨3279234828559960356442507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372313104746613808590009 3279234828559960356442507)
                      ·
                        rfl

theorem cell23_6386287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 2, 2].length) (baseStart_6386287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386287 prefixEnd_6386287 := by exact prefixLift 6386287
  have htrace : WordTrace (prefixWord ++ tailWord_6386287) baseStart_6386287 baseEnd_6386287 := by
    simpa [prefixWord, tailWord_6386287, baseEnd_6386287] using wordTrace_append hprefix tailTrace_6386287
  have hstable : (prefixWord ++ tailWord_6386287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386287).length < 2 ^ (prefixWord ++ tailWord_6386287).sum := by decide
  have hdescent : baseEnd_6386287 < baseStart_6386287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386297 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 2, 4]
def baseStart_6386297 : Nat := 118140960795 + 6386297 * 2 ^ 59
def prefixEnd_6386297 : Nat := 4983230072969 + 3 ^ 40 * 6386297 * 2
def baseEnd_6386297 : Nat := 1093079987788835105772487

theorem tailTrace_6386297 : CollatzResearch.WordTrace tailWord_6386297 prefixEnd_6386297 1093079987788835105772487 := by
  unfold tailWord_6386297
  simp only [CollatzResearch.WordTrace]
  refine ⟨232927387344544136538229145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155284924896362757692152763 232927387344544136538229145)
  ·
    refine ⟨174695540508408102403671859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232927387344544136538229145 174695540508408102403671859)
    ·
      refine ⟨262043310762612153605507789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174695540508408102403671859 262043310762612153605507789)
      ·
        refine ⟨98266241535979557602065421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262043310762612153605507789 98266241535979557602065421)
        ·
          refine ⟨36849840575992334100774533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98266241535979557602065421 36849840575992334100774533)
          ·
            refine ⟨6909345107998562643895225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36849840575992334100774533 6909345107998562643895225)
            ·
              refine ⟨5182008830998921982921419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6909345107998562643895225 5182008830998921982921419)
              ·
                refine ⟨7773013246498382974382129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182008830998921982921419 7773013246498382974382129)
                ·
                  refine ⟨5829759934873787230786597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7773013246498382974382129 5829759934873787230786597)
                  ·
                    refine ⟨1093079987788835105772487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5829759934873787230786597 1093079987788835105772487)
                    ·
                      rfl

theorem cell23_6386297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 4].length) (baseStart_6386297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386297 prefixEnd_6386297 := by exact prefixLift 6386297
  have htrace : WordTrace (prefixWord ++ tailWord_6386297) baseStart_6386297 baseEnd_6386297 := by
    simpa [prefixWord, tailWord_6386297, baseEnd_6386297] using wordTrace_append hprefix tailTrace_6386297
  have hstable : (prefixWord ++ tailWord_6386297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386297).length < 2 ^ (prefixWord ++ tailWord_6386297).sum := by decide
  have hdescent : baseEnd_6386297 < baseStart_6386297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386303 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 3]
def baseStart_6386303 : Nat := 118140960795 + 6386303 * 2 ^ 59
def prefixEnd_6386303 : Nat := 4983230072969 + 3 ^ 40 * 6386303 * 2
def baseEnd_6386303 : Nat := 3279243044250432293842433

theorem tailTrace_6386303 : CollatzResearch.WordTrace tailWord_6386303 prefixEnd_6386303 3279243044250432293842433 := by
  unfold tailWord_6386303
  simp only [CollatzResearch.WordTrace]
  refine ⟨232927606182522399562947563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155285070788348266375298375 232927606182522399562947563)
  ·
    refine ⟨349391409273783599344421345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232927606182522399562947563 349391409273783599344421345)
    ·
      refine ⟨262043556955337699508316009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349391409273783599344421345 262043556955337699508316009)
      ·
        refine ⟨196532667716503274631237007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262043556955337699508316009 196532667716503274631237007)
        ·
          refine ⟨294799001574754911946855511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196532667716503274631237007 294799001574754911946855511)
          ·
            refine ⟨442198502362132367920283267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294799001574754911946855511 442198502362132367920283267)
            ·
              refine ⟨663297753543198551880424901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442198502362132367920283267 663297753543198551880424901)
              ·
                refine ⟨124368328789349728477579669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 663297753543198551880424901 124368328789349728477579669)
                ·
                  refine ⟨5829765412000768522386547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124368328789349728477579669 5829765412000768522386547)
                  ·
                    refine ⟨8744648118001152783579821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5829765412000768522386547 8744648118001152783579821)
                    ·
                      refine ⟨3279243044250432293842433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8744648118001152783579821 3279243044250432293842433)
                      ·
                        rfl

theorem cell23_6386303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_6386303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386303 prefixEnd_6386303 := by exact prefixLift 6386303
  have htrace : WordTrace (prefixWord ++ tailWord_6386303) baseStart_6386303 baseEnd_6386303 := by
    simpa [prefixWord, tailWord_6386303, baseEnd_6386303] using wordTrace_append hprefix tailTrace_6386303
  have hstable : (prefixWord ++ tailWord_6386303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386303).length < 2 ^ (prefixWord ++ tailWord_6386303).sum := by decide
  have hdescent : baseEnd_6386303 < baseStart_6386303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386316 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_6386316 : Nat := 118140960795 + 6386316 * 2 ^ 59
def prefixEnd_6386316 : Nat := 4983230072969 + 3 ^ 40 * 6386316 * 2
def baseEnd_6386316 : Nat := 3279249719498940742979873

theorem tailTrace_6386316 : CollatzResearch.WordTrace tailWord_6386316 prefixEnd_6386316 3279249719498940742979873 := by
  unfold tailWord_6386316
  simp only [CollatzResearch.WordTrace]
  refine ⟨116464040165737651391585401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155285386887650201855447201 116464040165737651391585401)
  ·
    refine ⟨87348030124303238543689051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116464040165737651391585401 87348030124303238543689051)
    ·
      refine ⟨131022045186454857815533577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87348030124303238543689051 131022045186454857815533577)
      ·
        refine ⟨98266533889841143361650183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131022045186454857815533577 98266533889841143361650183)
        ·
          refine ⟨147399800834761715042475275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98266533889841143361650183 147399800834761715042475275)
          ·
            refine ⟨221099701252142572563712913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147399800834761715042475275 221099701252142572563712913)
            ·
              refine ⟨165824775939106929422784685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221099701252142572563712913 165824775939106929422784685)
              ·
                refine ⟨62184290977165098533544257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165824775939106929422784685 62184290977165098533544257)
                ·
                  refine ⟨46638218232873823900158193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62184290977165098533544257 46638218232873823900158193)
                  ·
                    refine ⟨34978663674655367925118645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46638218232873823900158193 34978663674655367925118645)
                    ·
                      refine ⟨3279249719498940742979873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34978663674655367925118645 3279249719498940742979873)
                      ·
                        rfl

theorem cell23_6386316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_6386316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386316 prefixEnd_6386316 := by exact prefixLift 6386316
  have htrace : WordTrace (prefixWord ++ tailWord_6386316) baseStart_6386316 baseEnd_6386316 := by
    simpa [prefixWord, tailWord_6386316, baseEnd_6386316] using wordTrace_append hprefix tailTrace_6386316
  have hstable : (prefixWord ++ tailWord_6386316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386316).length < 2 ^ (prefixWord ++ tailWord_6386316).sum := by decide
  have hdescent : baseEnd_6386316 < baseStart_6386316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386324 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6386324 : Nat := 118140960795 + 6386324 * 2 ^ 59
def prefixEnd_6386324 : Nat := 4983230072969 + 3 ^ 40 * 6386324 * 2
def baseEnd_6386324 : Nat := 3279253827344176711679837

theorem tailTrace_6386324 : CollatzResearch.WordTrace tailWord_6386324 prefixEnd_6386324 3279253827344176711679837 := by
  unfold tailWord_6386324
  simp only [CollatzResearch.WordTrace]
  refine ⟨116464186057723160074731013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155285581410297546766308017 116464186057723160074731013)
  ·
    refine ⟨21837034885823092514012065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116464186057723160074731013 21837034885823092514012065)
    ·
      refine ⟨16377776164367319385509049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21837034885823092514012065 16377776164367319385509049)
      ·
        refine ⟨12283332123275489539131787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16377776164367319385509049 12283332123275489539131787)
        ·
          refine ⟨18424998184913234308697681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12283332123275489539131787 18424998184913234308697681)
          ·
            refine ⟨13818748638684925731523261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18424998184913234308697681 13818748638684925731523261)
            ·
              refine ⟨5182030739506847149321223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13818748638684925731523261 5182030739506847149321223)
              ·
                refine ⟨7773046109260270723981835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182030739506847149321223 7773046109260270723981835)
                ·
                  refine ⟨11659569163890406085972753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773046109260270723981835 11659569163890406085972753)
                  ·
                    refine ⟨8744676872917804564479565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11659569163890406085972753 8744676872917804564479565)
                    ·
                      refine ⟨3279253827344176711679837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8744676872917804564479565 3279253827344176711679837)
                      ·
                        rfl

theorem cell23_6386324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6386324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386324 prefixEnd_6386324 := by exact prefixLift 6386324
  have htrace : WordTrace (prefixWord ++ tailWord_6386324) baseStart_6386324 baseEnd_6386324 := by
    simpa [prefixWord, tailWord_6386324, baseEnd_6386324] using wordTrace_append hprefix tailTrace_6386324
  have hstable : (prefixWord ++ tailWord_6386324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386324).length < 2 ^ (prefixWord ++ tailWord_6386324).sum := by decide
  have hdescent : baseEnd_6386324 < baseStart_6386324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386360 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 8, 2, 2]
def baseStart_6386360 : Nat := 118140960795 + 6386360 * 2 ^ 59
def prefixEnd_6386360 : Nat := 4983230072969 + 3 ^ 40 * 6386360 * 2
def baseEnd_6386360 : Nat := 3279272312647738570829671

theorem tailTrace_6386360 : CollatzResearch.WordTrace tailWord_6386360 prefixEnd_6386360 3279272312647738570829671 := by
  unfold tailWord_6386360
  simp only [CollatzResearch.WordTrace]
  refine ⟨116464842571657949148886267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155286456762210598865181689 116464842571657949148886267)
  ·
    refine ⟨174697263857486923723329401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116464842571657949148886267 174697263857486923723329401)
    ·
      refine ⟨131022947893115192792497051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174697263857486923723329401 131022947893115192792497051)
      ·
        refine ⟨196534421839672789188745577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131022947893115192792497051 196534421839672789188745577)
        ·
          refine ⟨147400816379754591891559183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196534421839672789188745577 147400816379754591891559183)
          ·
            refine ⟨221101224569631887837338775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147400816379754591891559183 221101224569631887837338775)
            ·
              refine ⟨331651836854447831756008163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221101224569631887837338775 331651836854447831756008163)
              ·
                refine ⟨497477755281671747634012245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331651836854447831756008163 497477755281671747634012245)
                ·
                  refine ⟨5829817444707090792586081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 497477755281671747634012245 5829817444707090792586081)
                  ·
                    refine ⟨4372363083530318094439561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5829817444707090792586081 4372363083530318094439561)
                    ·
                      refine ⟨3279272312647738570829671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372363083530318094439561 3279272312647738570829671)
                      ·
                        rfl

theorem cell23_6386360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_6386360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386360 prefixEnd_6386360 := by exact prefixLift 6386360
  have htrace : WordTrace (prefixWord ++ tailWord_6386360) baseStart_6386360 baseEnd_6386360 := by
    simpa [prefixWord, tailWord_6386360, baseEnd_6386360] using wordTrace_append hprefix tailTrace_6386360
  have hstable : (prefixWord ++ tailWord_6386360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386360).length < 2 ^ (prefixWord ++ tailWord_6386360).sum := by decide
  have hdescent : baseEnd_6386360 < baseStart_6386360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386381 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6386381 : Nat := 118140960795 + 6386381 * 2 ^ 59
def prefixEnd_6386381 : Nat := 4983230072969 + 3 ^ 40 * 6386381 * 2
def baseEnd_6386381 : Nat := 3279283095741482988667075

theorem tailTrace_6386381 : CollatzResearch.WordTrace tailWord_6386381 prefixEnd_6386381 3279283095741482988667075 := by
  unfold tailWord_6386381
  simp only [CollatzResearch.WordTrace]
  refine ⟨232930451076239818884286997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155286967384159879256191331 232930451076239818884286997)
  ·
    refine ⟨10918614894198741510200953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232930451076239818884286997 10918614894198741510200953)
    ·
      refine ⟨8188961170649056132650715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10918614894198741510200953 8188961170649056132650715)
      ·
        refine ⟨12283441755973584198976073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8188961170649056132650715 12283441755973584198976073)
        ·
          refine ⟨9212581316980188149232055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12283441755973584198976073 9212581316980188149232055)
          ·
            refine ⟨13818871975470282223848083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212581316980188149232055 13818871975470282223848083)
            ·
              refine ⟨20728307963205423335772125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13818871975470282223848083 20728307963205423335772125)
              ·
                refine ⟨7773115486202033750914547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20728307963205423335772125 7773115486202033750914547)
                ·
                  refine ⟨11659673229303050626371821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773115486202033750914547 11659673229303050626371821)
                  ·
                    refine ⟨4372377460988643984889433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11659673229303050626371821 4372377460988643984889433)
                    ·
                      refine ⟨3279283095741482988667075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372377460988643984889433 3279283095741482988667075)
                      ·
                        rfl

theorem cell23_6386381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6386381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386381 prefixEnd_6386381 := by exact prefixLift 6386381
  have htrace : WordTrace (prefixWord ++ tailWord_6386381) baseStart_6386381 baseEnd_6386381 := by
    simpa [prefixWord, tailWord_6386381, baseEnd_6386381] using wordTrace_append hprefix tailTrace_6386381
  have hstable : (prefixWord ++ tailWord_6386381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386381).length < 2 ^ (prefixWord ++ tailWord_6386381).sum := by decide
  have hdescent : baseEnd_6386381 < baseStart_6386381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386393 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_6386393 : Nat := 118140960795 + 6386393 * 2 ^ 59
def prefixEnd_6386393 : Nat := 4983230072969 + 3 ^ 40 * 6386393 * 2
def baseEnd_6386393 : Nat := 3279289257509336941717019

theorem tailTrace_6386393 : CollatzResearch.WordTrace tailWord_6386393 prefixEnd_6386393 3279289257509336941717019 := by
  unfold tailWord_6386393
  simp only [CollatzResearch.WordTrace]
  refine ⟨232930888752196344933723833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155287259168130896622482555 232930888752196344933723833)
  ·
    refine ⟨174698166564147258700292875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232930888752196344933723833 174698166564147258700292875)
    ·
      refine ⟨262047249846220888050439313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174698166564147258700292875 262047249846220888050439313)
      ·
        refine ⟨196535437384665666037829485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262047249846220888050439313 196535437384665666037829485)
        ·
          refine ⟨73700789019249624764186057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196535437384665666037829485 73700789019249624764186057)
          ·
            refine ⟨55275591764437218573139543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73700789019249624764186057 55275591764437218573139543)
            ·
              refine ⟨82913387646655827859709315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55275591764437218573139543 82913387646655827859709315)
              ·
                refine ⟨124370081469983741789563973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82913387646655827859709315 124370081469983741789563973)
                ·
                  refine ⟨23319390275621951585543245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124370081469983741789563973 23319390275621951585543245)
                  ·
                    refine ⟨8744771353358231844578717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23319390275621951585543245 8744771353358231844578717)
                    ·
                      refine ⟨3279289257509336941717019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8744771353358231844578717 3279289257509336941717019)
                      ·
                        rfl

theorem cell23_6386393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_6386393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386393 prefixEnd_6386393 := by exact prefixLift 6386393
  have htrace : WordTrace (prefixWord ++ tailWord_6386393) baseStart_6386393 baseEnd_6386393 := by
    simpa [prefixWord, tailWord_6386393, baseEnd_6386393] using wordTrace_append hprefix tailTrace_6386393
  have hstable : (prefixWord ++ tailWord_6386393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386393).length < 2 ^ (prefixWord ++ tailWord_6386393).sum := by decide
  have hdescent : baseEnd_6386393 < baseStart_6386393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386413 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_6386413 : Nat := 118140960795 + 6386413 * 2 ^ 59
def prefixEnd_6386413 : Nat := 4983230072969 + 3 ^ 40 * 6386413 * 2
def baseEnd_6386413 : Nat := 1093099842374142287822309

theorem tailTrace_6386413 : CollatzResearch.WordTrace tailWord_6386413 prefixEnd_6386413 1093099842374142287822309 := by
  unfold tailWord_6386413
  simp only [CollatzResearch.WordTrace]
  refine ⟨232931618212123888349451893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155287745474749258899634595 232931618212123888349451893)
  ·
    refine ⟨21837339207386614532761115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232931618212123888349451893 21837339207386614532761115)
    ·
      refine ⟨32756008811079921799141673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21837339207386614532761115 32756008811079921799141673)
      ·
        refine ⟨24567006608309941349356255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32756008811079921799141673 24567006608309941349356255)
        ·
          refine ⟨36850509912464912024034383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24567006608309941349356255 36850509912464912024034383)
          ·
            refine ⟨55275764868697368036051575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36850509912464912024034383 55275764868697368036051575)
            ·
              refine ⟨82913647303046052054077363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55275764868697368036051575 82913647303046052054077363)
              ·
                refine ⟨124370470954569078081116045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82913647303046052054077363 124370470954569078081116045)
                ·
                  refine ⟨46638926607963404280418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124370470954569078081116045 46638926607963404280418517)
                  ·
                    refine ⟨1093099842374142287822309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46638926607963404280418517 1093099842374142287822309)
                    ·
                      rfl

theorem cell23_6386413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_6386413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386413 prefixEnd_6386413 := by exact prefixLift 6386413
  have htrace : WordTrace (prefixWord ++ tailWord_6386413) baseStart_6386413 baseEnd_6386413 := by
    simpa [prefixWord, tailWord_6386413, baseEnd_6386413] using wordTrace_append hprefix tailTrace_6386413
  have hstable : (prefixWord ++ tailWord_6386413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386413).length < 2 ^ (prefixWord ++ tailWord_6386413).sum := by decide
  have hdescent : baseEnd_6386413 < baseStart_6386413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386430 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_6386430 : Nat := 118140960795 + 6386430 * 2 ^ 59
def prefixEnd_6386430 : Nat := 4983230072969 + 3 ^ 40 * 6386430 * 2
def baseEnd_6386430 : Nat := 1093102752097851098984783

theorem tailTrace_6386430 : CollatzResearch.WordTrace tailWord_6386430 prefixEnd_6386430 1093102752097851098984783 := by
  unfold tailWord_6386430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29116529781632787531602593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155288158835374866835213829 29116529781632787531602593)
  ·
    refine ⟨21837397336224590648701945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29116529781632787531602593 21837397336224590648701945)
    ·
      refine ⟨16378048002168442986526459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21837397336224590648701945 16378048002168442986526459)
      ·
        refine ⟨24567072003252664479789689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378048002168442986526459 24567072003252664479789689)
        ·
          refine ⟨18425304002439498359842267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24567072003252664479789689 18425304002439498359842267)
          ·
            refine ⟨27637956003659247539763401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18425304002439498359842267 27637956003659247539763401)
            ·
              refine ⟨20728467002744435654822551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27637956003659247539763401 20728467002744435654822551)
              ·
                refine ⟨31092700504116653482233827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20728467002744435654822551 31092700504116653482233827)
                ·
                  refine ⟨46639050756174980223350741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31092700504116653482233827 46639050756174980223350741)
                  ·
                    refine ⟨1093102752097851098984783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46639050756174980223350741 1093102752097851098984783)
                    ·
                      rfl

theorem cell23_6386430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_6386430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386430 prefixEnd_6386430 := by exact prefixLift 6386430
  have htrace : WordTrace (prefixWord ++ tailWord_6386430) baseStart_6386430 baseEnd_6386430 := by
    simpa [prefixWord, tailWord_6386430, baseEnd_6386430] using wordTrace_append hprefix tailTrace_6386430
  have hstable : (prefixWord ++ tailWord_6386430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386430).length < 2 ^ (prefixWord ++ tailWord_6386430).sum := by decide
  have hdescent : baseEnd_6386430 < baseStart_6386430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386434 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_6386434 : Nat := 118140960795 + 6386434 * 2 ^ 59
def prefixEnd_6386434 : Nat := 4983230072969 + 3 ^ 40 * 6386434 * 2
def baseEnd_6386434 : Nat := 364367812246241253478259

theorem tailTrace_6386434 : CollatzResearch.WordTrace tailWord_6386434 prefixEnd_6386434 364367812246241253478259 := by
  unfold tailWord_6386434
  simp only [CollatzResearch.WordTrace]
  refine ⟨58233096036261952233991589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155288256096698539290644237 58233096036261952233991589)
  ·
    refine ⟨10918705506799116043873423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58233096036261952233991589 10918705506799116043873423)
    ·
      refine ⟨16378058260198674065810135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10918705506799116043873423 16378058260198674065810135)
      ·
        refine ⟨24567087390298011098715203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378058260198674065810135 24567087390298011098715203)
        ·
          refine ⟨36850631085447016648072805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24567087390298011098715203 36850631085447016648072805)
          ·
            refine ⟨6909493328521315621513651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36850631085447016648072805 6909493328521315621513651)
            ·
              refine ⟨10364239992781973432270477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6909493328521315621513651 10364239992781973432270477)
              ·
                refine ⟨3886589997293240037101429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10364239992781973432270477 3886589997293240037101429)
                ·
                  refine ⟨364367812246241253478259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3886589997293240037101429 364367812246241253478259)
                  ·
                    rfl

theorem cell23_6386434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_6386434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386434 prefixEnd_6386434 := by exact prefixLift 6386434
  have htrace : WordTrace (prefixWord ++ tailWord_6386434) baseStart_6386434 baseEnd_6386434 := by
    simpa [prefixWord, tailWord_6386434, baseEnd_6386434] using wordTrace_append hprefix tailTrace_6386434
  have hstable : (prefixWord ++ tailWord_6386434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386434).length < 2 ^ (prefixWord ++ tailWord_6386434).sum := by decide
  have hdescent : baseEnd_6386434 < baseStart_6386434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386473 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 6]
def baseStart_6386473 : Nat := 118140960795 + 6386473 * 2 ^ 59
def prefixEnd_6386473 : Nat := 4983230072969 + 3 ^ 40 * 6386473 * 2
def baseEnd_6386473 : Nat := 364370037329077403190739

theorem tailTrace_6386473 : CollatzResearch.WordTrace tailWord_6386473 prefixEnd_6386473 364370037329077403190739 := by
  unfold tailWord_6386473
  simp only [CollatzResearch.WordTrace]
  refine ⟨232933806591906518596636073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155289204394604345731090715 232933806591906518596636073)
  ·
    refine ⟨174700354943929888947477055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232933806591906518596636073 174700354943929888947477055)
    ·
      refine ⟨262050532415894833421215583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174700354943929888947477055 262050532415894833421215583)
      ·
        refine ⟨393075798623842250131823375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262050532415894833421215583 393075798623842250131823375)
        ·
          refine ⟨589613697935763375197735063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393075798623842250131823375 589613697935763375197735063)
          ·
            refine ⟨884420546903645062796602595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589613697935763375197735063 884420546903645062796602595)
            ·
              refine ⟨1326630820355467594194903893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884420546903645062796602595 1326630820355467594194903893)
              ·
                refine ⟨7773227463020317934735765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1326630820355467594194903893 7773227463020317934735765)
                ·
                  refine ⟨364370037329077403190739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7773227463020317934735765 364370037329077403190739)
                  ·
                    rfl

theorem cell23_6386473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_6386473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386473 prefixEnd_6386473 := by exact prefixLift 6386473
  have htrace : WordTrace (prefixWord ++ tailWord_6386473) baseStart_6386473 baseEnd_6386473 := by
    simpa [prefixWord, tailWord_6386473, baseEnd_6386473] using wordTrace_append hprefix tailTrace_6386473
  have hstable : (prefixWord ++ tailWord_6386473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386473).length < 2 ^ (prefixWord ++ tailWord_6386473).sum := by decide
  have hdescent : baseEnd_6386473 < baseStart_6386473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386484 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_6386484 : Nat := 118140960795 + 6386484 * 2 ^ 59
def prefixEnd_6386484 : Nat := 4983230072969 + 3 ^ 40 * 6386484 * 2
def baseEnd_6386484 : Nat := 3279335984248896085679101

theorem tailTrace_6386484 : CollatzResearch.WordTrace tailWord_6386484 prefixEnd_6386484 3279335984248896085679101 := by
  unfold tailWord_6386484
  simp only [CollatzResearch.WordTrace]
  refine ⟨116467103897433333737643253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155289471863244444983524337 116467103897433333737643253)
  ·
    refine ⟨10918790990384375037904055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116467103897433333737643253 10918790990384375037904055)
    ·
      refine ⟨16378186485576562556856083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10918790990384375037904055 16378186485576562556856083)
      ·
        refine ⟨24567279728364843835284125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378186485576562556856083 24567279728364843835284125)
        ·
          refine ⟨9212729898136816438231547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24567279728364843835284125 9212729898136816438231547)
          ·
            refine ⟨13819094847205224657347321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9212729898136816438231547 13819094847205224657347321)
            ·
              refine ⟨10364321135403918493010491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13819094847205224657347321 10364321135403918493010491)
              ·
                refine ⟨15546481703105877739515737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10364321135403918493010491 15546481703105877739515737)
                ·
                  refine ⟨11659861277329408304636803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15546481703105877739515737 11659861277329408304636803)
                  ·
                    refine ⟨17489791915994112456955205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11659861277329408304636803 17489791915994112456955205)
                    ·
                      refine ⟨3279335984248896085679101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17489791915994112456955205 3279335984248896085679101)
                      ·
                        rfl

theorem cell23_6386484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_6386484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386484 prefixEnd_6386484 := by exact prefixLift 6386484
  have htrace : WordTrace (prefixWord ++ tailWord_6386484) baseStart_6386484 baseEnd_6386484 := by
    simpa [prefixWord, tailWord_6386484, baseEnd_6386484] using wordTrace_append hprefix tailTrace_6386484
  have hstable : (prefixWord ++ tailWord_6386484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386484).length < 2 ^ (prefixWord ++ tailWord_6386484).sum := by decide
  have hdescent : baseEnd_6386484 < baseStart_6386484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386517 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_6386517 : Nat := 118140960795 + 6386517 * 2 ^ 59
def prefixEnd_6386517 : Nat := 4983230072969 + 3 ^ 40 * 6386517 * 2
def baseEnd_6386517 : Nat := 3279352929110494456566449

theorem tailTrace_6386517 : CollatzResearch.WordTrace tailWord_6386517 prefixEnd_6386517 3279352929110494456566449 := by
  unfold tailWord_6386517
  simp only [CollatzResearch.WordTrace]
  refine ⟨232935411403747114111237805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155290274269164742740825203 232935411403747114111237805)
  ·
    refine ⟨87350779276405167791714177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232935411403747114111237805 87350779276405167791714177)
    ·
      refine ⟨65513084457303875843785633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87350779276405167791714177 65513084457303875843785633)
      ·
        refine ⟨49134813342977906882839225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65513084457303875843785633 49134813342977906882839225)
        ·
          refine ⟨36851110007233430162129419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49134813342977906882839225 36851110007233430162129419)
          ·
            refine ⟨55276665010850145243194129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36851110007233430162129419 55276665010850145243194129)
            ·
              refine ⟨41457498758137608932395597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55276665010850145243194129 41457498758137608932395597)
              ·
                refine ⟨15546562034301603349648349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41457498758137608932395597 15546562034301603349648349)
                ·
                  refine ⟨5829960762863101256118131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15546562034301603349648349 5829960762863101256118131)
                  ·
                    refine ⟨8744941144294651884177197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5829960762863101256118131 8744941144294651884177197)
                    ·
                      refine ⟨3279352929110494456566449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8744941144294651884177197 3279352929110494456566449)
                      ·
                        rfl

theorem cell23_6386517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_6386517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386517 prefixEnd_6386517 := by exact prefixLift 6386517
  have htrace : WordTrace (prefixWord ++ tailWord_6386517) baseStart_6386517 baseEnd_6386517 := by
    simpa [prefixWord, tailWord_6386517, baseEnd_6386517] using wordTrace_append hprefix tailTrace_6386517
  have hstable : (prefixWord ++ tailWord_6386517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386517).length < 2 ^ (prefixWord ++ tailWord_6386517).sum := by decide
  have hdescent : baseEnd_6386517 < baseStart_6386517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386540 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_6386540 : Nat := 118140960795 + 6386540 * 2 ^ 59
def prefixEnd_6386540 : Nat := 4983230072969 + 3 ^ 40 * 6386540 * 2
def baseEnd_6386540 : Nat := 3279364739165547866578843

theorem tailTrace_6386540 : CollatzResearch.WordTrace tailWord_6386540 prefixEnd_6386540 3279364739165547866578843 := by
  unfold tailWord_6386540
  simp only [CollatzResearch.WordTrace]
  refine ⟨116468125141331894519662537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155290833521775859359550049 116468125141331894519662537)
  ·
    refine ⟨87351093855998920889746903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116468125141331894519662537 87351093855998920889746903)
    ·
      refine ⟨131026640783998381334620355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87351093855998920889746903 131026640783998381334620355)
      ·
        refine ⟨196539961175997572001930533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131026640783998381334620355 196539961175997572001930533)
        ·
          refine ⟨36851242720499544750361975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196539961175997572001930533 36851242720499544750361975)
          ·
            refine ⟨55276864080749317125542963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36851242720499544750361975 55276864080749317125542963)
            ·
              refine ⟨82915296121123975688314445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55276864080749317125542963 82915296121123975688314445)
              ·
                refine ⟨31093236045421490883117917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82915296121123975688314445 31093236045421490883117917)
                ·
                  refine ⟨11659963517033059081169219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31093236045421490883117917 11659963517033059081169219)
                  ·
                    refine ⟨17489945275549588621753829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11659963517033059081169219 17489945275549588621753829)
                    ·
                      refine ⟨3279364739165547866578843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17489945275549588621753829 3279364739165547866578843)
                      ·
                        rfl

theorem cell23_6386540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_6386540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386540 prefixEnd_6386540 := by exact prefixLift 6386540
  have htrace : WordTrace (prefixWord ++ tailWord_6386540) baseStart_6386540 baseEnd_6386540 := by
    simpa [prefixWord, tailWord_6386540, baseEnd_6386540] using wordTrace_append hprefix tailTrace_6386540
  have hstable : (prefixWord ++ tailWord_6386540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386540).length < 2 ^ (prefixWord ++ tailWord_6386540).sum := by decide
  have hdescent : baseEnd_6386540 < baseStart_6386540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386560 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_6386560 : Nat := 118140960795 + 6386560 * 2 ^ 59
def prefixEnd_6386560 : Nat := 4983230072969 + 3 ^ 40 * 6386560 * 2
def baseEnd_6386560 : Nat := 3279375008778637788328751

theorem tailTrace_6386560 : CollatzResearch.WordTrace tailWord_6386560 prefixEnd_6386560 3279375008778637788328751 := by
  unfold tailWord_6386560
  simp only [CollatzResearch.WordTrace]
  refine ⟨116468489871295666227526567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155291319828394221636702089 116468489871295666227526567)
  ·
    refine ⟨174702734806943499341289851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116468489871295666227526567 174702734806943499341289851)
    ·
      refine ⟨262054102210415249011934777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174702734806943499341289851 262054102210415249011934777)
      ·
        refine ⟨196540576657811436758951083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262054102210415249011934777 196540576657811436758951083)
        ·
          refine ⟨294810864986717155138426625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196540576657811436758951083 294810864986717155138426625)
          ·
            refine ⟨221108148740037866353819969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294810864986717155138426625 221108148740037866353819969)
            ·
              refine ⟨165831111555028399765364977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221108148740037866353819969 165831111555028399765364977)
              ·
                refine ⟨124373333666271299824023733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165831111555028399765364977 124373333666271299824023733)
                ·
                  refine ⟨11660000031212934358502225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124373333666271299824023733 11660000031212934358502225)
                  ·
                    refine ⟨8745000023409700768876669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11660000031212934358502225 8745000023409700768876669)
                    ·
                      refine ⟨3279375008778637788328751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8745000023409700768876669 3279375008778637788328751)
                      ·
                        rfl

theorem cell23_6386560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_6386560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386560 prefixEnd_6386560 := by exact prefixLift 6386560
  have htrace : WordTrace (prefixWord ++ tailWord_6386560) baseStart_6386560 baseEnd_6386560 := by
    simpa [prefixWord, tailWord_6386560, baseEnd_6386560] using wordTrace_append hprefix tailTrace_6386560
  have hstable : (prefixWord ++ tailWord_6386560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386560).length < 2 ^ (prefixWord ++ tailWord_6386560).sum := by decide
  have hdescent : baseEnd_6386560 < baseStart_6386560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386563 : List Nat := [1, 1, 1, 3, 4, 1, 12]
def baseStart_6386563 : Nat := 118140960795 + 6386563 * 2 ^ 59
def prefixEnd_6386563 : Nat := 4983230072969 + 3 ^ 40 * 6386563 * 2
def baseEnd_6386563 : Nat := 40486130237291373785077

theorem tailTrace_6386563 : CollatzResearch.WordTrace tailWord_6386563 prefixEnd_6386563 40486130237291373785077 := by
  unfold tailWord_6386563
  simp only [CollatzResearch.WordTrace]
  refine ⟨232937089161580463967412343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155291392774386975978274895 232937089161580463967412343)
  ·
    refine ⟨349405633742370695951118515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232937089161580463967412343 349405633742370695951118515)
    ·
      refine ⟨524108450613556043926677773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349405633742370695951118515 524108450613556043926677773)
      ·
        refine ⟨196540668980083516472504165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524108450613556043926677773 196540668980083516472504165)
        ·
          refine ⟨36851375433765659338594531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196540668980083516472504165 36851375433765659338594531)
          ·
            refine ⟨55277063150648489007891797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36851375433765659338594531 55277063150648489007891797)
            ·
              refine ⟨40486130237291373785077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 55277063150648489007891797 40486130237291373785077)
              ·
                rfl

theorem cell23_6386563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 12].length) (baseStart_6386563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386563 prefixEnd_6386563 := by exact prefixLift 6386563
  have htrace : WordTrace (prefixWord ++ tailWord_6386563) baseStart_6386563 baseEnd_6386563 := by
    simpa [prefixWord, tailWord_6386563, baseEnd_6386563] using wordTrace_append hprefix tailTrace_6386563
  have hstable : (prefixWord ++ tailWord_6386563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386563).length < 2 ^ (prefixWord ++ tailWord_6386563).sum := by decide
  have hdescent : baseEnd_6386563 < baseStart_6386563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386567 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 4, 4]
def baseStart_6386567 : Nat := 118140960795 + 6386567 * 2 ^ 59
def prefixEnd_6386567 : Nat := 4983230072969 + 3 ^ 40 * 6386567 * 2
def baseEnd_6386567 : Nat := 1093126201047739753647073

theorem tailTrace_6386567 : CollatzResearch.WordTrace tailWord_6386567 prefixEnd_6386567 1093126201047739753647073 := by
  unfold tailWord_6386567
  simp only [CollatzResearch.WordTrace]
  refine ⟨232937235053565972650557955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155291490035710648433705303 232937235053565972650557955)
  ·
    refine ⟨349405852580348958975836933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232937235053565972650557955 349405852580348958975836933)
    ·
      refine ⟨65513597358815429807969425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349405852580348958975836933 65513597358815429807969425)
      ·
        refine ⟨49135198019111572355977069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65513597358815429807969425 49135198019111572355977069)
        ·
          refine ⟨18425699257166839633491401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49135198019111572355977069 18425699257166839633491401)
          ·
            refine ⟨13819274442875129725118551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18425699257166839633491401 13819274442875129725118551)
            ·
              refine ⟨20728911664312694587677827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13819274442875129725118551 20728911664312694587677827)
              ·
                refine ⟨31093367496469041881516741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20728911664312694587677827 31093367496469041881516741)
                ·
                  refine ⟨5830006405587945352784389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31093367496469041881516741 5830006405587945352784389)
                  ·
                    refine ⟨1093126201047739753647073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5830006405587945352784389 1093126201047739753647073)
                    ·
                      rfl

theorem cell23_6386567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_6386567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386567 prefixEnd_6386567 := by exact prefixLift 6386567
  have htrace : WordTrace (prefixWord ++ tailWord_6386567) baseStart_6386567 baseEnd_6386567 := by
    simpa [prefixWord, tailWord_6386567, baseEnd_6386567] using wordTrace_append hprefix tailTrace_6386567
  have hstable : (prefixWord ++ tailWord_6386567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386567).length < 2 ^ (prefixWord ++ tailWord_6386567).sum := by decide
  have hdescent : baseEnd_6386567 < baseStart_6386567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386580 : List Nat := [2, 4, 2, 1, 1, 1, 2, 10]
def baseStart_6386580 : Nat := 118140960795 + 6386580 * 2 ^ 59
def prefixEnd_6386580 : Nat := 4983230072969 + 3 ^ 40 * 6386580 * 2
def baseEnd_6386580 : Nat := 121458714014508433706617

theorem tailTrace_6386580 : CollatzResearch.WordTrace tailWord_6386580 prefixEnd_6386580 121458714014508433706617 := by
  unfold tailWord_6386580
  simp only [CollatzResearch.WordTrace]
  refine ⟨116468854601259437935390597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155291806135012583913854129 116468854601259437935390597)
  ·
    refine ⟨21837910237736144612885737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116468854601259437935390597 21837910237736144612885737)
    ·
      refine ⟨16378432678302108459664303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21837910237736144612885737 16378432678302108459664303)
      ·
        refine ⟨24567649017453162689496455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378432678302108459664303 24567649017453162689496455)
        ·
          refine ⟨36851473526179744034244683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24567649017453162689496455 36851473526179744034244683)
          ·
            refine ⟨55277210289269616051367025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36851473526179744034244683 55277210289269616051367025)
            ·
              refine ⟨41457907716952212038525269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55277210289269616051367025 41457907716952212038525269)
              ·
                refine ⟨121458714014508433706617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41457907716952212038525269 121458714014508433706617)
                ·
                  rfl

theorem cell23_6386580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 10].length) (baseStart_6386580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386580 prefixEnd_6386580 := by exact prefixLift 6386580
  have htrace : WordTrace (prefixWord ++ tailWord_6386580) baseStart_6386580 baseEnd_6386580 := by
    simpa [prefixWord, tailWord_6386580, baseEnd_6386580] using wordTrace_append hprefix tailTrace_6386580
  have hstable : (prefixWord ++ tailWord_6386580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386580).length < 2 ^ (prefixWord ++ tailWord_6386580).sum := by decide
  have hdescent : baseEnd_6386580 < baseStart_6386580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386594 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_6386594 : Nat := 118140960795 + 6386594 * 2 ^ 59
def prefixEnd_6386594 : Nat := 4983230072969 + 3 ^ 40 * 6386594 * 2
def baseEnd_6386594 : Nat := 3279392467120890655303595

theorem tailTrace_6386594 : CollatzResearch.WordTrace tailWord_6386594 prefixEnd_6386594 3279392467120890655303595 := by
  unfold tailWord_6386594
  simp only [CollatzResearch.WordTrace]
  refine ⟨58234554956117039065447709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155292146549645437507860557 58234554956117039065447709)
  ·
    refine ⟨21837958108543889649542891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58234554956117039065447709 21837958108543889649542891)
    ·
      refine ⟨32756937162815834474314337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21837958108543889649542891 32756937162815834474314337)
      ·
        refine ⟨24567702872111875855735753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32756937162815834474314337 24567702872111875855735753)
        ·
          refine ⟨18425777154083906891801815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24567702872111875855735753 18425777154083906891801815)
          ·
            refine ⟨27638665731125860337702723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18425777154083906891801815 27638665731125860337702723)
            ·
              refine ⟨41457998596688790506554085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27638665731125860337702723 41457998596688790506554085)
              ·
                refine ⟨7773374736879148219978891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41457998596688790506554085 7773374736879148219978891)
                ·
                  refine ⟨11660062105318722329968337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773374736879148219978891 11660062105318722329968337)
                  ·
                    refine ⟨8745046578989041747476253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11660062105318722329968337 8745046578989041747476253)
                    ·
                      refine ⟨3279392467120890655303595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8745046578989041747476253 3279392467120890655303595)
                      ·
                        rfl

theorem cell23_6386594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_6386594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386594 prefixEnd_6386594 := by exact prefixLift 6386594
  have htrace : WordTrace (prefixWord ++ tailWord_6386594) baseStart_6386594 baseEnd_6386594 := by
    simpa [prefixWord, tailWord_6386594, baseEnd_6386594] using wordTrace_append hprefix tailTrace_6386594
  have hstable : (prefixWord ++ tailWord_6386594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386594).length < 2 ^ (prefixWord ++ tailWord_6386594).sum := by decide
  have hdescent : baseEnd_6386594 < baseStart_6386594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386660 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_6386660 : Nat := 118140960795 + 6386660 * 2 ^ 59
def prefixEnd_6386660 : Nat := 4983230072969 + 3 ^ 40 * 6386660 * 2
def baseEnd_6386660 : Nat := 3279426356844087397078291

theorem tailTrace_6386660 : CollatzResearch.WordTrace tailWord_6386660 prefixEnd_6386660 3279426356844087397078291 := by
  unfold tailWord_6386660
  simp only [CollatzResearch.WordTrace]
  refine ⟨116470313521114524766846717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155293751361486033022462289 116470313521114524766846717)
  ·
    refine ⟨43676367570417946787567519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116470313521114524766846717 43676367570417946787567519)
    ·
      refine ⟨65514551355626920181351279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43676367570417946787567519 65514551355626920181351279)
      ·
        refine ⟨98271827033440380272026919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65514551355626920181351279 98271827033440380272026919)
        ·
          refine ⟨147407740550160570408040379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98271827033440380272026919 147407740550160570408040379)
          ·
            refine ⟨221111610825240855612060569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147407740550160570408040379 221111610825240855612060569)
            ·
              refine ⟨165833708118930641709045427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221111610825240855612060569 165833708118930641709045427)
              ·
                refine ⟨248750562178395962563568141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165833708118930641709045427 248750562178395962563568141)
                ·
                  refine ⟨93281460816898485961338053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248750562178395962563568141 93281460816898485961338053)
                  ·
                    refine ⟨17490273903168466117750885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93281460816898485961338053 17490273903168466117750885)
                    ·
                      refine ⟨3279426356844087397078291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17490273903168466117750885 3279426356844087397078291)
                      ·
                        rfl

theorem cell23_6386660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_6386660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386660 prefixEnd_6386660 := by exact prefixLift 6386660
  have htrace : WordTrace (prefixWord ++ tailWord_6386660) baseStart_6386660 baseEnd_6386660 := by
    simpa [prefixWord, tailWord_6386660, baseEnd_6386660] using wordTrace_append hprefix tailTrace_6386660
  have hstable : (prefixWord ++ tailWord_6386660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386660).length < 2 ^ (prefixWord ++ tailWord_6386660).sum := by decide
  have hdescent : baseEnd_6386660 < baseStart_6386660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386664 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_6386664 : Nat := 118140960795 + 6386664 * 2 ^ 59
def prefixEnd_6386664 : Nat := 4983230072969 + 3 ^ 40 * 6386664 * 2
def baseEnd_6386664 : Nat := 3279428410766705381428273

theorem tailTrace_6386664 : CollatzResearch.WordTrace tailWord_6386664 prefixEnd_6386664 3279428410766705381428273 := by
  unfold tailWord_6386664
  simp only [CollatzResearch.WordTrace]
  refine ⟨116470386467107279108419523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155293848622809705477892697 116470386467107279108419523)
  ·
    refine ⟨174705579700660918662629285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116470386467107279108419523 174705579700660918662629285)
    ·
      refine ⟨32757296193873922249242991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174705579700660918662629285 32757296193873922249242991)
      ·
        refine ⟨49135944290810883373864487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32757296193873922249242991 49135944290810883373864487)
        ·
          refine ⟨73703916436216325060796731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49135944290810883373864487 73703916436216325060796731)
          ·
            refine ⟨110555874654324487591195097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73703916436216325060796731 110555874654324487591195097)
            ·
              refine ⟨82916905990743365693396323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110555874654324487591195097 82916905990743365693396323)
              ·
                refine ⟨124375358986115048540094485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82916905990743365693396323 124375358986115048540094485)
                ·
                  refine ⟨5830094952474142900316929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124375358986115048540094485 5830094952474142900316929)
                  ·
                    refine ⟨4372571214355607175237697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5830094952474142900316929 4372571214355607175237697)
                    ·
                      refine ⟨3279428410766705381428273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372571214355607175237697 3279428410766705381428273)
                      ·
                        rfl

theorem cell23_6386664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_6386664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386664 prefixEnd_6386664 := by exact prefixLift 6386664
  have htrace : WordTrace (prefixWord ++ tailWord_6386664) baseStart_6386664 baseEnd_6386664 := by
    simpa [prefixWord, tailWord_6386664, baseEnd_6386664] using wordTrace_append hprefix tailTrace_6386664
  have hstable : (prefixWord ++ tailWord_6386664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386664).length < 2 ^ (prefixWord ++ tailWord_6386664).sum := by decide
  have hdescent : baseEnd_6386664 < baseStart_6386664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386681 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 2, 2, 2]
def baseStart_6386681 : Nat := 118140960795 + 6386681 * 2 ^ 59
def prefixEnd_6386681 : Nat := 4983230072969 + 3 ^ 40 * 6386681 * 2
def baseEnd_6386681 : Nat := 3279437139937831814915695

theorem tailTrace_6386681 : CollatzResearch.WordTrace tailWord_6386681 prefixEnd_6386681 3279437139937831814915695 := by
  unfold tailWord_6386681
  simp only [CollatzResearch.WordTrace]
  refine ⟨232941392975152970120207897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155294261983435313413471931 232941392975152970120207897)
  ·
    refine ⟨174706044731364727590155923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232941392975152970120207897 174706044731364727590155923)
    ·
      refine ⟨262059067097047091385233885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174706044731364727590155923 262059067097047091385233885)
      ·
        refine ⟨98272150161392659269462707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262059067097047091385233885 98272150161392659269462707)
        ·
          refine ⟨147408225242088988904194061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98272150161392659269462707 147408225242088988904194061)
          ·
            refine ⟨55278084465783370839072773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147408225242088988904194061 55278084465783370839072773)
            ·
              refine ⟨10364640837334382032326145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55278084465783370839072773 10364640837334382032326145)
              ·
                refine ⟨7773480628000786524244609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10364640837334382032326145 7773480628000786524244609)
                ·
                  refine ⟨5830110471000589893183457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7773480628000786524244609 5830110471000589893183457)
                  ·
                    refine ⟨4372582853250442419887593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5830110471000589893183457 4372582853250442419887593)
                    ·
                      refine ⟨3279437139937831814915695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372582853250442419887593 3279437139937831814915695)
                      ·
                        rfl

theorem cell23_6386681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_6386681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386681 prefixEnd_6386681 := by exact prefixLift 6386681
  have htrace : WordTrace (prefixWord ++ tailWord_6386681) baseStart_6386681 baseEnd_6386681 := by
    simpa [prefixWord, tailWord_6386681, baseEnd_6386681] using wordTrace_append hprefix tailTrace_6386681
  have hstable : (prefixWord ++ tailWord_6386681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386681).length < 2 ^ (prefixWord ++ tailWord_6386681).sum := by decide
  have hdescent : baseEnd_6386681 < baseStart_6386681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386707 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 4, 5, 2]
def baseStart_6386707 : Nat := 118140960795 + 6386707 * 2 ^ 59
def prefixEnd_6386707 : Nat := 4983230072969 + 3 ^ 40 * 6386707 * 2
def baseEnd_6386707 : Nat := 3279450490434848713190575

theorem tailTrace_6386707 : CollatzResearch.WordTrace tailWord_6386707 prefixEnd_6386707 3279450490434848713190575 := by
  unfold tailWord_6386707
  simp only [CollatzResearch.WordTrace]
  refine ⟨232942341273058776560654375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155294894182039184373769583 232942341273058776560654375)
  ·
    refine ⟨349413511909588164840981563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232942341273058776560654375 349413511909588164840981563)
    ·
      refine ⟨524120267864382247261472345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349413511909588164840981563 524120267864382247261472345)
      ·
        refine ⟨393090200898286685446104259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524120267864382247261472345 393090200898286685446104259)
        ·
          refine ⟨589635301347430028169156389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393090200898286685446104259 589635301347430028169156389)
          ·
            refine ⟨110556619002643130281716823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 589635301347430028169156389 110556619002643130281716823)
            ·
              refine ⟨165834928503964695422575235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110556619002643130281716823 165834928503964695422575235)
              ·
                refine ⟨248752392755947043133862853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165834928503964695422575235 248752392755947043133862853)
                ·
                  refine ⟨46641073641740070587599285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248752392755947043133862853 46641073641740070587599285)
                  ·
                    refine ⟨4372600653913131617587433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46641073641740070587599285 4372600653913131617587433)
                    ·
                      refine ⟨3279450490434848713190575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372600653913131617587433 3279450490434848713190575)
                      ·
                        rfl

theorem cell23_6386707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 5, 2].length) (baseStart_6386707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386707 prefixEnd_6386707 := by exact prefixLift 6386707
  have htrace : WordTrace (prefixWord ++ tailWord_6386707) baseStart_6386707 baseEnd_6386707 := by
    simpa [prefixWord, tailWord_6386707, baseEnd_6386707] using wordTrace_append hprefix tailTrace_6386707
  have hstable : (prefixWord ++ tailWord_6386707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386707).length < 2 ^ (prefixWord ++ tailWord_6386707).sum := by decide
  have hdescent : baseEnd_6386707 < baseStart_6386707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386737 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6386737 : Nat := 118140960795 + 6386737 * 2 ^ 59
def prefixEnd_6386737 : Nat := 4983230072969 + 3 ^ 40 * 6386737 * 2
def baseEnd_6386737 : Nat := 3279465894854483595815437

theorem tailTrace_6386737 : CollatzResearch.WordTrace tailWord_6386737 prefixEnd_6386737 3279465894854483595815437 := by
  unfold tailWord_6386737
  simp only [CollatzResearch.WordTrace]
  refine ⟨232943435462950091684246465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155295623641966727789497643 232943435462950091684246465)
  ·
    refine ⟨174707576597212568763184849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232943435462950091684246465 174707576597212568763184849)
    ·
      refine ⟨131030682447909426572388637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174707576597212568763184849 131030682447909426572388637)
      ·
        refine ⟨49136505917966034964645739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131030682447909426572388637 49136505917966034964645739)
        ·
          refine ⟨73704758876949052446968609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49136505917966034964645739 73704758876949052446968609)
          ·
            refine ⟨55278569157711789335226457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73704758876949052446968609 55278569157711789335226457)
            ·
              refine ⟨41458926868283842001419843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55278569157711789335226457 41458926868283842001419843)
              ·
                refine ⟨62188390302425763002129765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41458926868283842001419843 62188390302425763002129765)
                ·
                  refine ⟨11660323181704830562899331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62188390302425763002129765 11660323181704830562899331)
                  ·
                    refine ⟨17490484772557245844348997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11660323181704830562899331 17490484772557245844348997)
                    ·
                      refine ⟨3279465894854483595815437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17490484772557245844348997 3279465894854483595815437)
                      ·
                        rfl

theorem cell23_6386737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6386737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386737 prefixEnd_6386737 := by exact prefixLift 6386737
  have htrace : WordTrace (prefixWord ++ tailWord_6386737) baseStart_6386737 baseEnd_6386737 := by
    simpa [prefixWord, tailWord_6386737, baseEnd_6386737] using wordTrace_append hprefix tailTrace_6386737
  have hstable : (prefixWord ++ tailWord_6386737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386737).length < 2 ^ (prefixWord ++ tailWord_6386737).sum := by decide
  have hdescent : baseEnd_6386737 < baseStart_6386737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386757 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_6386757 : Nat := 118140960795 + 6386757 * 2 ^ 59
def prefixEnd_6386757 : Nat := 4983230072969 + 3 ^ 40 * 6386757 * 2
def baseEnd_6386757 : Nat := 3279476164467573517565345

theorem tailTrace_6386757 : CollatzResearch.WordTrace tailWord_6386757 prefixEnd_6386757 3279476164467573517565345 := by
  unfold tailWord_6386757
  simp only [CollatzResearch.WordTrace]
  refine ⟨232944164922877635099974525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155296109948585090066649683 232944164922877635099974525)
  ·
    refine ⟨87354061846079113162490447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232944164922877635099974525 87354061846079113162490447)
    ·
      refine ⟨131031092769118669743735671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87354061846079113162490447 131031092769118669743735671)
      ·
        refine ⟨196546639153678004615603507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131031092769118669743735671 196546639153678004615603507)
        ·
          refine ⟨294819958730517006923405261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196546639153678004615603507 294819958730517006923405261)
          ·
            refine ⟨110557484523943877596276973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294819958730517006923405261 110557484523943877596276973)
            ·
              refine ⟨41459056696478954098603865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110557484523943877596276973 41459056696478954098603865)
              ·
                refine ⟨31094292522359215573952899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41459056696478954098603865 31094292522359215573952899)
                ·
                  refine ⟨46641438783538823360929349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31094292522359215573952899 46641438783538823360929349)
                  ·
                    refine ⟨8745269771913529380174253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46641438783538823360929349 8745269771913529380174253)
                    ·
                      refine ⟨3279476164467573517565345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8745269771913529380174253 3279476164467573517565345)
                      ·
                        rfl

theorem cell23_6386757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_6386757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386757 prefixEnd_6386757 := by exact prefixLift 6386757
  have htrace : WordTrace (prefixWord ++ tailWord_6386757) baseStart_6386757 baseEnd_6386757 := by
    simpa [prefixWord, tailWord_6386757, baseEnd_6386757] using wordTrace_append hprefix tailTrace_6386757
  have hstable : (prefixWord ++ tailWord_6386757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386757).length < 2 ^ (prefixWord ++ tailWord_6386757).sum := by decide
  have hdescent : baseEnd_6386757 < baseStart_6386757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386807 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 3, 5]
def baseStart_6386807 : Nat := 118140960795 + 6386807 * 2 ^ 59
def prefixEnd_6386807 : Nat := 4983230072969 + 3 ^ 40 * 6386807 * 2
def baseEnd_6386807 : Nat := 1093167279500099440646705

theorem tailTrace_6386807 : CollatzResearch.WordTrace tailWord_6386807 prefixEnd_6386807 1093167279500099440646705 := by
  unfold tailWord_6386807
  simp only [CollatzResearch.WordTrace]
  refine ⟨232945988572696493639294675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155297325715130995759529783 232945988572696493639294675)
  ·
    refine ⟨349418982859044740458942013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232945988572696493639294675 349418982859044740458942013)
    ·
      refine ⟨131032118572141777672103255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349418982859044740458942013 131032118572141777672103255)
      ·
        refine ⟨196548177858212666508154883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131032118572141777672103255 196548177858212666508154883)
        ·
          refine ⟨294822266787318999762232325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196548177858212666508154883 294822266787318999762232325)
          ·
            refine ⟨55279175022622312455418561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294822266787318999762232325 55279175022622312455418561)
            ·
              refine ⟨41459381266966734341563921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55279175022622312455418561 41459381266966734341563921)
              ·
                refine ⟨31094535950225050756172941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41459381266966734341563921 31094535950225050756172941)
                ·
                  refine ⟨11660450981334394033564853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31094535950225050756172941 11660450981334394033564853)
                  ·
                    refine ⟨1093167279500099440646705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11660450981334394033564853 1093167279500099440646705)
                    ·
                      rfl

theorem cell23_6386807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_6386807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386807 prefixEnd_6386807 := by exact prefixLift 6386807
  have htrace : WordTrace (prefixWord ++ tailWord_6386807) baseStart_6386807 baseEnd_6386807 := by
    simpa [prefixWord, tailWord_6386807, baseEnd_6386807] using wordTrace_append hprefix tailTrace_6386807
  have hstable : (prefixWord ++ tailWord_6386807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386807).length < 2 ^ (prefixWord ++ tailWord_6386807).sum := by decide
  have hdescent : baseEnd_6386807 < baseStart_6386807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386855 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6386855 : Nat := 118140960795 + 6386855 * 2 ^ 59
def prefixEnd_6386855 : Nat := 4983230072969 + 3 ^ 40 * 6386855 * 2
def baseEnd_6386855 : Nat := 3279526485571714134139895

theorem tailTrace_6386855 : CollatzResearch.WordTrace tailWord_6386855 prefixEnd_6386855 3279526485571714134139895 := by
  unfold tailWord_6386855
  simp only [CollatzResearch.WordTrace]
  refine ⟨232947739276522597837042019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155298492851015065224694679 232947739276522597837042019)
  ·
    refine ⟨349421608914783896755563029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232947739276522597837042019 349421608914783896755563029)
    ·
      refine ⟨16379137917880495160417017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 349421608914783896755563029 16379137917880495160417017)
      ·
        refine ⟨12284353438410371370312763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16379137917880495160417017 12284353438410371370312763)
        ·
          refine ⟨18426530157615557055469145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12284353438410371370312763 18426530157615557055469145)
          ·
            refine ⟨13819897618211667791601859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18426530157615557055469145 13819897618211667791601859)
            ·
              refine ⟨20729846427317501687402789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13819897618211667791601859 20729846427317501687402789)
              ·
                refine ⟨3886846205122031566388023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20729846427317501687402789 3886846205122031566388023)
                ·
                  refine ⟨5830269307683047349582035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886846205122031566388023 5830269307683047349582035)
                  ·
                    refine ⟨8745403961524571024373053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5830269307683047349582035 8745403961524571024373053)
                    ·
                      refine ⟨3279526485571714134139895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8745403961524571024373053 3279526485571714134139895)
                      ·
                        rfl

theorem cell23_6386855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6386855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386855 prefixEnd_6386855 := by exact prefixLift 6386855
  have htrace : WordTrace (prefixWord ++ tailWord_6386855) baseStart_6386855 baseEnd_6386855 := by
    simpa [prefixWord, tailWord_6386855, baseEnd_6386855] using wordTrace_append hprefix tailTrace_6386855
  have hstable : (prefixWord ++ tailWord_6386855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386855).length < 2 ^ (prefixWord ++ tailWord_6386855).sum := by decide
  have hdescent : baseEnd_6386855 < baseStart_6386855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386867 : List Nat := [1, 1, 1, 2, 3, 2, 5, 8]
def baseStart_6386867 : Nat := 118140960795 + 6386867 * 2 ^ 59
def prefixEnd_6386867 : Nat := 4983230072969 + 3 ^ 40 * 6386867 * 2
def baseEnd_6386867 : Nat := 121464172123687706932957

theorem tailTrace_6386867 : CollatzResearch.WordTrace tailWord_6386867 prefixEnd_6386867 121464172123687706932957 := by
  unfold tailWord_6386867
  simp only [CollatzResearch.WordTrace]
  refine ⟨232948176952479123886478855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155298784634986082590985903 232948176952479123886478855)
  ·
    refine ⟨349422265428718685829718283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232948176952479123886478855 349422265428718685829718283)
    ·
      refine ⟨524133398143078028744577425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349422265428718685829718283 524133398143078028744577425)
      ·
        refine ⟨393100048607308521558433069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524133398143078028744577425 393100048607308521558433069)
        ·
          refine ⟨147412518227740695584412401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393100048607308521558433069 147412518227740695584412401)
          ·
            refine ⟨110559388670805521688309301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147412518227740695584412401 110559388670805521688309301)
            ·
              refine ⟨10364942687888017658278997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110559388670805521688309301 10364942687888017658278997)
              ·
                refine ⟨121464172123687706932957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10364942687888017658278997 121464172123687706932957)
                ·
                  rfl

theorem cell23_6386867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 8].length) (baseStart_6386867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386867 prefixEnd_6386867 := by exact prefixLift 6386867
  have htrace : WordTrace (prefixWord ++ tailWord_6386867) baseStart_6386867 baseEnd_6386867 := by
    simpa [prefixWord, tailWord_6386867, baseEnd_6386867] using wordTrace_append hprefix tailTrace_6386867
  have hstable : (prefixWord ++ tailWord_6386867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386867).length < 2 ^ (prefixWord ++ tailWord_6386867).sum := by decide
  have hdescent : baseEnd_6386867 < baseStart_6386867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386878 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_6386878 : Nat := 118140960795 + 6386878 * 2 ^ 59
def prefixEnd_6386878 : Nat := 4983230072969 + 3 ^ 40 * 6386878 * 2
def baseEnd_6386878 : Nat := 3279538295626767544152289

theorem tailTrace_6386878 : CollatzResearch.WordTrace tailWord_6386878 prefixEnd_6386878 3279538295626767544152289 := by
  unfold tailWord_6386878
  simp only [CollatzResearch.WordTrace]
  refine ⟨29118572269429909095641161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155299052103626181843419525 29118572269429909095641161)
  ·
    refine ⟨21838929202072431821730871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29118572269429909095641161 21838929202072431821730871)
    ·
      refine ⟨32758393803108647732596307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21838929202072431821730871 32758393803108647732596307)
      ·
        refine ⟨49137590704662971598894461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32758393803108647732596307 49137590704662971598894461)
        ·
          refine ⟨18426596514248614349585423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49137590704662971598894461 18426596514248614349585423)
          ·
            refine ⟨27639894771372921524378135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18426596514248614349585423 27639894771372921524378135)
            ·
              refine ⟨41459842157059382286567203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27639894771372921524378135 41459842157059382286567203)
              ·
                refine ⟨62189763235589073429850805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41459842157059382286567203 62189763235589073429850805)
                ·
                  refine ⟨5830290303336475634048513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62189763235589073429850805 5830290303336475634048513)
                  ·
                    refine ⟨4372717727502356725536385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5830290303336475634048513 4372717727502356725536385)
                    ·
                      refine ⟨3279538295626767544152289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372717727502356725536385 3279538295626767544152289)
                      ·
                        rfl

theorem cell23_6386878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_6386878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386878 prefixEnd_6386878 := by exact prefixLift 6386878
  have htrace : WordTrace (prefixWord ++ tailWord_6386878) baseStart_6386878 baseEnd_6386878 := by
    simpa [prefixWord, tailWord_6386878, baseEnd_6386878] using wordTrace_append hprefix tailTrace_6386878
  have hstable : (prefixWord ++ tailWord_6386878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386878).length < 2 ^ (prefixWord ++ tailWord_6386878).sum := by decide
  have hdescent : baseEnd_6386878 < baseStart_6386878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386938 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2]
def baseStart_6386938 : Nat := 118140960795 + 6386938 * 2 ^ 59
def prefixEnd_6386938 : Nat := 4983230072969 + 3 ^ 40 * 6386938 * 2
def baseEnd_6386938 : Nat := 3279569104466037309402013

theorem tailTrace_6386938 : CollatzResearch.WordTrace tailWord_6386938 prefixEnd_6386938 3279569104466037309402013 := by
  unfold tailWord_6386938
  simp only [CollatzResearch.WordTrace]
  refine ⟨58237691633805475753078367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155300511023481268674875645 58237691633805475753078367)
  ·
    refine ⟨87356537450708213629617551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58237691633805475753078367 87356537450708213629617551)
    ·
      refine ⟨131034806176062320444426327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87356537450708213629617551 131034806176062320444426327)
      ·
        refine ⟨196552209264093480666639491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131034806176062320444426327 196552209264093480666639491)
        ·
          refine ⟨294828313896140220999959237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196552209264093480666639491 294828313896140220999959237)
          ·
            refine ⟨55280308855526291437492357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294828313896140220999959237 55280308855526291437492357)
            ·
              refine ⟨10365057910411179644529817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55280308855526291437492357 10365057910411179644529817)
              ·
                refine ⟨7773793432808384733397363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10365057910411179644529817 7773793432808384733397363)
                ·
                  refine ⟨11660690149212577100096045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773793432808384733397363 11660690149212577100096045)
                  ·
                    refine ⟨4372758805954716412536017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11660690149212577100096045 4372758805954716412536017)
                    ·
                      refine ⟨3279569104466037309402013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372758805954716412536017 3279569104466037309402013)
                      ·
                        rfl

theorem cell23_6386938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_6386938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386938 prefixEnd_6386938 := by exact prefixLift 6386938
  have htrace : WordTrace (prefixWord ++ tailWord_6386938) baseStart_6386938 baseEnd_6386938 := by
    simpa [prefixWord, tailWord_6386938, baseEnd_6386938] using wordTrace_append hprefix tailTrace_6386938
  have hstable : (prefixWord ++ tailWord_6386938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386938).length < 2 ^ (prefixWord ++ tailWord_6386938).sum := by decide
  have hdescent : baseEnd_6386938 < baseStart_6386938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386946 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_6386946 : Nat := 118140960795 + 6386946 * 2 ^ 59
def prefixEnd_6386946 : Nat := 4983230072969 + 3 ^ 40 * 6386946 * 2
def baseEnd_6386946 : Nat := 3279573212311273278101977

theorem tailTrace_6386946 : CollatzResearch.WordTrace tailWord_6386946 prefixEnd_6386946 3279573212311273278101977 := by
  unfold tailWord_6386946
  simp only [CollatzResearch.WordTrace]
  refine ⟨58237764579798230094651173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155300705546128613585736461 58237764579798230094651173)
  ·
    refine ⟨10919580858712168142747095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58237764579798230094651173 10919580858712168142747095)
    ·
      refine ⟨16379371288068252214120643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10919580858712168142747095 16379371288068252214120643)
      ·
        refine ⟨24569056932102378321180965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16379371288068252214120643 24569056932102378321180965)
        ·
          refine ⟨4606698174769195935221431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24569056932102378321180965 4606698174769195935221431)
          ·
            refine ⟨6910047262153793902832147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606698174769195935221431 6910047262153793902832147)
            ·
              refine ⟨10365070893230690854248221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6910047262153793902832147 10365070893230690854248221)
              ·
                refine ⟨3886901584961509070343083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10365070893230690854248221 3886901584961509070343083)
                ·
                  refine ⟨5830352377442263605514625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886901584961509070343083 5830352377442263605514625)
                  ·
                    refine ⟨4372764283081697704135969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5830352377442263605514625 4372764283081697704135969)
                    ·
                      refine ⟨3279573212311273278101977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372764283081697704135969 3279573212311273278101977)
                      ·
                        rfl

theorem cell23_6386946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_6386946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386946 prefixEnd_6386946 := by exact prefixLift 6386946
  have htrace : WordTrace (prefixWord ++ tailWord_6386946) baseStart_6386946 baseEnd_6386946 := by
    simpa [prefixWord, tailWord_6386946, baseEnd_6386946] using wordTrace_append hprefix tailTrace_6386946
  have hstable : (prefixWord ++ tailWord_6386946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386946).length < 2 ^ (prefixWord ++ tailWord_6386946).sum := by decide
  have hdescent : baseEnd_6386946 < baseStart_6386946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386954 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_6386954 : Nat := 118140960795 + 6386954 * 2 ^ 59
def prefixEnd_6386954 : Nat := 4983230072969 + 3 ^ 40 * 6386954 * 2
def baseEnd_6386954 : Nat := 3279577320156509246801939

theorem tailTrace_6386954 : CollatzResearch.WordTrace tailWord_6386954 prefixEnd_6386954 3279577320156509246801939 := by
  unfold tailWord_6386954
  simp only [CollatzResearch.WordTrace]
  refine ⟨58237837525790984436223979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155300900068775958496597277 58237837525790984436223979)
  ·
    refine ⟨87356756288686476654335969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58237837525790984436223979 87356756288686476654335969)
    ·
      refine ⟨65517567216514857490751977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87356756288686476654335969 65517567216514857490751977)
      ·
        refine ⟨49138175412386143118063983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65517567216514857490751977 49138175412386143118063983)
        ·
          refine ⟨73707263118579214677095975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49138175412386143118063983 73707263118579214677095975)
          ·
            refine ⟨110560894677868822015643963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73707263118579214677095975 110560894677868822015643963)
            ·
              refine ⟨165841342016803233023465945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110560894677868822015643963 165841342016803233023465945)
              ·
                refine ⟨124381006512602424767599459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165841342016803233023465945 124381006512602424767599459)
                ·
                  refine ⟨186571509768903637151399189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124381006512602424767599459 186571509768903637151399189)
                  ·
                    refine ⟨8745539520417357991471837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 186571509768903637151399189 8745539520417357991471837)
                    ·
                      refine ⟨3279577320156509246801939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8745539520417357991471837 3279577320156509246801939)
                      ·
                        rfl

theorem cell23_6386954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_6386954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386954 prefixEnd_6386954 := by exact prefixLift 6386954
  have htrace : WordTrace (prefixWord ++ tailWord_6386954) baseStart_6386954 baseEnd_6386954 := by
    simpa [prefixWord, tailWord_6386954, baseEnd_6386954] using wordTrace_append hprefix tailTrace_6386954
  have hstable : (prefixWord ++ tailWord_6386954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386954).length < 2 ^ (prefixWord ++ tailWord_6386954).sum := by decide
  have hdescent : baseEnd_6386954 < baseStart_6386954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6386968 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 4, 2, 2]
def baseStart_6386968 : Nat := 118140960795 + 6386968 * 2 ^ 59
def prefixEnd_6386968 : Nat := 4983230072969 + 3 ^ 40 * 6386968 * 2
def baseEnd_6386968 : Nat := 3279584508885672192026875

theorem tailTrace_6386968 : CollatzResearch.WordTrace tailWord_6386968 prefixEnd_6386968 3279584508885672192026875 := by
  unfold tailWord_6386968
  simp only [CollatzResearch.WordTrace]
  refine ⟨116475930362556609067952779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155301240483408812090603705 116475930362556609067952779)
  ·
    refine ⟨174713895543834913601929169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116475930362556609067952779 174713895543834913601929169)
    ·
      refine ⟨131035421657876185201446877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174713895543834913601929169 131035421657876185201446877)
      ·
        refine ⟨49138283121703569450542579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131035421657876185201446877 49138283121703569450542579)
        ·
          refine ⟨73707424682555354175813869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49138283121703569450542579 73707424682555354175813869)
          ·
            refine ⟨27640284255958257815930201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73707424682555354175813869 27640284255958257815930201)
            ·
              refine ⟨20730213191968693361947651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27640284255958257815930201 20730213191968693361947651)
              ·
                refine ⟨31095319787953040042921477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20730213191968693361947651 31095319787953040042921477)
                ·
                  refine ⟨5830372460241195008047777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31095319787953040042921477 5830372460241195008047777)
                  ·
                    refine ⟨4372779345180896256035833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5830372460241195008047777 4372779345180896256035833)
                    ·
                      refine ⟨3279584508885672192026875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372779345180896256035833 3279584508885672192026875)
                      ·
                        rfl

theorem cell23_6386968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_6386968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6386968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6386968 prefixEnd_6386968 := by exact prefixLift 6386968
  have htrace : WordTrace (prefixWord ++ tailWord_6386968) baseStart_6386968 baseEnd_6386968 := by
    simpa [prefixWord, tailWord_6386968, baseEnd_6386968] using wordTrace_append hprefix tailTrace_6386968
  have hstable : (prefixWord ++ tailWord_6386968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6386968).length < 2 ^ (prefixWord ++ tailWord_6386968).sum := by decide
  have hdescent : baseEnd_6386968 < baseStart_6386968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6386968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387081 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 8]
def baseStart_6387081 : Nat := 118140960795 + 6387081 * 2 ^ 59
def prefixEnd_6387081 : Nat := 4983230072969 + 3 ^ 40 * 6387081 * 2
def baseEnd_6387081 : Nat := 364404725799958916657095

theorem tailTrace_6387081 : CollatzResearch.WordTrace tailWord_6387081 prefixEnd_6387081 364404725799958916657095 := by
  unfold tailWord_6387081
  simp only [CollatzResearch.WordTrace]
  refine ⟨232955982173703838434769097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155303988115802558956512731 232955982173703838434769097)
  ·
    refine ⟨174716986630277878826076823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232955982173703838434769097 174716986630277878826076823)
    ·
      refine ⟨262075479945416818239115235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174716986630277878826076823 262075479945416818239115235)
      ·
        refine ⟨393113219918125227358672853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262075479945416818239115235 393113219918125227358672853)
        ·
          refine ⟨9213591091831060016218895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 393113219918125227358672853 9213591091831060016218895)
          ·
            refine ⟨13820386637746590024328343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9213591091831060016218895 13820386637746590024328343)
            ·
              refine ⟨20730579956619885036492515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13820386637746590024328343 20730579956619885036492515)
              ·
                refine ⟨31095869934929827554738773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20730579956619885036492515 31095869934929827554738773)
                ·
                  refine ⟨364404725799958916657095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31095869934929827554738773 364404725799958916657095)
                  ·
                    rfl

theorem cell23_6387081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_6387081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387081 prefixEnd_6387081 := by exact prefixLift 6387081
  have htrace : WordTrace (prefixWord ++ tailWord_6387081) baseStart_6387081 baseEnd_6387081 := by
    simpa [prefixWord, tailWord_6387081, baseEnd_6387081] using wordTrace_append hprefix tailTrace_6387081
  have hstable : (prefixWord ++ tailWord_6387081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387081).length < 2 ^ (prefixWord ++ tailWord_6387081).sum := by decide
  have hdescent : baseEnd_6387081 < baseStart_6387081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387084 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_6387084 : Nat := 118140960795 + 6387084 * 2 ^ 59
def prefixEnd_6387084 : Nat := 4983230072969 + 3 ^ 40 * 6387084 * 2
def baseEnd_6387084 : Nat := 3279644072641593738176341

theorem tailTrace_6387084 : CollatzResearch.WordTrace tailWord_6387084 prefixEnd_6387084 3279644072641593738176341 := by
  unfold tailWord_6387084
  simp only [CollatzResearch.WordTrace]
  refine ⟨116478045796346484973564153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155304061061795313298085537 116478045796346484973564153)
  ·
    refine ⟨87358534347259863730173115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116478045796346484973564153 87358534347259863730173115)
    ·
      refine ⟨131037801520889795595259673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87358534347259863730173115 131037801520889795595259673)
      ·
        refine ⟨98278351140667346696444755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131037801520889795595259673 98278351140667346696444755)
        ·
          refine ⟨147417526711001020044667133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98278351140667346696444755 147417526711001020044667133)
          ·
            refine ⟨55281572516625382516750175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147417526711001020044667133 55281572516625382516750175)
            ·
              refine ⟨82922358774938073775125263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55281572516625382516750175 82922358774938073775125263)
              ·
                refine ⟨124383538162407110662687895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82922358774938073775125263 124383538162407110662687895)
                ·
                  refine ⟨186575307243610665994031843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124383538162407110662687895 186575307243610665994031843)
                  ·
                    refine ⟨279862960865415998991047765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 186575307243610665994031843 279862960865415998991047765)
                    ·
                      refine ⟨3279644072641593738176341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 279862960865415998991047765 3279644072641593738176341)
                      ·
                        rfl

theorem cell23_6387084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_6387084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387084 prefixEnd_6387084 := by exact prefixLift 6387084
  have htrace : WordTrace (prefixWord ++ tailWord_6387084) baseStart_6387084 baseEnd_6387084 := by
    simpa [prefixWord, tailWord_6387084, baseEnd_6387084] using wordTrace_append hprefix tailTrace_6387084
  have hstable : (prefixWord ++ tailWord_6387084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387084).length < 2 ^ (prefixWord ++ tailWord_6387084).sum := by decide
  have hdescent : baseEnd_6387084 < baseStart_6387084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387098 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_6387098 : Nat := 118140960795 + 6387098 * 2 ^ 59
def prefixEnd_6387098 : Nat := 4983230072969 + 3 ^ 40 * 6387098 * 2
def baseEnd_6387098 : Nat := 364405695707861853711253

theorem tailTrace_6387098 : CollatzResearch.WordTrace tailWord_6387098 prefixEnd_6387098 364405695707861853711253 := by
  unfold tailWord_6387098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58239150553660562584534487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155304401476428166892091965 58239150553660562584534487)
  ·
    refine ⟨87358725830490843876801731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58239150553660562584534487 87358725830490843876801731)
    ·
      refine ⟨131038088745736265815202597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87358725830490843876801731 131038088745736265815202597)
      ·
        refine ⟨24569641639825549840350487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131038088745736265815202597 24569641639825549840350487)
        ·
          refine ⟨36854462459738324760525731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24569641639825549840350487 36854462459738324760525731)
          ·
            refine ⟨55281693689607487140788597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36854462459738324760525731 55281693689607487140788597)
            ·
              refine ⟨5182658783400701919448931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55281693689607487140788597 5182658783400701919448931)
              ·
                refine ⟨7773988175101052879173397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182658783400701919448931 7773988175101052879173397)
                ·
                  refine ⟨364405695707861853711253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7773988175101052879173397 364405695707861853711253)
                  ·
                    rfl

theorem cell23_6387098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_6387098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387098 prefixEnd_6387098 := by exact prefixLift 6387098
  have htrace : WordTrace (prefixWord ++ tailWord_6387098) baseStart_6387098 baseEnd_6387098 := by
    simpa [prefixWord, tailWord_6387098, baseEnd_6387098] using wordTrace_append hprefix tailTrace_6387098
  have hstable : (prefixWord ++ tailWord_6387098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387098).length < 2 ^ (prefixWord ++ tailWord_6387098).sum := by decide
  have hdescent : baseEnd_6387098 < baseStart_6387098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387151 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_6387151 : Nat := 118140960795 + 6387151 * 2 ^ 59
def prefixEnd_6387151 : Nat := 4983230072969 + 3 ^ 40 * 6387151 * 2
def baseEnd_6387151 : Nat := 3279678475845444976038533

theorem tailTrace_6387151 : CollatzResearch.WordTrace tailWord_6387151 prefixEnd_6387151 3279678475845444976038533 := by
  unfold tailWord_6387151
  simp only [CollatzResearch.WordTrace]
  refine ⟨232958535283450240389817307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155305690188966826926544871 232958535283450240389817307)
  ·
    refine ⟨349437802925175360584725961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232958535283450240389817307 349437802925175360584725961)
    ·
      refine ⟨262078352193881520438544471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349437802925175360584725961 262078352193881520438544471)
      ·
        refine ⟨393117528290822280657816707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262078352193881520438544471 393117528290822280657816707)
        ·
          refine ⟨589676292436233420986725061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393117528290822280657816707 589676292436233420986725061)
          ·
            refine ⟨110564304831793766435010949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 589676292436233420986725061 110564304831793766435010949)
            ·
              refine ⟨20730807155961331206564553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110564304831793766435010949 20730807155961331206564553)
              ·
                refine ⟨15548105366970998404923415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20730807155961331206564553 15548105366970998404923415)
                ·
                  refine ⟨23322158050456497607385123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15548105366970998404923415 23322158050456497607385123)
                  ·
                    refine ⟨34983237075684746411077685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23322158050456497607385123 34983237075684746411077685)
                    ·
                      refine ⟨3279678475845444976038533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34983237075684746411077685 3279678475845444976038533)
                      ·
                        rfl

theorem cell23_6387151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_6387151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387151 prefixEnd_6387151 := by exact prefixLift 6387151
  have htrace : WordTrace (prefixWord ++ tailWord_6387151) baseStart_6387151 baseEnd_6387151 := by
    simpa [prefixWord, tailWord_6387151, baseEnd_6387151] using wordTrace_append hprefix tailTrace_6387151
  have hstable : (prefixWord ++ tailWord_6387151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387151).length < 2 ^ (prefixWord ++ tailWord_6387151).sum := by decide
  have hdescent : baseEnd_6387151 < baseStart_6387151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387161 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_6387161 : Nat := 118140960795 + 6387161 * 2 ^ 59
def prefixEnd_6387161 : Nat := 4983230072969 + 3 ^ 40 * 6387161 * 2
def baseEnd_6387161 : Nat := 3279683610651989936913487

theorem tailTrace_6387161 : CollatzResearch.WordTrace tailWord_6387161 prefixEnd_6387161 3279683610651989936913487 := by
  unfold tailWord_6387161
  simp only [CollatzResearch.WordTrace]
  refine ⟨232958900013414012097681337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155305933342276008065120891 232958900013414012097681337)
  ·
    refine ⟨174719175010060509073261003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232958900013414012097681337 174719175010060509073261003)
    ·
      refine ⟨262078762515090763609891505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174719175010060509073261003 262078762515090763609891505)
      ·
        refine ⟨196559071886318072707418629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262078762515090763609891505 196559071886318072707418629)
        ·
          refine ⟨36854825978684638632640993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196559071886318072707418629 36854825978684638632640993)
          ·
            refine ⟨27641119484013478974480745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36854825978684638632640993 27641119484013478974480745)
            ·
              refine ⟨20730839613010109230860559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27641119484013478974480745 20730839613010109230860559)
              ·
                refine ⟨31096259419515163846290839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20730839613010109230860559 31096259419515163846290839)
                ·
                  refine ⟨46644389129272745769436259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31096259419515163846290839 46644389129272745769436259)
                  ·
                    refine ⟨69966583693909118654154389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46644389129272745769436259 69966583693909118654154389)
                    ·
                      refine ⟨3279683610651989936913487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69966583693909118654154389 3279683610651989936913487)
                      ·
                        rfl

theorem cell23_6387161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_6387161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387161 prefixEnd_6387161 := by exact prefixLift 6387161
  have htrace : WordTrace (prefixWord ++ tailWord_6387161) baseStart_6387161 baseEnd_6387161 := by
    simpa [prefixWord, tailWord_6387161, baseEnd_6387161] using wordTrace_append hprefix tailTrace_6387161
  have hstable : (prefixWord ++ tailWord_6387161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387161).length < 2 ^ (prefixWord ++ tailWord_6387161).sum := by decide
  have hdescent : baseEnd_6387161 < baseStart_6387161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387165 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_6387165 : Nat := 118140960795 + 6387165 * 2 ^ 59
def prefixEnd_6387165 : Nat := 4983230072969 + 3 ^ 40 * 6387165 * 2
def baseEnd_6387165 : Nat := 3279685664574607921263469

theorem tailTrace_6387165 : CollatzResearch.WordTrace tailWord_6387165 prefixEnd_6387165 3279685664574607921263469 := by
  unfold tailWord_6387165
  simp only [CollatzResearch.WordTrace]
  refine ⟨232959045905399520780826949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155306030603599680520551299 232959045905399520780826949)
  ·
    refine ⟨43679821107262410146405053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232959045905399520780826949 43679821107262410146405053)
    ·
      refine ⟨16379932915223403804901895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43679821107262410146405053 16379932915223403804901895)
      ·
        refine ⟨24569899372835105707352843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16379932915223403804901895 24569899372835105707352843)
        ·
          refine ⟨36854849059252658561029265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24569899372835105707352843 36854849059252658561029265)
          ·
            refine ⟨27641136794439493920771949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36854849059252658561029265 27641136794439493920771949)
            ·
              refine ⟨10365426297914810220289481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27641136794439493920771949 10365426297914810220289481)
              ·
                refine ⟨7774069723436107665217111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10365426297914810220289481 7774069723436107665217111)
                ·
                  refine ⟨11661104585154161497825667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774069723436107665217111 11661104585154161497825667)
                  ·
                    refine ⟨17491656877731242246738501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11661104585154161497825667 17491656877731242246738501)
                    ·
                      refine ⟨3279685664574607921263469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17491656877731242246738501 3279685664574607921263469)
                      ·
                        rfl

theorem cell23_6387165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_6387165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387165 prefixEnd_6387165 := by exact prefixLift 6387165
  have htrace : WordTrace (prefixWord ++ tailWord_6387165) baseStart_6387165 baseEnd_6387165 := by
    simpa [prefixWord, tailWord_6387165, baseEnd_6387165] using wordTrace_append hprefix tailTrace_6387165
  have hstable : (prefixWord ++ tailWord_6387165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387165).length < 2 ^ (prefixWord ++ tailWord_6387165).sum := by decide
  have hdescent : baseEnd_6387165 < baseStart_6387165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387168 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3]
def baseStart_6387168 : Nat := 118140960795 + 6387168 * 2 ^ 59
def prefixEnd_6387168 : Nat := 4983230072969 + 3 ^ 40 * 6387168 * 2
def baseEnd_6387168 : Nat := 3279687205016571409525955

theorem tailTrace_6387168 : CollatzResearch.WordTrace tailWord_6387168 prefixEnd_6387168 3279687205016571409525955 := by
  unfold tailWord_6387168
  simp only [CollatzResearch.WordTrace]
  refine ⟨116479577662194326146593079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155306103549592434862124105 116479577662194326146593079)
  ·
    refine ⟨174719366493291489219889619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116479577662194326146593079 174719366493291489219889619)
    ·
      refine ⟨262079049739937233829834429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174719366493291489219889619 262079049739937233829834429)
      ·
        refine ⟨98279643652476462686187911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262079049739937233829834429 98279643652476462686187911)
        ·
          refine ⟨147419465478714694029281867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98279643652476462686187911 147419465478714694029281867)
          ·
            refine ⟨221129198218072041043922801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147419465478714694029281867 221129198218072041043922801)
            ·
              refine ⟨165846898663554030782942101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221129198218072041043922801 165846898663554030782942101)
              ·
                refine ⟨7774073374854095192950411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165846898663554030782942101 7774073374854095192950411)
                ·
                  refine ⟨11661110062281142789425617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774073374854095192950411 11661110062281142789425617)
                  ·
                    refine ⟨8745832546710857092069213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11661110062281142789425617 8745832546710857092069213)
                    ·
                      refine ⟨3279687205016571409525955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8745832546710857092069213 3279687205016571409525955)
                      ·
                        rfl

theorem cell23_6387168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_6387168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387168 prefixEnd_6387168 := by exact prefixLift 6387168
  have htrace : WordTrace (prefixWord ++ tailWord_6387168) baseStart_6387168 baseEnd_6387168 := by
    simpa [prefixWord, tailWord_6387168, baseEnd_6387168] using wordTrace_append hprefix tailTrace_6387168
  have hstable : (prefixWord ++ tailWord_6387168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387168).length < 2 ^ (prefixWord ++ tailWord_6387168).sum := by decide
  have hdescent : baseEnd_6387168 < baseStart_6387168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387171 : List Nat := [1, 1, 1, 6, 2, 1, 2, 9]
def baseStart_6387171 : Nat := 118140960795 + 6387171 * 2 ^ 59
def prefixEnd_6387171 : Nat := 4983230072969 + 3 ^ 40 * 6387171 * 2
def baseEnd_6387171 : Nat := 121469953535501292510683

theorem tailTrace_6387171 : CollatzResearch.WordTrace tailWord_6387171 prefixEnd_6387171 121469953535501292510683 := by
  unfold tailWord_6387171
  simp only [CollatzResearch.WordTrace]
  refine ⟨232959264743377783805545367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155306176495585189203696911 232959264743377783805545367)
  ·
    refine ⟨349438897115066675708318051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232959264743377783805545367 349438897115066675708318051)
    ·
      refine ⟨524158345672600013562477077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349438897115066675708318051 524158345672600013562477077)
      ·
        refine ⟨24569922453403125635741113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 524158345672600013562477077 24569922453403125635741113)
        ·
          refine ⟨18427441840052344226805835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24569922453403125635741113 18427441840052344226805835)
          ·
            refine ⟨27641162760078516340208753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18427441840052344226805835 27641162760078516340208753)
            ·
              refine ⟨20730872070058887255156565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27641162760078516340208753 20730872070058887255156565)
              ·
                refine ⟨121469953535501292510683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20730872070058887255156565 121469953535501292510683)
                ·
                  rfl

theorem cell23_6387171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 9].length) (baseStart_6387171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387171 prefixEnd_6387171 := by exact prefixLift 6387171
  have htrace : WordTrace (prefixWord ++ tailWord_6387171) baseStart_6387171 baseEnd_6387171 := by
    simpa [prefixWord, tailWord_6387171, baseEnd_6387171] using wordTrace_append hprefix tailTrace_6387171
  have hstable : (prefixWord ++ tailWord_6387171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387171).length < 2 ^ (prefixWord ++ tailWord_6387171).sum := by decide
  have hdescent : baseEnd_6387171 < baseStart_6387171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387242 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6387242 : Nat := 118140960795 + 6387242 * 2 ^ 59
def prefixEnd_6387242 : Nat := 4983230072969 + 3 ^ 40 * 6387242 * 2
def baseEnd_6387242 : Nat := 3279725202585004120000615

theorem tailTrace_6387242 : CollatzResearch.WordTrace tailWord_6387242 prefixEnd_6387242 3279725202585004120000615 := by
  unfold tailWord_6387242
  simp only [CollatzResearch.WordTrace]
  refine ⟨58240463581530140732844995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155307902884080375287586653 58240463581530140732844995)
  ·
    refine ⟨87360695372295211099267493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58240463581530140732844995 87360695372295211099267493)
    ·
      refine ⟨16380130382305352081112655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87360695372295211099267493 16380130382305352081112655)
      ·
        refine ⟨24570195573458028121668983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16380130382305352081112655 24570195573458028121668983)
        ·
          refine ⟨36855293360187042182503475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24570195573458028121668983 36855293360187042182503475)
          ·
            refine ⟨55282940040280563273755213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36855293360187042182503475 55282940040280563273755213)
            ·
              refine ⟨20731102515105211227658205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55282940040280563273755213 20731102515105211227658205)
              ·
                refine ⟨7774163443164454210371827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20731102515105211227658205 7774163443164454210371827)
                ·
                  refine ⟨11661245164746681315557741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774163443164454210371827 11661245164746681315557741)
                  ·
                    refine ⟨4372966936780005493334153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11661245164746681315557741 4372966936780005493334153)
                    ·
                      refine ⟨3279725202585004120000615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4372966936780005493334153 3279725202585004120000615)
                      ·
                        rfl

theorem cell23_6387242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6387242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387242 prefixEnd_6387242 := by exact prefixLift 6387242
  have htrace : WordTrace (prefixWord ++ tailWord_6387242) baseStart_6387242 baseEnd_6387242 := by
    simpa [prefixWord, tailWord_6387242, baseEnd_6387242] using wordTrace_append hprefix tailTrace_6387242
  have hstable : (prefixWord ++ tailWord_6387242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387242).length < 2 ^ (prefixWord ++ tailWord_6387242).sum := by decide
  have hdescent : baseEnd_6387242 < baseStart_6387242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387312 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 5]
def baseStart_6387312 : Nat := 118140960795 + 6387312 * 2 ^ 59
def prefixEnd_6387312 : Nat := 4983230072969 + 3 ^ 40 * 6387312 * 2
def baseEnd_6387312 : Nat := 364417905136757649569477

theorem tailTrace_6387312 : CollatzResearch.WordTrace tailWord_6387312 prefixEnd_6387312 364417905136757649569477 := by
  unfold tailWord_6387312
  simp only [CollatzResearch.WordTrace]
  refine ⟨116482203717933482443214095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155309604957244643257618793 116482203717933482443214095)
  ·
    refine ⟨174723305576900223664821143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116482203717933482443214095 174723305576900223664821143)
    ·
      refine ⟨262084958365350335497231715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174723305576900223664821143 262084958365350335497231715)
      ·
        refine ⟨393127437548025503245847573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262084958365350335497231715 393127437548025503245847573)
        ·
          refine ⟨18427848635063695464649105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 393127437548025503245847573 18427848635063695464649105)
          ·
            refine ⟨13820886476297771598486829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18427848635063695464649105 13820886476297771598486829)
            ·
              refine ⟨5182832428611664349432561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13820886476297771598486829 5182832428611664349432561)
              ·
                refine ⟨3887124321458748262074421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5182832428611664349432561 3887124321458748262074421)
                ·
                  refine ⟨364417905136757649569477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3887124321458748262074421 364417905136757649569477)
                  ·
                    rfl

theorem cell23_6387312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 5].length) (baseStart_6387312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387312 prefixEnd_6387312 := by exact prefixLift 6387312
  have htrace : WordTrace (prefixWord ++ tailWord_6387312) baseStart_6387312 baseEnd_6387312 := by
    simpa [prefixWord, tailWord_6387312, baseEnd_6387312] using wordTrace_append hprefix tailTrace_6387312
  have hstable : (prefixWord ++ tailWord_6387312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387312).length < 2 ^ (prefixWord ++ tailWord_6387312).sum := by decide
  have hdescent : baseEnd_6387312 < baseStart_6387312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387328 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_6387328 : Nat := 118140960795 + 6387328 * 2 ^ 59
def prefixEnd_6387328 : Nat := 4983230072969 + 3 ^ 40 * 6387328 * 2
def baseEnd_6387328 : Nat := 3279769361921290783525219

theorem tailTrace_6387328 : CollatzResearch.WordTrace tailWord_6387328 prefixEnd_6387328 3279769361921290783525219 := by
  unfold tailWord_6387328
  simp only [CollatzResearch.WordTrace]
  refine ⟨116482495501904499809505319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155309994002539333079340425 116482495501904499809505319)
  ·
    refine ⟨174723743252856749714257979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116482495501904499809505319 174723743252856749714257979)
    ·
      refine ⟨262085614879285124571386969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174723743252856749714257979 262085614879285124571386969)
      ·
        refine ⟨196564211159463843428540227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262085614879285124571386969 196564211159463843428540227)
        ·
          refine ⟨294846316739195765142810341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196564211159463843428540227 294846316739195765142810341)
          ·
            refine ⟨55283684388599205964276939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294846316739195765142810341 55283684388599205964276939)
            ·
              refine ⟨82925526582898808946415409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55283684388599205964276939 82925526582898808946415409)
              ·
                refine ⟨62194144937174106709811557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82925526582898808946415409 62194144937174106709811557)
                ·
                  refine ⟨11661402175720145008089667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62194144937174106709811557 11661402175720145008089667)
                  ·
                    refine ⟨17492103263580217512134501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11661402175720145008089667 17492103263580217512134501)
                    ·
                      refine ⟨3279769361921290783525219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17492103263580217512134501 3279769361921290783525219)
                      ·
                        rfl

theorem cell23_6387328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_6387328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387328 prefixEnd_6387328 := by exact prefixLift 6387328
  have htrace : WordTrace (prefixWord ++ tailWord_6387328) baseStart_6387328 baseEnd_6387328 := by
    simpa [prefixWord, tailWord_6387328, baseEnd_6387328] using wordTrace_append hprefix tailTrace_6387328
  have hstable : (prefixWord ++ tailWord_6387328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387328).length < 2 ^ (prefixWord ++ tailWord_6387328).sum := by decide
  have hdescent : baseEnd_6387328 < baseStart_6387328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387365 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_6387365 : Nat := 118140960795 + 6387365 * 2 ^ 59
def prefixEnd_6387365 : Nat := 4983230072969 + 3 ^ 40 * 6387365 * 2
def baseEnd_6387365 : Nat := 3279788360705507138762549

theorem tailTrace_6387365 : CollatzResearch.WordTrace tailWord_6387365 prefixEnd_6387365 3279788360705507138762549 := by
  unfold tailWord_6387365
  simp only [CollatzResearch.WordTrace]
  refine ⟨232966340504674954938107549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155310893669783303292071699 232966340504674954938107549)
  ·
    refine ⟨87362377689253108101790331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232966340504674954938107549 87362377689253108101790331)
    ·
      refine ⟨131043566533879662152685497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87362377689253108101790331 131043566533879662152685497)
      ·
        refine ⟨98282674900409746614514123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131043566533879662152685497 98282674900409746614514123)
        ·
          refine ⟨147424012350614619921771185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98282674900409746614514123 147424012350614619921771185)
          ·
            refine ⟨110568009262960964941328389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147424012350614619921771185 110568009262960964941328389)
            ·
              refine ⟨20731501736805180926499073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110568009262960964941328389 20731501736805180926499073)
              ·
                refine ⟨15548626302603885694874305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20731501736805180926499073 15548626302603885694874305)
                ·
                  refine ⟨11661469726952914271155729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15548626302603885694874305 11661469726952914271155729)
                  ·
                    refine ⟨8746102295214685703366797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11661469726952914271155729 8746102295214685703366797)
                    ·
                      refine ⟨3279788360705507138762549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8746102295214685703366797 3279788360705507138762549)
                      ·
                        rfl

theorem cell23_6387365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_6387365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387365 prefixEnd_6387365 := by exact prefixLift 6387365
  have htrace : WordTrace (prefixWord ++ tailWord_6387365) baseStart_6387365 baseEnd_6387365 := by
    simpa [prefixWord, tailWord_6387365, baseEnd_6387365] using wordTrace_append hprefix tailTrace_6387365
  have hstable : (prefixWord ++ tailWord_6387365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387365).length < 2 ^ (prefixWord ++ tailWord_6387365).sum := by decide
  have hdescent : baseEnd_6387365 < baseStart_6387365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387415 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 1, 5]
def baseStart_6387415 : Nat := 118140960795 + 6387415 * 2 ^ 59
def prefixEnd_6387415 : Nat := 4983230072969 + 3 ^ 40 * 6387415 * 2
def baseEnd_6387415 : Nat := 1093271344912743981045773

theorem tailTrace_6387415 : CollatzResearch.WordTrace tailWord_6387415 prefixEnd_6387415 1093271344912743981045773 := by
  unfold tailWord_6387415
  simp only [CollatzResearch.WordTrace]
  refine ⟨232968164154493813477427699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155312109436329208984951799 232968164154493813477427699)
  ·
    refine ⟨349452246231740720216141549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232968164154493813477427699 349452246231740720216141549)
    ·
      refine ⟨131044592336902770081053081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349452246231740720216141549 131044592336902770081053081)
      ·
        refine ⟨98283444252677077560789811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131044592336902770081053081 98283444252677077560789811)
        ·
          refine ⟨147425166379015616341184717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98283444252677077560789811 147425166379015616341184717)
          ·
            refine ⟨55284437392130856127944269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147425166379015616341184717 55284437392130856127944269)
            ·
              refine ⟨20731664022049071047979101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55284437392130856127944269 20731664022049071047979101)
              ·
                refine ⟨7774374008268401642992163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20731664022049071047979101 7774374008268401642992163)
                ·
                  refine ⟨11661561012402602464488245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774374008268401642992163 11661561012402602464488245)
                  ·
                    refine ⟨1093271344912743981045773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11661561012402602464488245 1093271344912743981045773)
                    ·
                      rfl

theorem cell23_6387415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_6387415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387415 prefixEnd_6387415 := by exact prefixLift 6387415
  have htrace : WordTrace (prefixWord ++ tailWord_6387415) baseStart_6387415 baseEnd_6387415 := by
    simpa [prefixWord, tailWord_6387415, baseEnd_6387415] using wordTrace_append hprefix tailTrace_6387415
  have hstable : (prefixWord ++ tailWord_6387415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387415).length < 2 ^ (prefixWord ++ tailWord_6387415).sum := by decide
  have hdescent : baseEnd_6387415 < baseStart_6387415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387429 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6387429 : Nat := 118140960795 + 6387429 * 2 ^ 59
def prefixEnd_6387429 : Nat := 4983230072969 + 3 ^ 40 * 6387429 * 2
def baseEnd_6387429 : Nat := 3279821223467394888362255

theorem tailTrace_6387429 : CollatzResearch.WordTrace tailWord_6387429 prefixEnd_6387429 3279821223467394888362255 := by
  unfold tailWord_6387429
  simp only [CollatzResearch.WordTrace]
  refine ⟨232968674776443093868437341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155312449850962062578958227 232968674776443093868437341)
  ·
    refine ⟨87363253041166160200664003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232968674776443093868437341 87363253041166160200664003)
    ·
      refine ⟨131044879561749240300996005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87363253041166160200664003 131044879561749240300996005)
      ·
        refine ⟨24570914917827982556436751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131044879561749240300996005 24570914917827982556436751)
        ·
          refine ⟨36856372376741973834655127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24570914917827982556436751 36856372376741973834655127)
          ·
            refine ⟨55284558565112960751982691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36856372376741973834655127 55284558565112960751982691)
            ·
              refine ⟨82926837847669441127974037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55284558565112960751982691 82926837847669441127974037)
              ·
                refine ⟨3887195524109505052873783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82926837847669441127974037 3887195524109505052873783)
                ·
                  refine ⟨5830793286164257579310675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887195524109505052873783 5830793286164257579310675)
                  ·
                    refine ⟨8746189929246386368966013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5830793286164257579310675 8746189929246386368966013)
                    ·
                      refine ⟨3279821223467394888362255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8746189929246386368966013 3279821223467394888362255)
                      ·
                        rfl

theorem cell23_6387429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6387429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387429 prefixEnd_6387429 := by exact prefixLift 6387429
  have htrace : WordTrace (prefixWord ++ tailWord_6387429) baseStart_6387429 baseEnd_6387429 := by
    simpa [prefixWord, tailWord_6387429, baseEnd_6387429] using wordTrace_append hprefix tailTrace_6387429
  have hstable : (prefixWord ++ tailWord_6387429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387429).length < 2 ^ (prefixWord ++ tailWord_6387429).sum := by decide
  have hdescent : baseEnd_6387429 < baseStart_6387429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387452 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_6387452 : Nat := 118140960795 + 6387452 * 2 ^ 59
def prefixEnd_6387452 : Nat := 4983230072969 + 3 ^ 40 * 6387452 * 2
def baseEnd_6387452 : Nat := 3279833033522448298374649

theorem tailTrace_6387452 : CollatzResearch.WordTrace tailWord_6387452 prefixEnd_6387452 3279833033522448298374649 := by
  unfold tailWord_6387452
  simp only [CollatzResearch.WordTrace]
  refine ⟨116484756827679884398262305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155313009103573179197683073 116484756827679884398262305)
  ·
    refine ⟨87363567620759913298696729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116484756827679884398262305 87363567620759913298696729)
    ·
      refine ⟨65522675715569934974022547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87363567620759913298696729 65522675715569934974022547)
      ·
        refine ⟨98284013573354902461033821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65522675715569934974022547 98284013573354902461033821)
        ·
          refine ⟨36856505090008088422887683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98284013573354902461033821 36856505090008088422887683)
          ·
            refine ⟨55284757635012132634331525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36856505090008088422887683 55284757635012132634331525)
            ·
              refine ⟨10365892056564774868937161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55284757635012132634331525 10365892056564774868937161)
              ·
                refine ⟨7774419042423581151702871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10365892056564774868937161 7774419042423581151702871)
                ·
                  refine ⟨11661628563635371727554307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774419042423581151702871 11661628563635371727554307)
                  ·
                    refine ⟨17492442845453057591331461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11661628563635371727554307 17492442845453057591331461)
                    ·
                      refine ⟨3279833033522448298374649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17492442845453057591331461 3279833033522448298374649)
                      ·
                        rfl

theorem cell23_6387452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_6387452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387452 prefixEnd_6387452 := by exact prefixLift 6387452
  have htrace : WordTrace (prefixWord ++ tailWord_6387452) baseStart_6387452 baseEnd_6387452 := by
    simpa [prefixWord, tailWord_6387452, baseEnd_6387452] using wordTrace_append hprefix tailTrace_6387452
  have hstable : (prefixWord ++ tailWord_6387452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387452).length < 2 ^ (prefixWord ++ tailWord_6387452).sum := by decide
  have hdescent : baseEnd_6387452 < baseStart_6387452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387455 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_6387455 : Nat := 118140960795 + 6387455 * 2 ^ 59
def prefixEnd_6387455 : Nat := 4983230072969 + 3 ^ 40 * 6387455 * 2
def baseEnd_6387455 : Nat := 3279834573964411786637135

theorem tailTrace_6387455 : CollatzResearch.WordTrace tailWord_6387455 prefixEnd_6387455 3279834573964411786637135 := by
  unfold tailWord_6387455
  simp only [CollatzResearch.WordTrace]
  refine ⟨232969623074348900308883819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155313082049565933539255879 232969623074348900308883819)
  ·
    refine ⟨349454434611523350463325729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232969623074348900308883819 349454434611523350463325729)
    ·
      refine ⟨262090825958642512847494297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349454434611523350463325729 262090825958642512847494297)
      ·
        refine ⟨196568119468981884635620723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262090825958642512847494297 196568119468981884635620723)
        ·
          refine ⟨294852179203472826953431085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196568119468981884635620723 294852179203472826953431085)
          ·
            refine ⟨110569567201302310107536657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294852179203472826953431085 110569567201302310107536657)
            ·
              refine ⟨82927175400976732580652493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110569567201302310107536657 82927175400976732580652493)
              ·
                refine ⟨31097690775366274717744685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82927175400976732580652493 31097690775366274717744685)
                ·
                  refine ⟨11661634040762353019154257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31097690775366274717744685 11661634040762353019154257)
                  ·
                    refine ⟨8746225530571764764365693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11661634040762353019154257 8746225530571764764365693)
                    ·
                      refine ⟨3279834573964411786637135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8746225530571764764365693 3279834573964411786637135)
                      ·
                        rfl

theorem cell23_6387455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_6387455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387455 prefixEnd_6387455 := by exact prefixLift 6387455
  have htrace : WordTrace (prefixWord ++ tailWord_6387455) baseStart_6387455 baseEnd_6387455 := by
    simpa [prefixWord, tailWord_6387455, baseEnd_6387455] using wordTrace_append hprefix tailTrace_6387455
  have hstable : (prefixWord ++ tailWord_6387455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387455).length < 2 ^ (prefixWord ++ tailWord_6387455).sum := by decide
  have hdescent : baseEnd_6387455 < baseStart_6387455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387463 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6387463 : Nat := 118140960795 + 6387463 * 2 ^ 59
def prefixEnd_6387463 : Nat := 4983230072969 + 3 ^ 40 * 6387463 * 2
def baseEnd_6387463 : Nat := 3279838681809647755337099

theorem tailTrace_6387463 : CollatzResearch.WordTrace tailWord_6387463 prefixEnd_6387463 3279838681809647755337099 := by
  unfold tailWord_6387463
  simp only [CollatzResearch.WordTrace]
  refine ⟨232969914858319917675175043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155313276572213278450116695 232969914858319917675175043)
  ·
    refine ⟨349454872287479876512762565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232969914858319917675175043 349454872287479876512762565)
    ·
      refine ⟨65522788553902476846142981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349454872287479876512762565 65522788553902476846142981)
      ·
        refine ⟨12285522853856714408651809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65522788553902476846142981 12285522853856714408651809)
        ·
          refine ⟨9214142140392535806488857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12285522853856714408651809 9214142140392535806488857)
          ·
            refine ⟨6910606605294401854866643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9214142140392535806488857 6910606605294401854866643)
            ·
              refine ⟨10365909907941602782299965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6910606605294401854866643 10365909907941602782299965)
              ·
                refine ⟨3887216215478101043362487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10365909907941602782299965 3887216215478101043362487)
                ·
                  refine ⟨5830824323217151565043731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887216215478101043362487 5830824323217151565043731)
                  ·
                    refine ⟨8746236484825727347565597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5830824323217151565043731 8746236484825727347565597)
                    ·
                      refine ⟨3279838681809647755337099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8746236484825727347565597 3279838681809647755337099)
                      ·
                        rfl

theorem cell23_6387463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6387463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387463 prefixEnd_6387463 := by exact prefixLift 6387463
  have htrace : WordTrace (prefixWord ++ tailWord_6387463) baseStart_6387463 baseEnd_6387463 := by
    simpa [prefixWord, tailWord_6387463, baseEnd_6387463] using wordTrace_append hprefix tailTrace_6387463
  have hstable : (prefixWord ++ tailWord_6387463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387463).length < 2 ^ (prefixWord ++ tailWord_6387463).sum := by decide
  have hdescent : baseEnd_6387463 < baseStart_6387463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387496 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 2, 4]
def baseStart_6387496 : Nat := 118140960795 + 6387496 * 2 ^ 59
def prefixEnd_6387496 : Nat := 4983230072969 + 3 ^ 40 * 6387496 * 2
def baseEnd_6387496 : Nat := 1093285208890415375408149

theorem tailTrace_6387496 : CollatzResearch.WordTrace tailWord_6387496 prefixEnd_6387496 1093285208890415375408149 := by
  unfold tailWord_6387496
  simp only [CollatzResearch.WordTrace]
  refine ⟨116485559233600182155563171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155314078978133576207417561 116485559233600182155563171)
  ·
    refine ⟨174728338850400273233344757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116485559233600182155563171 174728338850400273233344757)
    ·
      refine ⟨16380781767225025615626071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174728338850400273233344757 16380781767225025615626071)
      ·
        refine ⟨24571172650837538423439107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16380781767225025615626071 24571172650837538423439107)
        ·
          refine ⟨36856758976256307635158661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24571172650837538423439107 36856758976256307635158661)
          ·
            refine ⟨6910642308048057681592249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36856758976256307635158661 6910642308048057681592249)
            ·
              refine ⟨5182981731036043261194187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6910642308048057681592249 5182981731036043261194187)
              ·
                refine ⟨7774472596554064891791281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182981731036043261194187 7774472596554064891791281)
                ·
                  refine ⟨5830854447415548668843461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7774472596554064891791281 5830854447415548668843461)
                  ·
                    refine ⟨1093285208890415375408149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5830854447415548668843461 1093285208890415375408149)
                    ·
                      rfl

theorem cell23_6387496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_6387496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387496 prefixEnd_6387496 := by exact prefixLift 6387496
  have htrace : WordTrace (prefixWord ++ tailWord_6387496) baseStart_6387496 baseEnd_6387496 := by
    simpa [prefixWord, tailWord_6387496, baseEnd_6387496] using wordTrace_append hprefix tailTrace_6387496
  have hstable : (prefixWord ++ tailWord_6387496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387496).length < 2 ^ (prefixWord ++ tailWord_6387496).sum := by decide
  have hdescent : baseEnd_6387496 < baseStart_6387496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387545 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_6387545 : Nat := 118140960795 + 6387545 * 2 ^ 59
def prefixEnd_6387545 : Nat := 4983230072969 + 3 ^ 40 * 6387545 * 2
def baseEnd_6387545 : Nat := 3279880787223316434511721

theorem tailTrace_6387545 : CollatzResearch.WordTrace tailWord_6387545 prefixEnd_6387545 3279880787223316434511721 := by
  unfold tailWord_6387545
  simp only [CollatzResearch.WordTrace]
  refine ⟨232972905644022845679660089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155315270429348563786440059 232972905644022845679660089)
  ·
    refine ⟨174729679233017134259745067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232972905644022845679660089 174729679233017134259745067)
    ·
      refine ⟨262094518849525701389617601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174729679233017134259745067 262094518849525701389617601)
      ·
        refine ⟨196570889137144276042213201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262094518849525701389617601 196570889137144276042213201)
        ·
          refine ⟨147428166852858207031659901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196570889137144276042213201 147428166852858207031659901)
          ·
            refine ⟨55285562569821827636872463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147428166852858207031659901 55285562569821827636872463)
            ·
              refine ⟨82928343854732741455308695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55285562569821827636872463 82928343854732741455308695)
              ·
                refine ⟨124392515782099112182963043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82928343854732741455308695 124392515782099112182963043)
                ·
                  refine ⟨186588773673148668274444565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124392515782099112182963043 186588773673148668274444565)
                  ·
                    refine ⟨8746348765928843825364589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 186588773673148668274444565 8746348765928843825364589)
                    ·
                      refine ⟨3279880787223316434511721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8746348765928843825364589 3279880787223316434511721)
                      ·
                        rfl

theorem cell23_6387545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_6387545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387545 prefixEnd_6387545 := by exact prefixLift 6387545
  have htrace : WordTrace (prefixWord ++ tailWord_6387545) baseStart_6387545 baseEnd_6387545 := by
    simpa [prefixWord, tailWord_6387545, baseEnd_6387545] using wordTrace_append hprefix tailTrace_6387545
  have hstable : (prefixWord ++ tailWord_6387545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387545).length < 2 ^ (prefixWord ++ tailWord_6387545).sum := by decide
  have hdescent : baseEnd_6387545 < baseStart_6387545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387559 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_6387559 : Nat := 118140960795 + 6387559 * 2 ^ 59
def prefixEnd_6387559 : Nat := 4983230072969 + 3 ^ 40 * 6387559 * 2
def baseEnd_6387559 : Nat := 3279887975952479379736657

theorem tailTrace_6387559 : CollatzResearch.WordTrace tailWord_6387559 prefixEnd_6387559 3279887975952479379736657 := by
  unfold tailWord_6387559
  simp only [CollatzResearch.WordTrace]
  refine ⟨232973416265972126070669731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155315610843981417380446487 232973416265972126070669731)
  ·
    refine ⟨349460124398958189106004597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232973416265972126070669731 349460124398958189106004597)
    ·
      refine ⟨32761886662402330228687931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 349460124398958189106004597 32761886662402330228687931)
      ·
        refine ⟨49142829993603495343031897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32761886662402330228687931 49142829993603495343031897)
        ·
          refine ⟨36857122495202621507273923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49142829993603495343031897 36857122495202621507273923)
          ·
            refine ⟨55285683742803932260910885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36857122495202621507273923 55285683742803932260910885)
            ·
              refine ⟨10366065701775737298920791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55285683742803932260910885 10366065701775737298920791)
              ·
                refine ⟨15549098552663605948381187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366065701775737298920791 15549098552663605948381187)
                ·
                  refine ⟨23323647828995408922571781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15549098552663605948381187 23323647828995408922571781)
                  ·
                    refine ⟨4373183967936639172982209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23323647828995408922571781 4373183967936639172982209)
                    ·
                      refine ⟨3279887975952479379736657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373183967936639172982209 3279887975952479379736657)
                      ·
                        rfl

theorem cell23_6387559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_6387559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387559 prefixEnd_6387559 := by exact prefixLift 6387559
  have htrace : WordTrace (prefixWord ++ tailWord_6387559) baseStart_6387559 baseEnd_6387559 := by
    simpa [prefixWord, tailWord_6387559, baseEnd_6387559] using wordTrace_append hprefix tailTrace_6387559
  have hstable : (prefixWord ++ tailWord_6387559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387559).length < 2 ^ (prefixWord ++ tailWord_6387559).sum := by decide
  have hdescent : baseEnd_6387559 < baseStart_6387559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387565 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 9]
def baseStart_6387565 : Nat := 118140960795 + 6387565 * 2 ^ 59
def prefixEnd_6387565 : Nat := 4983230072969 + 3 ^ 40 * 6387565 * 2
def baseEnd_6387565 : Nat := 364432339648489595140181

theorem tailTrace_6387565 : CollatzResearch.WordTrace tailWord_6387565 prefixEnd_6387565 364432339648489595140181 := by
  unfold tailWord_6387565
  simp only [CollatzResearch.WordTrace]
  refine ⟨232973635103950389095388149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155315756735966926063592099 232973635103950389095388149)
  ·
    refine ⟨21841278290995348977692639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232973635103950389095388149 21841278290995348977692639)
    ·
      refine ⟨32761917436493023466538959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21841278290995348977692639 32761917436493023466538959)
      ·
        refine ⟨49142876154739535199808439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32761917436493023466538959 49142876154739535199808439)
        ·
          refine ⟨73714314232109302799712659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49142876154739535199808439 73714314232109302799712659)
          ·
            refine ⟨110571471348163954199568989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73714314232109302799712659 110571471348163954199568989)
            ·
              refine ⟨41464301755561482824838371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110571471348163954199568989 41464301755561482824838371)
              ·
                refine ⟨62196452633342224237257557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41464301755561482824838371 62196452633342224237257557)
                ·
                  refine ⟨364432339648489595140181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62196452633342224237257557 364432339648489595140181)
                  ·
                    rfl

theorem cell23_6387565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_6387565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387565 prefixEnd_6387565 := by exact prefixLift 6387565
  have htrace : WordTrace (prefixWord ++ tailWord_6387565) baseStart_6387565 baseEnd_6387565 := by
    simpa [prefixWord, tailWord_6387565, baseEnd_6387565] using wordTrace_append hprefix tailTrace_6387565
  have hstable : (prefixWord ++ tailWord_6387565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387565).length < 2 ^ (prefixWord ++ tailWord_6387565).sum := by decide
  have hdescent : baseEnd_6387565 < baseStart_6387565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387595 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 4, 5]
def baseStart_6387595 : Nat := 118140960795 + 6387595 * 2 ^ 59
def prefixEnd_6387595 : Nat := 4983230072969 + 3 ^ 40 * 6387595 * 2
def baseEnd_6387595 : Nat := 1093302153752013746295497

theorem tailTrace_6387595 : CollatzResearch.WordTrace tailWord_6387595 prefixEnd_6387595 1093302153752013746295497 := by
  unfold tailWord_6387595
  simp only [CollatzResearch.WordTrace]
  refine ⟨232974729293841704218980239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155316486195894469479320159 232974729293841704218980239)
  ·
    refine ⟨349462093940762556328470359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232974729293841704218980239 349462093940762556328470359)
    ·
      refine ⟨524193140911143834492705539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349462093940762556328470359 524193140911143834492705539)
      ·
        refine ⟨786289711366715751739058309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524193140911143834492705539 786289711366715751739058309)
        ·
          refine ⟨147429320881259203451073433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 786289711366715751739058309 147429320881259203451073433)
          ·
            refine ⟨110571990660944402588305075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147429320881259203451073433 110571990660944402588305075)
            ·
              refine ⟨165857985991416603882457613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110571990660944402588305075 165857985991416603882457613)
              ·
                refine ⟨62196744746781226455921605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165857985991416603882457613 62196744746781226455921605)
                ·
                  refine ⟨11661889640021479960485301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62196744746781226455921605 11661889640021479960485301)
                  ·
                    refine ⟨1093302153752013746295497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11661889640021479960485301 1093302153752013746295497)
                    ·
                      rfl

theorem cell23_6387595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 5].length) (baseStart_6387595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387595 prefixEnd_6387595 := by exact prefixLift 6387595
  have htrace : WordTrace (prefixWord ++ tailWord_6387595) baseStart_6387595 baseEnd_6387595 := by
    simpa [prefixWord, tailWord_6387595, baseEnd_6387595] using wordTrace_append hprefix tailTrace_6387595
  have hstable : (prefixWord ++ tailWord_6387595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387595).length < 2 ^ (prefixWord ++ tailWord_6387595).sum := by decide
  have hdescent : baseEnd_6387595 < baseStart_6387595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387605 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_6387605 : Nat := 118140960795 + 6387605 * 2 ^ 59
def prefixEnd_6387605 : Nat := 4983230072969 + 3 ^ 40 * 6387605 * 2
def baseEnd_6387605 : Nat := 3279911596062586199761445

theorem tailTrace_6387605 : CollatzResearch.WordTrace tailWord_6387605 prefixEnd_6387605 3279911596062586199761445 := by
  unfold tailWord_6387605
  simp only [CollatzResearch.WordTrace]
  refine ⟨232975094023805475926844269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155316729349203650617896179 232975094023805475926844269)
  ·
    refine ⟨87365660258927053472566601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232975094023805475926844269 87365660258927053472566601)
    ·
      refine ⟨65524245194195290104424951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87365660258927053472566601 65524245194195290104424951)
      ·
        refine ⟨98286367791292935156637427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65524245194195290104424951 98286367791292935156637427)
        ·
          refine ⟨147429551686939402734956141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98286367791292935156637427 147429551686939402734956141)
          ·
            refine ⟨55286081882602276025608553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147429551686939402734956141 55286081882602276025608553)
            ·
              refine ⟨41464561411951707019206415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55286081882602276025608553 41464561411951707019206415)
              ·
                refine ⟨62196842117927560528809623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41464561411951707019206415 62196842117927560528809623)
                ·
                  refine ⟨93295263176891340793214435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62196842117927560528809623 93295263176891340793214435)
                  ·
                    refine ⟨139942894765337011189821653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93295263176891340793214435 139942894765337011189821653)
                    ·
                      refine ⟨3279911596062586199761445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139942894765337011189821653 3279911596062586199761445)
                      ·
                        rfl

theorem cell23_6387605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_6387605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387605 prefixEnd_6387605 := by exact prefixLift 6387605
  have htrace : WordTrace (prefixWord ++ tailWord_6387605) baseStart_6387605 baseEnd_6387605 := by
    simpa [prefixWord, tailWord_6387605, baseEnd_6387605] using wordTrace_append hprefix tailTrace_6387605
  have hstable : (prefixWord ++ tailWord_6387605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387605).length < 2 ^ (prefixWord ++ tailWord_6387605).sum := by decide
  have hdescent : baseEnd_6387605 < baseStart_6387605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387612 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6387612 : Nat := 118140960795 + 6387612 * 2 ^ 59
def prefixEnd_6387612 : Nat := 4983230072969 + 3 ^ 40 * 6387612 * 2
def baseEnd_6387612 : Nat := 1093305063475722557457971

theorem tailTrace_6387612 : CollatzResearch.WordTrace tailWord_6387612 prefixEnd_6387612 1093305063475722557457971 := by
  unfold tailWord_6387612
  simp only [CollatzResearch.WordTrace]
  refine ⟨116487674667390058061174545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155316899556520077414899393 116487674667390058061174545)
  ·
    refine ⟨87365756000542543545880909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116487674667390058061174545 87365756000542543545880909)
    ·
      refine ⟨32762158500203453829705341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87365756000542543545880909 32762158500203453829705341)
      ·
        refine ⟨12285809437576295186139503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32762158500203453829705341 12285809437576295186139503)
        ·
          refine ⟨18428714156364442779209255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12285809437576295186139503 18428714156364442779209255)
          ·
            refine ⟨27643071234546664168813883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18428714156364442779209255 27643071234546664168813883)
            ·
              refine ⟨41464606851819996253220825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27643071234546664168813883 41464606851819996253220825)
              ·
                refine ⟨31098455138864997189915619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41464606851819996253220825 31098455138864997189915619)
                ·
                  refine ⟨46647682708297495784873429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31098455138864997189915619 46647682708297495784873429)
                  ·
                    refine ⟨1093305063475722557457971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46647682708297495784873429 1093305063475722557457971)
                    ·
                      rfl

theorem cell23_6387612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6387612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387612 prefixEnd_6387612 := by exact prefixLift 6387612
  have htrace : WordTrace (prefixWord ++ tailWord_6387612) baseStart_6387612 baseEnd_6387612 := by
    simpa [prefixWord, tailWord_6387612, baseEnd_6387612] using wordTrace_append hprefix tailTrace_6387612
  have hstable : (prefixWord ++ tailWord_6387612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387612).length < 2 ^ (prefixWord ++ tailWord_6387612).sum := by decide
  have hdescent : baseEnd_6387612 < baseStart_6387612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387672 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 6]
def baseStart_6387672 : Nat := 118140960795 + 6387672 * 2 ^ 59
def prefixEnd_6387672 : Nat := 4983230072969 + 3 ^ 40 * 6387672 * 2
def baseEnd_6387672 : Nat := 364438444362937493069293

theorem tailTrace_6387672 : CollatzResearch.WordTrace tailWord_6387672 prefixEnd_6387672 364438444362937493069293 := by
  unfold tailWord_6387672
  simp only [CollatzResearch.WordTrace]
  refine ⟨116488768857281373184766635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155318358476375164246355513 116488768857281373184766635)
  ·
    refine ⟨174733153285922059777149953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116488768857281373184766635 174733153285922059777149953)
    ·
      refine ⟨131049864964441544832862465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174733153285922059777149953 131049864964441544832862465)
      ·
        refine ⟨98287398723331158624646849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131049864964441544832862465 98287398723331158624646849)
        ·
          refine ⟨73715549042498368968485137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98287398723331158624646849 73715549042498368968485137)
          ·
            refine ⟨55286661781873776726363853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73715549042498368968485137 55286661781873776726363853)
            ·
              refine ⟨20732498168202666272386445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55286661781873776726363853 20732498168202666272386445)
              ·
                refine ⟨7774686813075999852144917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20732498168202666272386445 7774686813075999852144917)
                ·
                  refine ⟨364438444362937493069293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7774686813075999852144917 364438444362937493069293)
                  ·
                    rfl

theorem cell23_6387672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 6].length) (baseStart_6387672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387672 prefixEnd_6387672 := by exact prefixLift 6387672
  have htrace : WordTrace (prefixWord ++ tailWord_6387672) baseStart_6387672 baseEnd_6387672 := by
    simpa [prefixWord, tailWord_6387672, baseEnd_6387672] using wordTrace_append hprefix tailTrace_6387672
  have hstable : (prefixWord ++ tailWord_6387672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387672).length < 2 ^ (prefixWord ++ tailWord_6387672).sum := by decide
  have hdescent : baseEnd_6387672 < baseStart_6387672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387710 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6387710 : Nat := 118140960795 + 6387710 * 2 ^ 59
def prefixEnd_6387710 : Nat := 4983230072969 + 3 ^ 40 * 6387710 * 2
def baseEnd_6387710 : Nat := 1093321837177102762982821

theorem tailTrace_6387710 : CollatzResearch.WordTrace tailWord_6387710 prefixEnd_6387710 1093321837177102762982821 := by
  unfold tailWord_6387710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122365461053134857427073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155319282458950052572944389 29122365461053134857427073)
  ·
    refine ⟨21841774095789851143070305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29122365461053134857427073 21841774095789851143070305)
    ·
      refine ⟨16381330571842388357302729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21841774095789851143070305 16381330571842388357302729)
      ·
        refine ⟨12285997928881791267977047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16381330571842388357302729 12285997928881791267977047)
        ·
          refine ⟨18428996893322686901965571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12285997928881791267977047 18428996893322686901965571)
          ·
            refine ⟨27643495339984030352948357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18428996893322686901965571 27643495339984030352948357)
            ·
              refine ⟨5183155376247005691177817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27643495339984030352948357 5183155376247005691177817)
              ·
                refine ⟨3887366532185254268383363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183155376247005691177817 3887366532185254268383363)
                ·
                  refine ⟨5831049798277881402575045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887366532185254268383363 5831049798277881402575045)
                  ·
                    refine ⟨1093321837177102762982821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5831049798277881402575045 1093321837177102762982821)
                    ·
                      rfl

theorem cell23_6387710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6387710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387710 prefixEnd_6387710 := by exact prefixLift 6387710
  have htrace : WordTrace (prefixWord ++ tailWord_6387710) baseStart_6387710 baseEnd_6387710 := by
    simpa [prefixWord, tailWord_6387710, baseEnd_6387710] using wordTrace_append hprefix tailTrace_6387710
  have hstable : (prefixWord ++ tailWord_6387710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387710).length < 2 ^ (prefixWord ++ tailWord_6387710).sum := by decide
  have hdescent : baseEnd_6387710 < baseStart_6387710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
