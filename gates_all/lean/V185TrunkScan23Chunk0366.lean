import V185TrunkScan23Chunk0365

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2164231 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_2164231 : Nat := 118140960795 + 2164231 * 2 ^ 59
def prefixEnd_2164231 : Nat := 4983230072969 + 3 ^ 40 * 2164231 * 2
def baseEnd_2164231 : Nat := 1111290750360827169959389

theorem tailTrace_2164231 : CollatzResearch.WordTrace tailWord_2164231 prefixEnd_2164231 1111290750360827169959389 := by
  unfold tailWord_2164231
  simp only [CollatzResearch.WordTrace]
  refine ⟨78935989422368183072860547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52623992948245455381907031 78935989422368183072860547)
  ·
    refine ⟨118403984133552274609290821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78935989422368183072860547 118403984133552274609290821)
    ·
      refine ⟨22200747025041051489242029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118403984133552274609290821 22200747025041051489242029)
      ·
        refine ⟨8325280134390394308465761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22200747025041051489242029 8325280134390394308465761)
        ·
          refine ⟨6243960100792795731349321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8325280134390394308465761 6243960100792795731349321)
          ·
            refine ⟨4682970075594596798511991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6243960100792795731349321 4682970075594596798511991)
            ·
              refine ⟨7024455113391895197767987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682970075594596798511991 7024455113391895197767987)
              ·
                refine ⟨10536682670087842796651981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7024455113391895197767987 10536682670087842796651981)
                ·
                  refine ⟨3951256001282941048744493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10536682670087842796651981 3951256001282941048744493)
                  ·
                    refine ⟨1481721000481102893279185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3951256001282941048744493 1481721000481102893279185)
                    ·
                      refine ⟨1111290750360827169959389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481721000481102893279185 1111290750360827169959389)
                      ·
                        rfl

theorem cell23_2164231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_2164231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164231 prefixEnd_2164231 := by exact prefixLift 2164231
  have htrace : WordTrace (prefixWord ++ tailWord_2164231) baseStart_2164231 baseEnd_2164231 := by
    simpa [prefixWord, tailWord_2164231, baseEnd_2164231] using wordTrace_append hprefix tailTrace_2164231
  have hstable : (prefixWord ++ tailWord_2164231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164231).length < 2 ^ (prefixWord ++ tailWord_2164231).sum := by decide
  have hdescent : baseEnd_2164231 < baseStart_2164231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164240 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_2164240 : Nat := 118140960795 + 2164240 * 2 ^ 59
def prefixEnd_2164240 : Nat := 4983230072969 + 3 ^ 40 * 2164240 * 2
def baseEnd_2164240 : Nat := 1111295371686717634746847

theorem tailTrace_2164240 : CollatzResearch.WordTrace tailWord_2164240 prefixEnd_2164240 1111295371686717634746847 := by
  unfold tailWord_2164240
  simp only [CollatzResearch.WordTrace]
  refine ⟨39468158839667788804969087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52624211786223718406625449 39468158839667788804969087)
  ·
    refine ⟨59202238259501683207453631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39468158839667788804969087 59202238259501683207453631)
    ·
      refine ⟨88803357389252524811180447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59202238259501683207453631 88803357389252524811180447)
      ·
        refine ⟨133205036083878787216770671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88803357389252524811180447 133205036083878787216770671)
        ·
          refine ⟨199807554125818180825156007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133205036083878787216770671 199807554125818180825156007)
          ·
            refine ⟨299711331188727271237734011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199807554125818180825156007 299711331188727271237734011)
            ·
              refine ⟨449566996783090906856601017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299711331188727271237734011 449566996783090906856601017)
              ·
                refine ⟨337175247587318180142450763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449566996783090906856601017 337175247587318180142450763)
                ·
                  refine ⟨505762871380977270213676145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337175247587318180142450763 505762871380977270213676145)
                  ·
                    refine ⟨379322153535732952660257109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 505762871380977270213676145 379322153535732952660257109)
                    ·
                      refine ⟨1111295371686717634746847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 379322153535732952660257109 1111295371686717634746847)
                      ·
                        rfl

theorem cell23_2164240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_2164240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164240 prefixEnd_2164240 := by exact prefixLift 2164240
  have htrace : WordTrace (prefixWord ++ tailWord_2164240) baseStart_2164240 baseEnd_2164240 := by
    simpa [prefixWord, tailWord_2164240, baseEnd_2164240] using wordTrace_append hprefix tailTrace_2164240
  have hstable : (prefixWord ++ tailWord_2164240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164240).length < 2 ^ (prefixWord ++ tailWord_2164240).sum := by decide
  have hdescent : baseEnd_2164240 < baseStart_2164240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164284 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 7]
def baseStart_2164284 : Nat := 118140960795 + 2164284 * 2 ^ 59
def prefixEnd_2164284 : Nat := 4983230072969 + 3 ^ 40 * 2164284 * 2
def baseEnd_2164284 : Nat := 123479773870612829177405

theorem tailTrace_2164284 : CollatzResearch.WordTrace tailWord_2164284 prefixEnd_2164284 123479773870612829177405 := by
  unfold tailWord_2164284
  simp only [CollatzResearch.WordTrace]
  refine ⟨39468961245588086562269953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52625281660784115416359937 39468961245588086562269953)
  ·
    refine ⟨29601720934191064921702465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39468961245588086562269953 29601720934191064921702465)
    ·
      refine ⟨22201290700643298691276849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29601720934191064921702465 22201290700643298691276849)
      ·
        refine ⟨16650968025482474018457637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22201290700643298691276849 16650968025482474018457637)
        ·
          refine ⟨3122056504777963878460807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16650968025482474018457637 3122056504777963878460807)
          ·
            refine ⟨4683084757166945817691211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122056504777963878460807 4683084757166945817691211)
            ·
              refine ⟨7024627135750418726536817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4683084757166945817691211 7024627135750418726536817)
              ·
                refine ⟨5268470351812814044902613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7024627135750418726536817 5268470351812814044902613)
                ·
                  refine ⟨123479773870612829177405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5268470351812814044902613 123479773870612829177405)
                  ·
                    rfl

theorem cell23_2164284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_2164284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164284 prefixEnd_2164284 := by exact prefixLift 2164284
  have htrace : WordTrace (prefixWord ++ tailWord_2164284) baseStart_2164284 baseEnd_2164284 := by
    simpa [prefixWord, tailWord_2164284, baseEnd_2164284] using wordTrace_append hprefix tailTrace_2164284
  have hstable : (prefixWord ++ tailWord_2164284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164284).length < 2 ^ (prefixWord ++ tailWord_2164284).sum := by decide
  have hdescent : baseEnd_2164284 < baseStart_2164284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164347 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4]
def baseStart_2164347 : Nat := 118140960795 + 2164347 * 2 ^ 59
def prefixEnd_2164347 : Nat := 4983230072969 + 3 ^ 40 * 2164347 * 2
def baseEnd_2164347 : Nat := 1111350314116748716108855

theorem tailTrace_2164347 : CollatzResearch.WordTrace tailWord_2164347 prefixEnd_2164347 1111350314116748716108855 := by
  unfold tailWord_2164347
  simp only [CollatzResearch.WordTrace]
  refine ⟨78940220289947934884083295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52626813526631956589388863 78940220289947934884083295)
  ·
    refine ⟨118410330434921902326124943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78940220289947934884083295 118410330434921902326124943)
    ·
      refine ⟨177615495652382853489187415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118410330434921902326124943 177615495652382853489187415)
      ·
        refine ⟨266423243478574280233781123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177615495652382853489187415 266423243478574280233781123)
        ·
          refine ⟨399634865217861420350671685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266423243478574280233781123 399634865217861420350671685)
          ·
            refine ⟨74931537228349016315750941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399634865217861420350671685 74931537228349016315750941)
            ·
              refine ⟨28099326460630881118406603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74931537228349016315750941 28099326460630881118406603)
              ·
                refine ⟨42148989690946321677609905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28099326460630881118406603 42148989690946321677609905)
                ·
                  refine ⟨31611742268209741258207429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42148989690946321677609905 31611742268209741258207429)
                  ·
                    refine ⟨5927201675289326485913893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31611742268209741258207429 5927201675289326485913893)
                    ·
                      refine ⟨1111350314116748716108855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5927201675289326485913893 1111350314116748716108855)
                      ·
                        rfl

theorem cell23_2164347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_2164347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164347 prefixEnd_2164347 := by exact prefixLift 2164347
  have htrace : WordTrace (prefixWord ++ tailWord_2164347) baseStart_2164347 baseEnd_2164347 := by
    simpa [prefixWord, tailWord_2164347, baseEnd_2164347] using wordTrace_append hprefix tailTrace_2164347
  have hstable : (prefixWord ++ tailWord_2164347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164347).length < 2 ^ (prefixWord ++ tailWord_2164347).sum := by decide
  have hdescent : baseEnd_2164347 < baseStart_2164347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164357 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 10]
def baseStart_2164357 : Nat := 118140960795 + 2164357 * 2 ^ 59
def prefixEnd_2164357 : Nat := 4983230072969 + 3 ^ 40 * 2164357 * 2
def baseEnd_2164357 : Nat := 123483938769254852998201

theorem tailTrace_2164357 : CollatzResearch.WordTrace tailWord_2164357 prefixEnd_2164357 123483938769254852998201 := by
  unfold tailWord_2164357
  simp only [CollatzResearch.WordTrace]
  refine ⟨78940585019911706591947325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52627056679941137727964883 78940585019911706591947325)
  ·
    refine ⟨29602719382466889971980247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78940585019911706591947325 29602719382466889971980247)
    ·
      refine ⟨44404079073700334957970371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29602719382466889971980247 44404079073700334957970371)
      ·
        refine ⟨66606118610550502436955557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44404079073700334957970371 66606118610550502436955557)
        ·
          refine ⟨12488647239478219206929167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66606118610550502436955557 12488647239478219206929167)
          ·
            refine ⟨18732970859217328810393751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12488647239478219206929167 18732970859217328810393751)
            ·
              refine ⟨28099456288825993215590627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18732970859217328810393751 28099456288825993215590627)
              ·
                refine ⟨42149184433238989823385941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28099456288825993215590627 42149184433238989823385941)
                ·
                  refine ⟨123483938769254852998201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42149184433238989823385941 123483938769254852998201)
                  ·
                    rfl

theorem cell23_2164357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_2164357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164357 prefixEnd_2164357 := by exact prefixLift 2164357
  have htrace : WordTrace (prefixWord ++ tailWord_2164357) baseStart_2164357 baseEnd_2164357 := by
    simpa [prefixWord, tailWord_2164357, baseEnd_2164357] using wordTrace_append hprefix tailTrace_2164357
  have hstable : (prefixWord ++ tailWord_2164357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164357).length < 2 ^ (prefixWord ++ tailWord_2164357).sum := by decide
  have hdescent : baseEnd_2164357 < baseStart_2164357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164377 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_2164377 : Nat := 118140960795 + 2164377 * 2 ^ 59
def prefixEnd_2164377 : Nat := 4983230072969 + 3 ^ 40 * 2164377 * 2
def baseEnd_2164377 : Nat := 1111365718536383598733717

theorem tailTrace_2164377 : CollatzResearch.WordTrace tailWord_2164377 prefixEnd_2164377 1111365718536383598733717 := by
  unfold tailWord_2164377
  simp only [CollatzResearch.WordTrace]
  refine ⟨78941314479839250007675385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52627542986559500005116923 78941314479839250007675385)
  ·
    refine ⟨59205985859879437505756539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78941314479839250007675385 59205985859879437505756539)
    ·
      refine ⟨88808978789819156258634809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59205985859879437505756539 88808978789819156258634809)
      ·
        refine ⟨66606734092364367193976107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88808978789819156258634809 66606734092364367193976107)
        ·
          refine ⟨99910101138546550790964161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66606734092364367193976107 99910101138546550790964161)
          ·
            refine ⟨74932575853909913093223121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99910101138546550790964161 74932575853909913093223121)
            ·
              refine ⟨56199431890432434819917341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74932575853909913093223121 56199431890432434819917341)
              ·
                refine ⟨21074786958912163057469003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56199431890432434819917341 21074786958912163057469003)
                ·
                  refine ⟨31612180438368244586203505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21074786958912163057469003 31612180438368244586203505)
                  ·
                    refine ⟨23709135328776183439652629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31612180438368244586203505 23709135328776183439652629)
                    ·
                      refine ⟨1111365718536383598733717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23709135328776183439652629 1111365718536383598733717)
                      ·
                        rfl

theorem cell23_2164377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_2164377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164377 prefixEnd_2164377 := by exact prefixLift 2164377
  have htrace : WordTrace (prefixWord ++ tailWord_2164377) baseStart_2164377 baseEnd_2164377 := by
    simpa [prefixWord, tailWord_2164377, baseEnd_2164377] using wordTrace_append hprefix tailTrace_2164377
  have hstable : (prefixWord ++ tailWord_2164377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164377).length < 2 ^ (prefixWord ++ tailWord_2164377).sum := by decide
  have hdescent : baseEnd_2164377 < baseStart_2164377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164429 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2164429 : Nat := 118140960795 + 2164429 * 2 ^ 59
def prefixEnd_2164429 : Nat := 4983230072969 + 3 ^ 40 * 2164429 * 2
def baseEnd_2164429 : Nat := 370464139843472465094493

theorem tailTrace_2164429 : CollatzResearch.WordTrace tailWord_2164429 prefixEnd_2164429 370464139843472465094493 := by
  unfold tailWord_2164429
  simp only [CollatzResearch.WordTrace]
  refine ⟨78943211075650862888568341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52628807383767241925712227 78943211075650862888568341)
  ·
    refine ⟨3700463019171134197901641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78943211075650862888568341 3700463019171134197901641)
    ·
      refine ⟨2775347264378350648426231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3700463019171134197901641 2775347264378350648426231)
      ·
        refine ⟨4163020896567525972639347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775347264378350648426231 4163020896567525972639347)
        ·
          refine ⟨6244531344851288958959021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163020896567525972639347 6244531344851288958959021)
          ·
            refine ⟨2341699254319233359609633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6244531344851288958959021 2341699254319233359609633)
            ·
              refine ⟨1756274440739425019707225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341699254319233359609633 1756274440739425019707225)
              ·
                refine ⟨1317205830554568764780419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756274440739425019707225 1317205830554568764780419)
                ·
                  refine ⟨1975808745831853147170629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317205830554568764780419 1975808745831853147170629)
                  ·
                    refine ⟨370464139843472465094493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975808745831853147170629 370464139843472465094493)
                    ·
                      rfl

theorem cell23_2164429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2164429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164429 prefixEnd_2164429 := by exact prefixLift 2164429
  have htrace : WordTrace (prefixWord ++ tailWord_2164429) baseStart_2164429 baseEnd_2164429 := by
    simpa [prefixWord, tailWord_2164429, baseEnd_2164429] using wordTrace_append hprefix tailTrace_2164429
  have hstable : (prefixWord ++ tailWord_2164429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164429).length < 2 ^ (prefixWord ++ tailWord_2164429).sum := by decide
  have hdescent : baseEnd_2164429 < baseStart_2164429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164458 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_2164458 : Nat := 118140960795 + 2164458 * 2 ^ 59
def prefixEnd_2164458 : Nat := 4983230072969 + 3 ^ 40 * 2164458 * 2
def baseEnd_2164458 : Nat := 1111407310469397781820845

theorem tailTrace_2164458 : CollatzResearch.WordTrace tailWord_2164458 prefixEnd_2164458 1111407310469397781820845 := by
  unfold tailWord_2164458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19736067198136450210343507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52629512528363867227582685 19736067198136450210343507)
  ·
    refine ⟨29604100797204675315515261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19736067198136450210343507 29604100797204675315515261)
    ·
      refine ⟨11101537798951753243318223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29604100797204675315515261 11101537798951753243318223)
      ·
        refine ⟨16652306698427629864977335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11101537798951753243318223 16652306698427629864977335)
        ·
          refine ⟨24978460047641444797466003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16652306698427629864977335 24978460047641444797466003)
          ·
            refine ⟨37467690071462167196199005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24978460047641444797466003 37467690071462167196199005)
            ·
              refine ⟨14050383776798312698574627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37467690071462167196199005 14050383776798312698574627)
              ·
                refine ⟨21075575665197469047861941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14050383776798312698574627 21075575665197469047861941)
                ·
                  refine ⟨1975835218612262723237057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21075575665197469047861941 1975835218612262723237057)
                  ·
                    refine ⟨1481876413959197042427793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1975835218612262723237057 1481876413959197042427793)
                    ·
                      refine ⟨1111407310469397781820845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481876413959197042427793 1111407310469397781820845)
                      ·
                        rfl

theorem cell23_2164458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_2164458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164458 prefixEnd_2164458 := by exact prefixLift 2164458
  have htrace : WordTrace (prefixWord ++ tailWord_2164458) baseStart_2164458 baseEnd_2164458 := by
    simpa [prefixWord, tailWord_2164458, baseEnd_2164458] using wordTrace_append hprefix tailTrace_2164458
  have hstable : (prefixWord ++ tailWord_2164458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164458).length < 2 ^ (prefixWord ++ tailWord_2164458).sum := by decide
  have hdescent : baseEnd_2164458 < baseStart_2164458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164494 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2164494 : Nat := 118140960795 + 2164494 * 2 ^ 59
def prefixEnd_2164494 : Nat := 4983230072969 + 3 ^ 40 * 2164494 * 2
def baseEnd_2164494 : Nat := 370475265257653213656893

theorem tailTrace_2164494 : CollatzResearch.WordTrace tailWord_2164494 prefixEnd_2164494 370475265257653213656893 := by
  unfold tailWord_2164494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868197727551922373710567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52630387880276919326456357 9868197727551922373710567)
  ·
    refine ⟨14802296591327883560565851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9868197727551922373710567 14802296591327883560565851)
    ·
      refine ⟨22203444886991825340848777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14802296591327883560565851 22203444886991825340848777)
      ·
        refine ⟨16652583665243869005636583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22203444886991825340848777 16652583665243869005636583)
        ·
          refine ⟨24978875497865803508454875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16652583665243869005636583 24978875497865803508454875)
          ·
            refine ⟨37468313246798705262682313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24978875497865803508454875 37468313246798705262682313)
            ·
              refine ⟨28101234935099028947011735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37468313246798705262682313 28101234935099028947011735)
              ·
                refine ⟨42151852402648543420517603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28101234935099028947011735 42151852402648543420517603)
                ·
                  refine ⟨63227778603972815130776405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42151852402648543420517603 63227778603972815130776405)
                  ·
                    refine ⟨370475265257653213656893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63227778603972815130776405 370475265257653213656893)
                    ·
                      rfl

theorem cell23_2164494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2164494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164494 prefixEnd_2164494 := by exact prefixLift 2164494
  have htrace : WordTrace (prefixWord ++ tailWord_2164494) baseStart_2164494 baseEnd_2164494 := by
    simpa [prefixWord, tailWord_2164494, baseEnd_2164494] using wordTrace_append hprefix tailTrace_2164494
  have hstable : (prefixWord ++ tailWord_2164494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164494).length < 2 ^ (prefixWord ++ tailWord_2164494).sum := by decide
  have hdescent : baseEnd_2164494 < baseStart_2164494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164526 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2164526 : Nat := 118140960795 + 2164526 * 2 ^ 59
def prefixEnd_2164526 : Nat := 4983230072969 + 3 ^ 40 * 2164526 * 2
def baseEnd_2164526 : Nat := 1111442227153903515770533

theorem tailTrace_2164526 : CollatzResearch.WordTrace tailWord_2164526 prefixEnd_2164526 1111442227153903515770533 := by
  unfold tailWord_2164526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868343619537431056856179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52631165970866298969899621 9868343619537431056856179)
  ·
    refine ⟨14802515429306146585284269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9868343619537431056856179 14802515429306146585284269)
    ·
      refine ⟨5550943285989804969481601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14802515429306146585284269 5550943285989804969481601)
      ·
        refine ⟨4163207464492353727111201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5550943285989804969481601 4163207464492353727111201)
        ·
          refine ⟨3122405598369265295333401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4163207464492353727111201 3122405598369265295333401)
          ·
            refine ⟨2341804198776948971500051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3122405598369265295333401 2341804198776948971500051)
            ·
              refine ⟨3512706298165423457250077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341804198776948971500051 3512706298165423457250077)
              ·
                refine ⟨1317264861812033796468779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3512706298165423457250077 1317264861812033796468779)
                ·
                  refine ⟨1975897292718050694703169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317264861812033796468779 1975897292718050694703169)
                  ·
                    refine ⟨1481922969538538021027377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1975897292718050694703169 1481922969538538021027377)
                    ·
                      refine ⟨1111442227153903515770533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481922969538538021027377 1111442227153903515770533)
                      ·
                        rfl

theorem cell23_2164526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2164526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164526 prefixEnd_2164526 := by exact prefixLift 2164526
  have htrace : WordTrace (prefixWord ++ tailWord_2164526) baseStart_2164526 baseEnd_2164526 := by
    simpa [prefixWord, tailWord_2164526, baseEnd_2164526] using wordTrace_append hprefix tailTrace_2164526
  have hstable : (prefixWord ++ tailWord_2164526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164526).length < 2 ^ (prefixWord ++ tailWord_2164526).sum := by decide
  have hdescent : baseEnd_2164526 < baseStart_2164526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164581 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_2164581 : Nat := 118140960795 + 2164581 * 2 ^ 59
def prefixEnd_2164581 : Nat := 4983230072969 + 3 ^ 40 * 2164581 * 2
def baseEnd_2164581 : Nat := 1111470468589900800582779

theorem tailTrace_2164581 : CollatzResearch.WordTrace tailWord_2164581 prefixEnd_2164581 1111470468589900800582779 := by
  unfold tailWord_2164581
  simp only [CollatzResearch.WordTrace]
  refine ⟨78948754971100192848101597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52632503314066795232067731 78948754971100192848101597)
  ·
    refine ⟨29605783114162572318038099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78948754971100192848101597 29605783114162572318038099)
    ·
      refine ⟨44408674671243858477057149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29605783114162572318038099 44408674671243858477057149)
      ·
        refine ⟨16653253001716446928896431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44408674671243858477057149 16653253001716446928896431)
        ·
          refine ⟨24979879502574670393344647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16653253001716446928896431 24979879502574670393344647)
          ·
            refine ⟨37469819253862005590016971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24979879502574670393344647 37469819253862005590016971)
            ·
              refine ⟨56204728880793008385025457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37469819253862005590016971 56204728880793008385025457)
              ·
                refine ⟨42153546660594756288769093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56204728880793008385025457 42153546660594756288769093)
                ·
                  refine ⟨7903789998861516804144205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42153546660594756288769093 7903789998861516804144205)
                  ·
                    refine ⟨2963921249573068801554077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7903789998861516804144205 2963921249573068801554077)
                    ·
                      refine ⟨1111470468589900800582779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2963921249573068801554077 1111470468589900800582779)
                      ·
                        rfl

theorem cell23_2164581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_2164581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164581 prefixEnd_2164581 := by exact prefixLift 2164581
  have htrace : WordTrace (prefixWord ++ tailWord_2164581) baseStart_2164581 baseEnd_2164581 := by
    simpa [prefixWord, tailWord_2164581, baseEnd_2164581] using wordTrace_append hprefix tailTrace_2164581
  have hstable : (prefixWord ++ tailWord_2164581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164581).length < 2 ^ (prefixWord ++ tailWord_2164581).sum := by decide
  have hdescent : baseEnd_2164581 < baseStart_2164581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164601 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_2164601 : Nat := 118140960795 + 2164601 * 2 ^ 59
def prefixEnd_2164601 : Nat := 4983230072969 + 3 ^ 40 * 2164601 * 2
def baseEnd_2164601 : Nat := 370493579400996907444229

theorem tailTrace_2164601 : CollatzResearch.WordTrace tailWord_2164601 prefixEnd_2164601 370493579400996907444229 := by
  unfold tailWord_2164601
  simp only [CollatzResearch.WordTrace]
  refine ⟨78949484431027736263829657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52632989620685157509219771 78949484431027736263829657)
  ·
    refine ⟨59212113323270802197872243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78949484431027736263829657 59212113323270802197872243)
    ·
      refine ⟨88818169984906203296808365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59212113323270802197872243 88818169984906203296808365)
      ·
        refine ⟨33306813744339826236303137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88818169984906203296808365 33306813744339826236303137)
        ·
          refine ⟨24980110308254869677227353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33306813744339826236303137 24980110308254869677227353)
          ·
            refine ⟨18735082731191152257920515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24980110308254869677227353 18735082731191152257920515)
            ·
              refine ⟨28102624096786728386880773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18735082731191152257920515 28102624096786728386880773)
              ·
                refine ⟨5269242018147511572540145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28102624096786728386880773 5269242018147511572540145)
                ·
                  refine ⟨3951931513610633679405109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269242018147511572540145 3951931513610633679405109)
                  ·
                    refine ⟨370493579400996907444229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3951931513610633679405109 370493579400996907444229)
                    ·
                      rfl

theorem cell23_2164601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_2164601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164601 prefixEnd_2164601 := by exact prefixLift 2164601
  have htrace : WordTrace (prefixWord ++ tailWord_2164601) baseStart_2164601 baseEnd_2164601 := by
    simpa [prefixWord, tailWord_2164601, baseEnd_2164601] using wordTrace_append hprefix tailTrace_2164601
  have hstable : (prefixWord ++ tailWord_2164601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164601).length < 2 ^ (prefixWord ++ tailWord_2164601).sum := by decide
  have hdescent : baseEnd_2164601 < baseStart_2164601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164611 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5]
def baseStart_2164611 : Nat := 118140960795 + 2164611 * 2 ^ 59
def prefixEnd_2164611 : Nat := 4983230072969 + 3 ^ 40 * 2164611 * 2
def baseEnd_2164611 : Nat := 1111485873009535683207641

theorem tailTrace_2164611 : CollatzResearch.WordTrace tailWord_2164611 prefixEnd_2164611 1111485873009535683207641 := by
  unfold tailWord_2164611
  simp only [CollatzResearch.WordTrace]
  refine ⟨78949849160991507971693687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52633232773994338647795791 78949849160991507971693687)
  ·
    refine ⟨118424773741487261957540531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78949849160991507971693687 118424773741487261957540531)
    ·
      refine ⟨177637160612230892936310797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118424773741487261957540531 177637160612230892936310797)
      ·
        refine ⟨66613935229586584851116549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177637160612230892936310797 66613935229586584851116549)
        ·
          refine ⟨12490112855547484659584353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66613935229586584851116549 12490112855547484659584353)
          ·
            refine ⟨9367584641660613494688265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12490112855547484659584353 9367584641660613494688265)
            ·
              refine ⟨7025688481245460121016199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9367584641660613494688265 7025688481245460121016199)
              ·
                refine ⟨10538532721868190181524299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7025688481245460121016199 10538532721868190181524299)
                ·
                  refine ⟨15807799082802285272286449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10538532721868190181524299 15807799082802285272286449)
                  ·
                    refine ⟨11855849312101713954214837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15807799082802285272286449 11855849312101713954214837)
                    ·
                      refine ⟨1111485873009535683207641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11855849312101713954214837 1111485873009535683207641)
                      ·
                        rfl

theorem cell23_2164611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_2164611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164611 prefixEnd_2164611 := by exact prefixLift 2164611
  have htrace : WordTrace (prefixWord ++ tailWord_2164611) baseStart_2164611 baseEnd_2164611 := by
    simpa [prefixWord, tailWord_2164611, baseEnd_2164611] using wordTrace_append hprefix tailTrace_2164611
  have hstable : (prefixWord ++ tailWord_2164611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164611).length < 2 ^ (prefixWord ++ tailWord_2164611).sum := by decide
  have hdescent : baseEnd_2164611 < baseStart_2164611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164658 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2164658 : Nat := 118140960795 + 2164658 * 2 ^ 59
def prefixEnd_2164658 : Nat := 4983230072969 + 3 ^ 40 * 2164658 * 2
def baseEnd_2164658 : Nat := 1111510006600296999319925

theorem tailTrace_2164658 : CollatzResearch.WordTrace tailWord_2164658 prefixEnd_2164658 1111510006600296999319925 := by
  unfold tailWord_2164658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19737890847955308749663657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52634375594547489999103085 19737890847955308749663657)
  ·
    refine ⟨14803418135966481562247743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19737890847955308749663657 14803418135966481562247743)
    ·
      refine ⟨22205127203949722343371615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14803418135966481562247743 22205127203949722343371615)
      ·
        refine ⟨33307690805924583515057423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22205127203949722343371615 33307690805924583515057423)
        ·
          refine ⟨49961536208886875272586135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33307690805924583515057423 49961536208886875272586135)
          ·
            refine ⟨74942304313330312908879203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49961536208886875272586135 74942304313330312908879203)
            ·
              refine ⟨112413456469995469363318805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74942304313330312908879203 112413456469995469363318805)
              ·
                refine ⟨5269380772031037626405569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112413456469995469363318805 5269380772031037626405569)
                ·
                  refine ⟨3952035579023278219804177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269380772031037626405569 3952035579023278219804177)
                  ·
                    refine ⟨2964026684267458664853133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3952035579023278219804177 2964026684267458664853133)
                    ·
                      refine ⟨1111510006600296999319925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2964026684267458664853133 1111510006600296999319925)
                      ·
                        rfl

theorem cell23_2164658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2164658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164658 prefixEnd_2164658 := by exact prefixLift 2164658
  have htrace : WordTrace (prefixWord ++ tailWord_2164658) baseStart_2164658 baseEnd_2164658 := by
    simpa [prefixWord, tailWord_2164658, baseEnd_2164658] using wordTrace_append hprefix tailTrace_2164658
  have hstable : (prefixWord ++ tailWord_2164658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164658).length < 2 ^ (prefixWord ++ tailWord_2164658).sum := by decide
  have hdescent : baseEnd_2164658 < baseStart_2164658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164665 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 1, 4]
def baseStart_2164665 : Nat := 118140960795 + 2164665 * 2 ^ 59
def prefixEnd_2164665 : Nat := 4983230072969 + 3 ^ 40 * 2164665 * 2
def baseEnd_2164665 : Nat := 370504533654959490644131

theorem tailTrace_2164665 : CollatzResearch.WordTrace tailWord_2164665 prefixEnd_2164665 370504533654959490644131 := by
  unfold tailWord_2164665
  simp only [CollatzResearch.WordTrace]
  refine ⟨78951818702795875194159449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52634545801863916796106299 78951818702795875194159449)
  ·
    refine ⟨59213864027096906395619587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78951818702795875194159449 59213864027096906395619587)
    ·
      refine ⟨88820796040645359593429381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59213864027096906395619587 88820796040645359593429381)
      ·
        refine ⟨16653899257621004923768009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88820796040645359593429381 16653899257621004923768009)
        ·
          refine ⟨12490424443215753692826007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16653899257621004923768009 12490424443215753692826007)
          ·
            refine ⟨18735636664823630539239011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12490424443215753692826007 18735636664823630539239011)
            ·
              refine ⟨28103454997235445808858517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18735636664823630539239011 28103454997235445808858517)
              ·
                refine ⟨1317349452995411522290243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28103454997235445808858517 1317349452995411522290243)
                ·
                  refine ⟨1976024179493117283435365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317349452995411522290243 1976024179493117283435365)
                  ·
                    refine ⟨370504533654959490644131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976024179493117283435365 370504533654959490644131)
                    ·
                      rfl

theorem cell23_2164665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 4].length) (baseStart_2164665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164665 prefixEnd_2164665 := by exact prefixLift 2164665
  have htrace : WordTrace (prefixWord ++ tailWord_2164665) baseStart_2164665 baseEnd_2164665 := by
    simpa [prefixWord, tailWord_2164665, baseEnd_2164665] using wordTrace_append hprefix tailTrace_2164665
  have hstable : (prefixWord ++ tailWord_2164665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164665).length < 2 ^ (prefixWord ++ tailWord_2164665).sum := by decide
  have hdescent : baseEnd_2164665 < baseStart_2164665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164708 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_2164708 : Nat := 118140960795 + 2164708 * 2 ^ 59
def prefixEnd_2164708 : Nat := 4983230072969 + 3 ^ 40 * 2164708 * 2
def baseEnd_2164708 : Nat := 370511893544340601231565

theorem tailTrace_2164708 : CollatzResearch.WordTrace tailWord_2164708 prefixEnd_2164708 370511893544340601231565 := by
  unfold tailWord_2164708
  simp only [CollatzResearch.WordTrace]
  refine ⟨39476693520820046768987389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52635591361093395691983185 39476693520820046768987389)
  ·
    refine ⟨14803760070307517538370271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39476693520820046768987389 14803760070307517538370271)
    ·
      refine ⟨22205640105461276307555407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14803760070307517538370271 22205640105461276307555407)
      ·
        refine ⟨33308460158191914461333111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22205640105461276307555407 33308460158191914461333111)
        ·
          refine ⟨49962690237287871691999667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33308460158191914461333111 49962690237287871691999667)
          ·
            refine ⟨74944035355931807537999501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49962690237287871691999667 74944035355931807537999501)
            ·
              refine ⟨28104013258474427826749813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74944035355931807537999501 28104013258474427826749813)
              ·
                refine ⟨2634751242981977608757795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28104013258474427826749813 2634751242981977608757795)
                ·
                  refine ⟨3952126864472966413136693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634751242981977608757795 3952126864472966413136693)
                  ·
                    refine ⟨370511893544340601231565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3952126864472966413136693 370511893544340601231565)
                    ·
                      rfl

theorem cell23_2164708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_2164708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164708 prefixEnd_2164708 := by exact prefixLift 2164708
  have htrace : WordTrace (prefixWord ++ tailWord_2164708) baseStart_2164708 baseEnd_2164708 := by
    simpa [prefixWord, tailWord_2164708, baseEnd_2164708] using wordTrace_append hprefix tailTrace_2164708
  have hstable : (prefixWord ++ tailWord_2164708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164708).length < 2 ^ (prefixWord ++ tailWord_2164708).sum := by decide
  have hdescent : baseEnd_2164708 < baseStart_2164708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164762 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4]
def baseStart_2164762 : Nat := 118140960795 + 2164762 * 2 ^ 59
def prefixEnd_2164762 : Nat := 4983230072969 + 3 ^ 40 * 2164762 * 2
def baseEnd_2164762 : Nat := 1111563408588364592419447

theorem tailTrace_2164762 : CollatzResearch.WordTrace tailWord_2164762 prefixEnd_2164762 1111563408588364592419447 := by
  unfold tailWord_2164762
  simp only [CollatzResearch.WordTrace]
  refine ⟨19738839145861115190110135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52636904388962973840293693 19738839145861115190110135)
  ·
    refine ⟨29608258718791672785165203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19738839145861115190110135 29608258718791672785165203)
    ·
      refine ⟨44412388078187509177747805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29608258718791672785165203 44412388078187509177747805)
      ·
        refine ⟨16654645529320315941655427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44412388078187509177747805 16654645529320315941655427)
        ·
          refine ⟨24981968293980473912483141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16654645529320315941655427 24981968293980473912483141)
          ·
            refine ⟨4684119055121338858590589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24981968293980473912483141 4684119055121338858590589)
            ·
              refine ⟨1756544645670502071971471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4684119055121338858590589 1756544645670502071971471)
              ·
                refine ⟨2634816968505753107957207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756544645670502071971471 2634816968505753107957207)
                ·
                  refine ⟨3952225452758629661935811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634816968505753107957207 3952225452758629661935811)
                  ·
                    refine ⟨5928338179137944492903717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3952225452758629661935811 5928338179137944492903717)
                    ·
                      refine ⟨1111563408588364592419447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5928338179137944492903717 1111563408588364592419447)
                      ·
                        rfl

theorem cell23_2164762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_2164762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164762 prefixEnd_2164762 := by exact prefixLift 2164762
  have htrace : WordTrace (prefixWord ++ tailWord_2164762) baseStart_2164762 baseEnd_2164762 := by
    simpa [prefixWord, tailWord_2164762, baseEnd_2164762] using wordTrace_append hprefix tailTrace_2164762
  have hstable : (prefixWord ++ tailWord_2164762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164762).length < 2 ^ (prefixWord ++ tailWord_2164762).sum := by decide
  have hdescent : baseEnd_2164762 < baseStart_2164762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164765 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2164765 : Nat := 118140960795 + 2164765 * 2 ^ 59
def prefixEnd_2164765 : Nat := 4983230072969 + 3 ^ 40 * 2164765 * 2
def baseEnd_2164765 : Nat := 1111564949030328080681933

theorem tailTrace_2164765 : CollatzResearch.WordTrace tailWord_2164765 prefixEnd_2164765 1111564949030328080681933 := by
  unfold tailWord_2164765
  simp only [CollatzResearch.WordTrace]
  refine ⟨78955466002433592272799749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52636977334955728181866499 78955466002433592272799749)
  ·
    refine ⟨14804149875456298551149953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78955466002433592272799749 14804149875456298551149953)
    ·
      refine ⟨11103112406592223913362465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14804149875456298551149953 11103112406592223913362465)
      ·
        refine ⟨8327334304944167935021849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11103112406592223913362465 8327334304944167935021849)
        ·
          refine ⟨6245500728708125951266387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8327334304944167935021849 6245500728708125951266387)
          ·
            refine ⟨9368251093062188926899581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6245500728708125951266387 9368251093062188926899581)
            ·
              refine ⟨3513094159898320847587343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9368251093062188926899581 3513094159898320847587343)
              ·
                refine ⟨5269641239847481271381015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513094159898320847587343 5269641239847481271381015)
                ·
                  refine ⟨7904461859771221907071523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269641239847481271381015 7904461859771221907071523)
                  ·
                    refine ⟨11856692789656832860607285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7904461859771221907071523 11856692789656832860607285)
                    ·
                      refine ⟨1111564949030328080681933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11856692789656832860607285 1111564949030328080681933)
                      ·
                        rfl

theorem cell23_2164765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2164765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164765 prefixEnd_2164765 := by exact prefixLift 2164765
  have htrace : WordTrace (prefixWord ++ tailWord_2164765) baseStart_2164765 baseEnd_2164765 := by
    simpa [prefixWord, tailWord_2164765, baseEnd_2164765] using wordTrace_append hprefix tailTrace_2164765
  have hstable : (prefixWord ++ tailWord_2164765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164765).length < 2 ^ (prefixWord ++ tailWord_2164765).sum := by decide
  have hdescent : baseEnd_2164765 < baseStart_2164765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164829 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2164829 : Nat := 118140960795 + 2164829 * 2 ^ 59
def prefixEnd_2164829 : Nat := 4983230072969 + 3 ^ 40 * 2164829 * 2
def baseEnd_2164829 : Nat := 1111597811792215830281639

theorem tailTrace_2164829 : CollatzResearch.WordTrace tailWord_2164829 prefixEnd_2164829 1111597811792215830281639 := by
  unfold tailWord_2164829
  simp only [CollatzResearch.WordTrace]
  refine ⟨78957800274201731203129541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52638533516134487468753027 78957800274201731203129541)
  ·
    refine ⟨14804587551412824600586789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78957800274201731203129541 14804587551412824600586789)
    ·
      refine ⟨2775860165889904612610023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14804587551412824600586789 2775860165889904612610023)
      ·
        refine ⟨4163790248834856918915035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775860165889904612610023 4163790248834856918915035)
        ·
          refine ⟨6245685373252285378372553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163790248834856918915035 6245685373252285378372553)
          ·
            refine ⟨4684264029939214033779415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6245685373252285378372553 4684264029939214033779415)
            ·
              refine ⟨7026396044908821050669123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684264029939214033779415 7026396044908821050669123)
              ·
                refine ⟨10539594067363231576003685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026396044908821050669123 10539594067363231576003685)
                ·
                  refine ⟨1976173887630605920500691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10539594067363231576003685 1976173887630605920500691)
                  ·
                    refine ⟨2964260831445908880751037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976173887630605920500691 2964260831445908880751037)
                    ·
                      refine ⟨1111597811792215830281639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2964260831445908880751037 1111597811792215830281639)
                      ·
                        rfl

theorem cell23_2164829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2164829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164829 prefixEnd_2164829 := by exact prefixLift 2164829
  have htrace : WordTrace (prefixWord ++ tailWord_2164829) baseStart_2164829 baseEnd_2164829 := by
    simpa [prefixWord, tailWord_2164829, baseEnd_2164829] using wordTrace_append hprefix tailTrace_2164829
  have hstable : (prefixWord ++ tailWord_2164829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164829).length < 2 ^ (prefixWord ++ tailWord_2164829).sum := by decide
  have hdescent : baseEnd_2164829 < baseStart_2164829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164835 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 3, 4, 2]
def baseStart_2164835 : Nat := 118140960795 + 2164835 * 2 ^ 59
def prefixEnd_2164835 : Nat := 4983230072969 + 3 ^ 40 * 2164835 * 2
def baseEnd_2164835 : Nat := 1111600892676142806806611

theorem tailTrace_2164835 : CollatzResearch.WordTrace tailWord_2164835 prefixEnd_2164835 1111600892676142806806611 := by
  unfold tailWord_2164835
  simp only [CollatzResearch.WordTrace]
  refine ⟨78958019112179994227847959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52638679408119996151898639 78958019112179994227847959)
  ·
    refine ⟨118437028668269991341771939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78958019112179994227847959 118437028668269991341771939)
    ·
      refine ⟨177655543002404987012657909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118437028668269991341771939 177655543002404987012657909)
      ·
        refine ⟨16655207156475467532436679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177655543002404987012657909 16655207156475467532436679)
        ·
          refine ⟨24982810734713201298655019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16655207156475467532436679 24982810734713201298655019)
          ·
            refine ⟨37474216102069801947982529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24982810734713201298655019 37474216102069801947982529)
            ·
              refine ⟨28105662076552351460986897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37474216102069801947982529 28105662076552351460986897)
              ·
                refine ⟨21079246557414263595740173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28105662076552351460986897 21079246557414263595740173)
                ·
                  refine ⟨7904717459030348848402565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21079246557414263595740173 7904717459030348848402565)
                  ·
                    refine ⟨1482134523568190409075481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7904717459030348848402565 1482134523568190409075481)
                    ·
                      refine ⟨1111600892676142806806611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482134523568190409075481 1111600892676142806806611)
                      ·
                        rfl

theorem cell23_2164835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_2164835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164835 prefixEnd_2164835 := by exact prefixLift 2164835
  have htrace : WordTrace (prefixWord ++ tailWord_2164835) baseStart_2164835 baseEnd_2164835 := by
    simpa [prefixWord, tailWord_2164835, baseEnd_2164835] using wordTrace_append hprefix tailTrace_2164835
  have hstable : (prefixWord ++ tailWord_2164835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164835).length < 2 ^ (prefixWord ++ tailWord_2164835).sum := by decide
  have hdescent : baseEnd_2164835 < baseStart_2164835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164942 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2164942 : Nat := 118140960795 + 2164942 * 2 ^ 59
def prefixEnd_2164942 : Nat := 4983230072969 + 3 ^ 40 * 2164942 * 2
def baseEnd_2164942 : Nat := 1111655835106173888168619

theorem tailTrace_2164942 : CollatzResearch.WordTrace tailWord_2164942 prefixEnd_2164942 1111655835106173888168619 := by
  unfold tailWord_2164942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870240215349043937749135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52641281148528234334662053 9870240215349043937749135)
  ·
    refine ⟨14805360323023565906623703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9870240215349043937749135 14805360323023565906623703)
    ·
      refine ⟨22208040484535348859935555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14805360323023565906623703 22208040484535348859935555)
      ·
        refine ⟨33312060726803023289903333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22208040484535348859935555 33312060726803023289903333)
        ·
          refine ⟨6246011386275566866856875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33312060726803023289903333 6246011386275566866856875)
          ·
            refine ⟨9369017079413350300285313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246011386275566866856875 9369017079413350300285313)
            ·
              refine ⟨7026762809560012725213985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9369017079413350300285313 7026762809560012725213985)
              ·
                refine ⟨5270072107170009543910489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7026762809560012725213985 5270072107170009543910489)
                ·
                  refine ⟨3952554080377507157932867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5270072107170009543910489 3952554080377507157932867)
                  ·
                    refine ⟨5928831120566260736899301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3952554080377507157932867 5928831120566260736899301)
                    ·
                      refine ⟨1111655835106173888168619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5928831120566260736899301 1111655835106173888168619)
                      ·
                        rfl

theorem cell23_2164942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2164942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164942 prefixEnd_2164942 := by exact prefixLift 2164942
  have htrace : WordTrace (prefixWord ++ tailWord_2164942) baseStart_2164942 baseEnd_2164942 := by
    simpa [prefixWord, tailWord_2164942, baseEnd_2164942] using wordTrace_append hprefix tailTrace_2164942
  have hstable : (prefixWord ++ tailWord_2164942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164942).length < 2 ^ (prefixWord ++ tailWord_2164942).sum := by decide
  have hdescent : baseEnd_2164942 < baseStart_2164942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165009 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_2165009 : Nat := 118140960795 + 2165009 * 2 ^ 59
def prefixEnd_2165009 : Nat := 4983230072969 + 3 ^ 40 * 2165009 * 2
def baseEnd_2165009 : Nat := 1111690238310025126030811

theorem tailTrace_2165009 : CollatzResearch.WordTrace tailWord_2165009 prefixEnd_2165009 1111690238310025126030811 := by
  unfold tailWord_2165009
  simp only [CollatzResearch.WordTrace]
  refine ⟨78964365413549621944682081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52642910275699747963121387 78964365413549621944682081)
  ·
    refine ⟨59223274060162216458511561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78964365413549621944682081 59223274060162216458511561)
    ·
      refine ⟨44417455545121662343883671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59223274060162216458511561 44417455545121662343883671)
      ·
        refine ⟨66626183317682493515825507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44417455545121662343883671 66626183317682493515825507)
        ·
          refine ⟨99939274976523740273738261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66626183317682493515825507 99939274976523740273738261)
          ·
            refine ⟨4684653514524550325331481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99939274976523740273738261 4684653514524550325331481)
            ·
              refine ⟨3513490135893412743998611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4684653514524550325331481 3513490135893412743998611)
              ·
                refine ⟨5270235203840119115997917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513490135893412743998611 5270235203840119115997917)
                ·
                  refine ⟨1976338201440044668499219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5270235203840119115997917 1976338201440044668499219)
                  ·
                    refine ⟨2964507302160067002748829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976338201440044668499219 2964507302160067002748829)
                    ·
                      refine ⟨1111690238310025126030811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2964507302160067002748829 1111690238310025126030811)
                      ·
                        rfl

theorem cell23_2165009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_2165009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165009 prefixEnd_2165009 := by exact prefixLift 2165009
  have htrace : WordTrace (prefixWord ++ tailWord_2165009) baseStart_2165009 baseEnd_2165009 := by
    simpa [prefixWord, tailWord_2165009, baseEnd_2165009] using wordTrace_append hprefix tailTrace_2165009
  have hstable : (prefixWord ++ tailWord_2165009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165009).length < 2 ^ (prefixWord ++ tailWord_2165009).sum := by decide
  have hdescent : baseEnd_2165009 < baseStart_2165009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165029 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_2165029 : Nat := 118140960795 + 2165029 * 2 ^ 59
def prefixEnd_2165029 : Nat := 4983230072969 + 3 ^ 40 * 2165029 * 2
def baseEnd_2165029 : Nat := 370566835974371682593573

theorem tailTrace_2165029 : CollatzResearch.WordTrace tailWord_2165029 prefixEnd_2165029 370566835974371682593573 := by
  unfold tailWord_2165029
  simp only [CollatzResearch.WordTrace]
  refine ⟨78965094873477165360410141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52643396582318110240273427 78965094873477165360410141)
  ·
    refine ⟨29611910577553937010153803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78965094873477165360410141 29611910577553937010153803)
    ·
      refine ⟨44417865866330905515230705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29611910577553937010153803 44417865866330905515230705)
      ·
        refine ⟨33313399399748179136423029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44417865866330905515230705 33313399399748179136423029)
        ·
          refine ⟨3123131193726391794039659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33313399399748179136423029 3123131193726391794039659)
          ·
            refine ⟨4684696790589587691059489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123131193726391794039659 4684696790589587691059489)
            ·
              refine ⟨3513522592942190768294617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4684696790589587691059489 3513522592942190768294617)
              ·
                refine ⟨2635141944706643076220963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513522592942190768294617 2635141944706643076220963)
                ·
                  refine ⟨3952712917059964614331445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635141944706643076220963 3952712917059964614331445)
                  ·
                    refine ⟨370566835974371682593573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3952712917059964614331445 370566835974371682593573)
                    ·
                      rfl

theorem cell23_2165029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_2165029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165029 prefixEnd_2165029 := by exact prefixLift 2165029
  have htrace : WordTrace (prefixWord ++ tailWord_2165029) baseStart_2165029 baseEnd_2165029 := by
    simpa [prefixWord, tailWord_2165029, baseEnd_2165029] using wordTrace_append hprefix tailTrace_2165029
  have hstable : (prefixWord ++ tailWord_2165029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165029).length < 2 ^ (prefixWord ++ tailWord_2165029).sum := by decide
  have hdescent : baseEnd_2165029 < baseStart_2165029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165049 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2165049 : Nat := 118140960795 + 2165049 * 2 ^ 59
def prefixEnd_2165049 : Nat := 4983230072969 + 3 ^ 40 * 2165049 * 2
def baseEnd_2165049 : Nat := 1111710777536204969530627

theorem tailTrace_2165049 : CollatzResearch.WordTrace tailWord_2165049 prefixEnd_2165049 1111710777536204969530627 := by
  unfold tailWord_2165049
  simp only [CollatzResearch.WordTrace]
  refine ⟨78965824333404708776138201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52643882888936472517425467 78965824333404708776138201)
  ·
    refine ⟨59224368250053531582103651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78965824333404708776138201 59224368250053531582103651)
    ·
      refine ⟨88836552375080297373155477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59224368250053531582103651 88836552375080297373155477)
      ·
        refine ⟨4164213392581888939366663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88836552375080297373155477 4164213392581888939366663)
        ·
          refine ⟨6246320088872833409049995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164213392581888939366663 6246320088872833409049995)
          ·
            refine ⟨9369480133309250113574993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246320088872833409049995 9369480133309250113574993)
            ·
              refine ⟨7027110099981937585181245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9369480133309250113574993 7027110099981937585181245)
              ·
                refine ⟨2635166287493226594442967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7027110099981937585181245 2635166287493226594442967)
                ·
                  refine ⟨3952749431239839891664451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635166287493226594442967 3952749431239839891664451)
                  ·
                    refine ⟨5929124146859759837496677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3952749431239839891664451 5929124146859759837496677)
                    ·
                      refine ⟨1111710777536204969530627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5929124146859759837496677 1111710777536204969530627)
                      ·
                        rfl

theorem cell23_2165049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2165049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165049 prefixEnd_2165049 := by exact prefixLift 2165049
  have htrace : WordTrace (prefixWord ++ tailWord_2165049) baseStart_2165049 baseEnd_2165049 := by
    simpa [prefixWord, tailWord_2165049, baseEnd_2165049] using wordTrace_append hprefix tailTrace_2165049
  have hstable : (prefixWord ++ tailWord_2165049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165049).length < 2 ^ (prefixWord ++ tailWord_2165049).sum := by decide
  have hdescent : baseEnd_2165049 < baseStart_2165049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165052 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_2165052 : Nat := 118140960795 + 2165052 * 2 ^ 59
def prefixEnd_2165052 : Nat := 4983230072969 + 3 ^ 40 * 2165052 * 2
def baseEnd_2165052 : Nat := 1111712317978168457793113

theorem tailTrace_2165052 : CollatzResearch.WordTrace tailWord_2165052 prefixEnd_2165052 1111712317978168457793113 := by
  unfold tailWord_2165052
  simp only [CollatzResearch.WordTrace]
  refine ⟨39482966876196920144248705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52643955834929226858998273 39482966876196920144248705)
  ·
    refine ⟨29612225157147690108186529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39482966876196920144248705 29612225157147690108186529)
    ·
      refine ⟨22209168867860767581139897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29612225157147690108186529 22209168867860767581139897)
      ·
        refine ⟨16656876650895575685854923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22209168867860767581139897 16656876650895575685854923)
        ·
          refine ⟨24985314976343363528782385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16656876650895575685854923 24985314976343363528782385)
          ·
            refine ⟨18738986232257522646586789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24985314976343363528782385 18738986232257522646586789)
            ·
              refine ⟨3513559918548285496235023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18738986232257522646586789 3513559918548285496235023)
              ·
                refine ⟨5270339877822428244352535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513559918548285496235023 5270339877822428244352535)
                ·
                  refine ⟨7905509816733642366528803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270339877822428244352535 7905509816733642366528803)
                  ·
                    refine ⟨11858264725100463549793205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7905509816733642366528803 11858264725100463549793205)
                    ·
                      refine ⟨1111712317978168457793113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11858264725100463549793205 1111712317978168457793113)
                      ·
                        rfl

theorem cell23_2165052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_2165052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165052 prefixEnd_2165052 := by exact prefixLift 2165052
  have htrace : WordTrace (prefixWord ++ tailWord_2165052) baseStart_2165052 baseEnd_2165052 := by
    simpa [prefixWord, tailWord_2165052, baseEnd_2165052] using wordTrace_append hprefix tailTrace_2165052
  have hstable : (prefixWord ++ tailWord_2165052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165052).length < 2 ^ (prefixWord ++ tailWord_2165052).sum := by decide
  have hdescent : baseEnd_2165052 < baseStart_2165052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165060 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2165060 : Nat := 118140960795 + 2165060 * 2 ^ 59
def prefixEnd_2165060 : Nat := 4983230072969 + 3 ^ 40 * 2165060 * 2
def baseEnd_2165060 : Nat := 1111716425823404426493077

theorem tailTrace_2165060 : CollatzResearch.WordTrace tailWord_2165060 prefixEnd_2165060 1111716425823404426493077 := by
  unfold tailWord_2165060
  simp only [CollatzResearch.WordTrace]
  refine ⟨39483112768182428827394317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52644150357576571769859089 39483112768182428827394317)
  ·
    refine ⟨14806167288068410810272869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39483112768182428827394317 14806167288068410810272869)
    ·
      refine ⟨2776156366512827026926163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14806167288068410810272869 2776156366512827026926163)
      ·
        refine ⟨4164234549769240540389245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776156366512827026926163 4164234549769240540389245)
        ·
          refine ⟨1561587956163465202645967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4164234549769240540389245 1561587956163465202645967)
          ·
            refine ⟨2342381934245197803968951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561587956163465202645967 2342381934245197803968951)
            ·
              refine ⟨3513572901367796705953427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342381934245197803968951 3513572901367796705953427)
              ·
                refine ⟨5270359352051695058930141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513572901367796705953427 5270359352051695058930141)
                ·
                  refine ⟨1976384757019385647098803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5270359352051695058930141 1976384757019385647098803)
                  ·
                    refine ⟨2964577135529078470648205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976384757019385647098803 2964577135529078470648205)
                    ·
                      refine ⟨1111716425823404426493077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2964577135529078470648205 1111716425823404426493077)
                      ·
                        rfl

theorem cell23_2165060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2165060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165060 prefixEnd_2165060 := by exact prefixLift 2165060
  have htrace : WordTrace (prefixWord ++ tailWord_2165060) baseStart_2165060 baseEnd_2165060 := by
    simpa [prefixWord, tailWord_2165060, baseEnd_2165060] using wordTrace_append hprefix tailTrace_2165060
  have hstable : (prefixWord ++ tailWord_2165060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165060).length < 2 ^ (prefixWord ++ tailWord_2165060).sum := by decide
  have hdescent : baseEnd_2165060 < baseStart_2165060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165076 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_2165076 : Nat := 118140960795 + 2165076 * 2 ^ 59
def prefixEnd_2165076 : Nat := 4983230072969 + 3 ^ 40 * 2165076 * 2
def baseEnd_2165076 : Nat := 370574880504625454631001

theorem tailTrace_2165076 : CollatzResearch.WordTrace tailWord_2165076 prefixEnd_2165076 370574880504625454631001 := by
  unfold tailWord_2165076
  simp only [CollatzResearch.WordTrace]
  refine ⟨39483404552153446193685541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52644539402871261591580721 39483404552153446193685541)
  ·
    refine ⟨7403138353528771161316039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39483404552153446193685541 7403138353528771161316039)
    ·
      refine ⟨11104707530293156741974059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7403138353528771161316039 11104707530293156741974059)
      ·
        refine ⟨16657061295439735112961089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11104707530293156741974059 16657061295439735112961089)
        ·
          refine ⟨12492795971579801334720817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16657061295439735112961089 12492795971579801334720817)
          ·
            refine ⟨9369596978684851001040613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12492795971579801334720817 9369596978684851001040613)
            ·
              refine ⟨1756799433503409562695115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9369596978684851001040613 1756799433503409562695115)
              ·
                refine ⟨2635199150255114344042673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756799433503409562695115 2635199150255114344042673)
                ·
                  refine ⟨1976399362691335758032005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635199150255114344042673 1976399362691335758032005)
                  ·
                    refine ⟨370574880504625454631001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976399362691335758032005 370574880504625454631001)
                    ·
                      rfl

theorem cell23_2165076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_2165076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165076 prefixEnd_2165076 := by exact prefixLift 2165076
  have htrace : WordTrace (prefixWord ++ tailWord_2165076) baseStart_2165076 baseEnd_2165076 := by
    simpa [prefixWord, tailWord_2165076, baseEnd_2165076] using wordTrace_append hprefix tailTrace_2165076
  have hstable : (prefixWord ++ tailWord_2165076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165076).length < 2 ^ (prefixWord ++ tailWord_2165076).sum := by decide
  have hdescent : baseEnd_2165076 < baseStart_2165076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165082 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_2165082 : Nat := 118140960795 + 2165082 * 2 ^ 59
def prefixEnd_2165082 : Nat := 4983230072969 + 3 ^ 40 * 2165082 * 2
def baseEnd_2165082 : Nat := 1111727722397803340417975

theorem tailTrace_2165082 : CollatzResearch.WordTrace tailWord_2165082 prefixEnd_2165082 1111727722397803340417975 := by
  unfold tailWord_2165082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19741756985571288853022375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52644685294856770274726333 19741756985571288853022375)
  ·
    refine ⟨29612635478356933279533563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19741756985571288853022375 29612635478356933279533563)
    ·
      refine ⟨44418953217535399919300345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29612635478356933279533563 44418953217535399919300345)
      ·
        refine ⟨33314214913151549939475259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44418953217535399919300345 33314214913151549939475259)
        ·
          refine ⟨49971322369727324909212889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33314214913151549939475259 49971322369727324909212889)
          ·
            refine ⟨37478491777295493681909667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49971322369727324909212889 37478491777295493681909667)
            ·
              refine ⟨56217737665943240522864501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37478491777295493681909667 56217737665943240522864501)
              ·
                refine ⟨5270412906182178799018547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56217737665943240522864501 5270412906182178799018547)
                ·
                  refine ⟨7905619359273268198527821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5270412906182178799018547 7905619359273268198527821)
                  ·
                    refine ⟨2964607259727475574447933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7905619359273268198527821 2964607259727475574447933)
                    ·
                      refine ⟨1111727722397803340417975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2964607259727475574447933 1111727722397803340417975)
                      ·
                        rfl

theorem cell23_2165082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_2165082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165082 prefixEnd_2165082 := by exact prefixLift 2165082
  have htrace : WordTrace (prefixWord ++ tailWord_2165082) baseStart_2165082 baseEnd_2165082 := by
    simpa [prefixWord, tailWord_2165082, baseEnd_2165082] using wordTrace_append hprefix tailTrace_2165082
  have hstable : (prefixWord ++ tailWord_2165082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165082).length < 2 ^ (prefixWord ++ tailWord_2165082).sum := by decide
  have hdescent : baseEnd_2165082 < baseStart_2165082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165132 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_2165132 : Nat := 118140960795 + 2165132 * 2 ^ 59
def prefixEnd_2165132 : Nat := 4983230072969 + 3 ^ 40 * 2165132 * 2
def baseEnd_2165132 : Nat := 370584465476842714930915

theorem tailTrace_2165132 : CollatzResearch.WordTrace tailWord_2165132 prefixEnd_2165132 370584465476842714930915 := by
  unfold tailWord_2165132
  simp only [CollatzResearch.WordTrace]
  refine ⟨39484425796052006975704825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52645901061402675967606433 39484425796052006975704825)
  ·
    refine ⟨29613319347039005231778619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39484425796052006975704825 29613319347039005231778619)
    ·
      refine ⟨44419979020558507847667929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29613319347039005231778619 44419979020558507847667929)
      ·
        refine ⟨33314984265418880885750947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44419979020558507847667929 33314984265418880885750947)
        ·
          refine ⟨49972476398128321328626421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33314984265418880885750947 49972476398128321328626421)
          ·
            refine ⟨4684919662324530124558727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49972476398128321328626421 4684919662324530124558727)
            ·
              refine ⟨7027379493486795186838091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684919662324530124558727 7027379493486795186838091)
              ·
                refine ⟨10541069240230192780257137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027379493486795186838091 10541069240230192780257137)
                ·
                  refine ⟨7905801930172644585192853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10541069240230192780257137 7905801930172644585192853)
                  ·
                    refine ⟨370584465476842714930915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7905801930172644585192853 370584465476842714930915)
                    ·
                      rfl

theorem cell23_2165132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_2165132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165132 prefixEnd_2165132 := by exact prefixLift 2165132
  have htrace : WordTrace (prefixWord ++ tailWord_2165132) baseStart_2165132 baseEnd_2165132 := by
    simpa [prefixWord, tailWord_2165132, baseEnd_2165132] using wordTrace_append hprefix tailTrace_2165132
  have hstable : (prefixWord ++ tailWord_2165132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165132).length < 2 ^ (prefixWord ++ tailWord_2165132).sum := by decide
  have hdescent : baseEnd_2165132 < baseStart_2165132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165160 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2165160 : Nat := 118140960795 + 2165160 * 2 ^ 59
def prefixEnd_2165160 : Nat := 4983230072969 + 3 ^ 40 * 2165160 * 2
def baseEnd_2165160 : Nat := 1111767773888854035242617

theorem tailTrace_2165160 : CollatzResearch.WordTrace tailWord_2165160 prefixEnd_2165160 1111767773888854035242617 := by
  unfold tailWord_2165160
  simp only [CollatzResearch.WordTrace]
  refine ⟨39484936418001287366714467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52646581890668383155619289 39484936418001287366714467)
  ·
    refine ⟨59227404627001931050071701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39484936418001287366714467 59227404627001931050071701)
    ·
      refine ⟨2776284591890715517972111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59227404627001931050071701 2776284591890715517972111)
      ·
        refine ⟨4164426887836073276958167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776284591890715517972111 4164426887836073276958167)
        ·
          refine ⟨6246640331754109915437251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164426887836073276958167 6246640331754109915437251)
          ·
            refine ⟨9369960497631164873155877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246640331754109915437251 9369960497631164873155877)
            ·
              refine ⟨1756867593305843413716727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9369960497631164873155877 1756867593305843413716727)
              ·
                refine ⟨2635301389958765120575091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756867593305843413716727 2635301389958765120575091)
                ·
                  refine ⟨3952952084938147680862637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635301389958765120575091 3952952084938147680862637)
                  ·
                    refine ⟨1482357031851805380323489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3952952084938147680862637 1482357031851805380323489)
                    ·
                      refine ⟨1111767773888854035242617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482357031851805380323489 1111767773888854035242617)
                      ·
                        rfl

theorem cell23_2165160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2165160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165160 prefixEnd_2165160 := by exact prefixLift 2165160
  have htrace : WordTrace (prefixWord ++ tailWord_2165160) baseStart_2165160 baseEnd_2165160 := by
    simpa [prefixWord, tailWord_2165160, baseEnd_2165160] using wordTrace_append hprefix tailTrace_2165160
  have hstable : (prefixWord ++ tailWord_2165160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165160).length < 2 ^ (prefixWord ++ tailWord_2165160).sum := by decide
  have hdescent : baseEnd_2165160 < baseStart_2165160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165173 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_2165173 : Nat := 118140960795 + 2165173 * 2 ^ 59
def prefixEnd_2165173 : Nat := 4983230072969 + 3 ^ 40 * 2165173 * 2
def baseEnd_2165173 : Nat := 1111774449137362484380057

theorem tailTrace_2165173 : CollatzResearch.WordTrace tailWord_2165173 prefixEnd_2165173 1111774449137362484380057 := by
  unfold tailWord_2165173
  simp only [CollatzResearch.WordTrace]
  refine ⟨78970346984955477953652173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52646897989970318635768115 78970346984955477953652173)
  ·
    refine ⟨29613880119358304232619565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78970346984955477953652173 29613880119358304232619565)
    ·
      refine ⟨11105205044759364087232337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29613880119358304232619565 11105205044759364087232337)
      ·
        refine ⟨8328903783569523065424253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11105205044759364087232337 8328903783569523065424253)
        ·
          refine ⟨3123338918838571149534095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8328903783569523065424253 3123338918838571149534095)
          ·
            refine ⟨4685008378257856724301143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123338918838571149534095 4685008378257856724301143)
            ·
              refine ⟨7027512567386785086451715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685008378257856724301143 7027512567386785086451715)
              ·
                refine ⟨10541268851080177629677573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027512567386785086451715 10541268851080177629677573)
                ·
                  refine ⟨1976487909577533305564545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10541268851080177629677573 1976487909577533305564545)
                  ·
                    refine ⟨1482365932183149979173409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1976487909577533305564545 1482365932183149979173409)
                    ·
                      refine ⟨1111774449137362484380057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482365932183149979173409 1111774449137362484380057)
                      ·
                        rfl

theorem cell23_2165173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_2165173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165173 prefixEnd_2165173 := by exact prefixLift 2165173
  have htrace : WordTrace (prefixWord ++ tailWord_2165173) baseStart_2165173 baseEnd_2165173 := by
    simpa [prefixWord, tailWord_2165173, baseEnd_2165173] using wordTrace_append hprefix tailTrace_2165173
  have hstable : (prefixWord ++ tailWord_2165173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165173).length < 2 ^ (prefixWord ++ tailWord_2165173).sum := by decide
  have hdescent : baseEnd_2165173 < baseStart_2165173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165192 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2165192 : Nat := 118140960795 + 2165192 * 2 ^ 59
def prefixEnd_2165192 : Nat := 4983230072969 + 3 ^ 40 * 2165192 * 2
def baseEnd_2165192 : Nat := 370594735089932636680823

theorem tailTrace_2165192 : CollatzResearch.WordTrace tailWord_2165192 prefixEnd_2165192 370594735089932636680823 := by
  unfold tailWord_2165192
  simp only [CollatzResearch.WordTrace]
  refine ⟨39485519985943322099296915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52647359981257762799062553 39485519985943322099296915)
  ·
    refine ⟨59228279978914983148945373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39485519985943322099296915 59228279978914983148945373)
    ·
      refine ⟨22210604992093118680854515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59228279978914983148945373 22210604992093118680854515)
      ·
        refine ⟨33315907488139678021281773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22210604992093118680854515 33315907488139678021281773)
        ·
          refine ⟨12493465308052379257980665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33315907488139678021281773 12493465308052379257980665)
          ·
            refine ⟨9370098981039284443485499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12493465308052379257980665 9370098981039284443485499)
            ·
              refine ⟨14055148471558926665228249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9370098981039284443485499 14055148471558926665228249)
              ·
                refine ⟨10541361353669194998921187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14055148471558926665228249 10541361353669194998921187)
                ·
                  refine ⟨15812042030503792498381781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10541361353669194998921187 15812042030503792498381781)
                  ·
                    refine ⟨370594735089932636680823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15812042030503792498381781 370594735089932636680823)
                    ·
                      rfl

theorem cell23_2165192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2165192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165192 prefixEnd_2165192 := by exact prefixLift 2165192
  have htrace : WordTrace (prefixWord ++ tailWord_2165192) baseStart_2165192 baseEnd_2165192 := by
    simpa [prefixWord, tailWord_2165192, baseEnd_2165192] using wordTrace_append hprefix tailTrace_2165192
  have hstable : (prefixWord ++ tailWord_2165192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165192).length < 2 ^ (prefixWord ++ tailWord_2165192).sum := by decide
  have hdescent : baseEnd_2165192 < baseStart_2165192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165242 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_2165242 : Nat := 118140960795 + 2165242 * 2 ^ 59
def prefixEnd_2165242 : Nat := 4983230072969 + 3 ^ 40 * 2165242 * 2
def baseEnd_2165242 : Nat := 1111809879302522714417239

theorem tailTrace_2165242 : CollatzResearch.WordTrace tailWord_2165242 prefixEnd_2165242 1111809879302522714417239 := by
  unfold tailWord_2165242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19743215905426375684478495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52648575747803668491942653 19743215905426375684478495)
  ·
    refine ⟨29614823858139563526717743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19743215905426375684478495 29614823858139563526717743)
    ·
      refine ⟨44422235787209345290076615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29614823858139563526717743 44422235787209345290076615)
      ·
        refine ⟨66633353680814017935114923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44422235787209345290076615 66633353680814017935114923)
        ·
          refine ⟨99950030521221026902672385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66633353680814017935114923 99950030521221026902672385)
          ·
            refine ⟨74962522890915770177004289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99950030521221026902672385 74962522890915770177004289)
            ·
              refine ⟨56221892168186827632753217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74962522890915770177004289 56221892168186827632753217)
              ·
                refine ⟨42166419126140120724564913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56221892168186827632753217 42166419126140120724564913)
                ·
                  refine ⟨31624814344605090543423685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42166419126140120724564913 31624814344605090543423685)
                  ·
                    refine ⟨5929652689613454476891941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31624814344605090543423685 5929652689613454476891941)
                    ·
                      refine ⟨1111809879302522714417239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5929652689613454476891941 1111809879302522714417239)
                      ·
                        rfl

theorem cell23_2165242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_2165242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165242 prefixEnd_2165242 := by exact prefixLift 2165242
  have htrace : WordTrace (prefixWord ++ tailWord_2165242) baseStart_2165242 baseEnd_2165242 := by
    simpa [prefixWord, tailWord_2165242, baseEnd_2165242] using wordTrace_append hprefix tailTrace_2165242
  have hstable : (prefixWord ++ tailWord_2165242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165242).length < 2 ^ (prefixWord ++ tailWord_2165242).sum := by decide
  have hdescent : baseEnd_2165242 < baseStart_2165242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165290 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2165290 : Nat := 118140960795 + 2165290 * 2 ^ 59
def prefixEnd_2165290 : Nat := 4983230072969 + 3 ^ 40 * 2165290 * 2
def baseEnd_2165290 : Nat := 370611508791312842205673

theorem tailTrace_2165290 : CollatzResearch.WordTrace tailWord_2165290 prefixEnd_2165290 370611508791312842205673 := by
  unfold tailWord_2165290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19743653581382901733915331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52649742883687737957107549 19743653581382901733915331)
  ·
    refine ⟨29615480372074352600872997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19743653581382901733915331 29615480372074352600872997)
    ·
      refine ⟨5552902569763941112663687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29615480372074352600872997 5552902569763941112663687)
      ·
        refine ⟨8329353854645911668995531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552902569763941112663687 8329353854645911668995531)
        ·
          refine ⟨12494030781968867503493297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8329353854645911668995531 12494030781968867503493297)
          ·
            refine ⟨9370523086476650627619973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12494030781968867503493297 9370523086476650627619973)
            ·
              refine ⟨1756973078714371992678745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9370523086476650627619973 1756973078714371992678745)
              ·
                refine ⟨1317729809035778994509059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756973078714371992678745 1317729809035778994509059)
                ·
                  refine ⟨1976594713553668491763589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317729809035778994509059 1976594713553668491763589)
                  ·
                    refine ⟨370611508791312842205673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976594713553668491763589 370611508791312842205673)
                    ·
                      rfl

theorem cell23_2165290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2165290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165290 prefixEnd_2165290 := by exact prefixLift 2165290
  have htrace : WordTrace (prefixWord ++ tailWord_2165290) baseStart_2165290 baseEnd_2165290 := by
    simpa [prefixWord, tailWord_2165290, baseEnd_2165290] using wordTrace_append hprefix tailTrace_2165290
  have hstable : (prefixWord ++ tailWord_2165290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165290).length < 2 ^ (prefixWord ++ tailWord_2165290).sum := by decide
  have hdescent : baseEnd_2165290 < baseStart_2165290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165292 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_2165292 : Nat := 118140960795 + 2165292 * 2 ^ 59
def prefixEnd_2165292 : Nat := 4983230072969 + 3 ^ 40 * 2165292 * 2
def baseEnd_2165292 : Nat := 1111835553335247518792009

theorem tailTrace_2165292 : CollatzResearch.WordTrace tailWord_2165292 prefixEnd_2165292 1111835553335247518792009 := by
  unfold tailWord_2165292
  simp only [CollatzResearch.WordTrace]
  refine ⟨39487343635762180638617065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52649791514349574184822753 39487343635762180638617065)
  ·
    refine ⟨29615507726821635478962799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39487343635762180638617065 29615507726821635478962799)
    ·
      refine ⟨44423261590232453218444199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29615507726821635478962799 44423261590232453218444199)
      ·
        refine ⟨66634892385348679827666299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44423261590232453218444199 66634892385348679827666299)
        ·
          refine ⟨99952338578023019741499449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66634892385348679827666299 99952338578023019741499449)
          ·
            refine ⟨74964253933517264806124587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99952338578023019741499449 74964253933517264806124587)
            ·
              refine ⟨112446380900275897209186881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74964253933517264806124587 112446380900275897209186881)
              ·
                refine ⟨84334785675206922906890161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112446380900275897209186881 84334785675206922906890161)
                ·
                  refine ⟨63251089256405192180167621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84334785675206922906890161 63251089256405192180167621)
                  ·
                    refine ⟨11859579235575973533781429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63251089256405192180167621 11859579235575973533781429)
                    ·
                      refine ⟨1111835553335247518792009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11859579235575973533781429 1111835553335247518792009)
                      ·
                        rfl

theorem cell23_2165292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_2165292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165292 prefixEnd_2165292 := by exact prefixLift 2165292
  have htrace : WordTrace (prefixWord ++ tailWord_2165292) baseStart_2165292 baseEnd_2165292 := by
    simpa [prefixWord, tailWord_2165292, baseEnd_2165292] using wordTrace_append hprefix tailTrace_2165292
  have hstable : (prefixWord ++ tailWord_2165292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165292).length < 2 ^ (prefixWord ++ tailWord_2165292).sum := by decide
  have hdescent : baseEnd_2165292 < baseStart_2165292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165313 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2165313 : Nat := 118140960795 + 2165313 * 2 ^ 59
def prefixEnd_2165313 : Nat := 4983230072969 + 3 ^ 40 * 2165313 * 2
def baseEnd_2165313 : Nat := 1111846336428991936629413

theorem tailTrace_2165313 : CollatzResearch.WordTrace tailWord_2165313 prefixEnd_2165313 1111846336428991936629413 := by
  unfold tailWord_2165313
  simp only [CollatzResearch.WordTrace]
  refine ⟨78975453204448281863748593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52650302136298854575832395 78975453204448281863748593)
  ·
    refine ⟨59231589903336211397811445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78975453204448281863748593 59231589903336211397811445)
    ·
      refine ⟨5552961553437769818544823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59231589903336211397811445 5552961553437769818544823)
      ·
        refine ⟨8329442330156654727817235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552961553437769818544823 8329442330156654727817235)
        ·
          refine ⟨12494163495234982091725853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8329442330156654727817235 12494163495234982091725853)
          ·
            refine ⟨4685311310713118284397195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12494163495234982091725853 4685311310713118284397195)
            ·
              refine ⟨7027966966069677426595793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685311310713118284397195 7027966966069677426595793)
              ·
                refine ⟨5270975224552258069946845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7027966966069677426595793 5270975224552258069946845)
                ·
                  refine ⟨1976615709207096776230067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5270975224552258069946845 1976615709207096776230067)
                  ·
                    refine ⟨2964923563810645164345101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976615709207096776230067 2964923563810645164345101)
                    ·
                      refine ⟨1111846336428991936629413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2964923563810645164345101 1111846336428991936629413)
                      ·
                        rfl

theorem cell23_2165313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2165313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165313 prefixEnd_2165313 := by exact prefixLift 2165313
  have htrace : WordTrace (prefixWord ++ tailWord_2165313) baseStart_2165313 baseEnd_2165313 := by
    simpa [prefixWord, tailWord_2165313, baseEnd_2165313] using wordTrace_append hprefix tailTrace_2165313
  have hstable : (prefixWord ++ tailWord_2165313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165313).length < 2 ^ (prefixWord ++ tailWord_2165313).sum := by decide
  have hdescent : baseEnd_2165313 < baseStart_2165313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165329 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_2165329 : Nat := 118140960795 + 2165329 * 2 ^ 59
def prefixEnd_2165329 : Nat := 4983230072969 + 3 ^ 40 * 2165329 * 2
def baseEnd_2165329 : Nat := 370618184039821291343113

theorem tailTrace_2165329 : CollatzResearch.WordTrace tailWord_2165329 prefixEnd_2165329 370618184039821291343113 := by
  unfold tailWord_2165329
  simp only [CollatzResearch.WordTrace]
  refine ⟨78976036772390316596331041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52650691181593544397554027 78976036772390316596331041)
  ·
    refine ⟨59232027579292737447248281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78976036772390316596331041 59232027579292737447248281)
    ·
      refine ⟨44424020684469553085436211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59232027579292737447248281 44424020684469553085436211)
      ·
        refine ⟨66636031026704329628154317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44424020684469553085436211 66636031026704329628154317)
        ·
          refine ⟨24988511635014123610557869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66636031026704329628154317 24988511635014123610557869)
          ·
            refine ⟨9370691863130296353959201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24988511635014123610557869 9370691863130296353959201)
            ·
              refine ⟨7028018897347722265469401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9370691863130296353959201 7028018897347722265469401)
              ·
                refine ⟨5271014173010791699102051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7028018897347722265469401 5271014173010791699102051)
                ·
                  refine ⟨7906521259516187548653077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271014173010791699102051 7906521259516187548653077)
                  ·
                    refine ⟨370618184039821291343113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7906521259516187548653077 370618184039821291343113)
                    ·
                      rfl

theorem cell23_2165329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_2165329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165329 prefixEnd_2165329 := by exact prefixLift 2165329
  have htrace : WordTrace (prefixWord ++ tailWord_2165329) baseStart_2165329 baseEnd_2165329 := by
    simpa [prefixWord, tailWord_2165329, baseEnd_2165329] using wordTrace_append hprefix tailTrace_2165329
  have hstable : (prefixWord ++ tailWord_2165329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165329).length < 2 ^ (prefixWord ++ tailWord_2165329).sum := by decide
  have hdescent : baseEnd_2165329 < baseStart_2165329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165330 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_2165330 : Nat := 118140960795 + 2165330 * 2 ^ 59
def prefixEnd_2165330 : Nat := 4983230072969 + 3 ^ 40 * 2165330 * 2
def baseEnd_2165330 : Nat := 1111855065600118370116835

theorem tailTrace_2165330 : CollatzResearch.WordTrace tailWord_2165330 prefixEnd_2165330 1111855065600118370116835 := by
  unfold tailWord_2165330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19744018311346673441779361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52650715496924462511411629 19744018311346673441779361)
  ·
    refine ⟨14808013733510005081334521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19744018311346673441779361 14808013733510005081334521)
    ·
      refine ⟨11106010300132503811000891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14808013733510005081334521 11106010300132503811000891)
      ·
        refine ⟨16659015450198755716501337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11106010300132503811000891 16659015450198755716501337)
        ·
          refine ⟨12494261587649066787376003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16659015450198755716501337 12494261587649066787376003)
          ·
            refine ⟨18741392381473600181064005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494261587649066787376003 18741392381473600181064005)
            ·
              refine ⟨3514011071526300033949501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18741392381473600181064005 3514011071526300033949501)
              ·
                refine ⟨1317754151822362512731063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3514011071526300033949501 1317754151822362512731063)
                ·
                  refine ⟨1976631227733543769096595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317754151822362512731063 1976631227733543769096595)
                  ·
                    refine ⟨2964946841600315653644893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976631227733543769096595 2964946841600315653644893)
                    ·
                      refine ⟨1111855065600118370116835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2964946841600315653644893 1111855065600118370116835)
                      ·
                        rfl

theorem cell23_2165330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_2165330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165330 prefixEnd_2165330 := by exact prefixLift 2165330
  have htrace : WordTrace (prefixWord ++ tailWord_2165330) baseStart_2165330 baseEnd_2165330 := by
    simpa [prefixWord, tailWord_2165330, baseEnd_2165330] using wordTrace_append hprefix tailTrace_2165330
  have hstable : (prefixWord ++ tailWord_2165330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165330).length < 2 ^ (prefixWord ++ tailWord_2165330).sum := by decide
  have hdescent : baseEnd_2165330 < baseStart_2165330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165376 : List Nat := [2, 1, 1, 2, 1, 7, 2, 7]
def baseStart_2165376 : Nat := 118140960795 + 2165376 * 2 ^ 59
def prefixEnd_2165376 : Nat := 4983230072969 + 3 ^ 40 * 2165376 * 2
def baseEnd_2165376 : Nat := 41180692063341673708949

theorem tailTrace_2165376 : CollatzResearch.WordTrace tailWord_2165376 prefixEnd_2165376 41180692063341673708949 := by
  unfold tailWord_2165376
  simp only [CollatzResearch.WordTrace]
  refine ⟨39488875501610021811645991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52651834002146695748861321 39488875501610021811645991)
  ·
    refine ⟨59233313252415032717468987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39488875501610021811645991 59233313252415032717468987)
    ·
      refine ⟨88849969878622549076203481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59233313252415032717468987 88849969878622549076203481)
      ·
        refine ⟨66637477408966911807152611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88849969878622549076203481 66637477408966911807152611)
        ·
          refine ⟨99956216113450367710728917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66637477408966911807152611 99956216113450367710728917)
          ·
            refine ⟨2342723815158992993220209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 99956216113450367710728917 2342723815158992993220209)
            ·
              refine ⟨1757042861369244744915157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342723815158992993220209 1757042861369244744915157)
              ·
                refine ⟨41180692063341673708949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1757042861369244744915157 41180692063341673708949)
                ·
                  rfl

theorem cell23_2165376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 7].length) (baseStart_2165376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165376 prefixEnd_2165376 := by exact prefixLift 2165376
  have htrace : WordTrace (prefixWord ++ tailWord_2165376) baseStart_2165376 baseEnd_2165376 := by
    simpa [prefixWord, tailWord_2165376, baseEnd_2165376] using wordTrace_append hprefix tailTrace_2165376
  have hstable : (prefixWord ++ tailWord_2165376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165376).length < 2 ^ (prefixWord ++ tailWord_2165376).sum := by decide
  have hdescent : baseEnd_2165376 < baseStart_2165376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165399 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2165399 : Nat := 118140960795 + 2165399 * 2 ^ 59
def prefixEnd_2165399 : Nat := 4983230072969 + 3 ^ 40 * 2165399 * 2
def baseEnd_2165399 : Nat := 1111890495765278600154017

theorem tailTrace_2165399 : CollatzResearch.WordTrace tailWord_2165399 prefixEnd_2165399 1111890495765278600154017 := by
  unfold tailWord_2165399
  simp only [CollatzResearch.WordTrace]
  refine ⟨78978589882136718551379251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52652393254757812367586167 78978589882136718551379251)
  ·
    refine ⟨118467884823205077827068877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78978589882136718551379251 118467884823205077827068877)
    ·
      refine ⟨44425456808701904185150829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118467884823205077827068877 44425456808701904185150829)
      ·
        refine ⟨16659546303263214069431561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44425456808701904185150829 16659546303263214069431561)
        ·
          refine ⟨12494659727447410552073671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16659546303263214069431561 12494659727447410552073671)
          ·
            refine ⟨18741989591171115828110507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494659727447410552073671 18741989591171115828110507)
            ·
              refine ⟨28112984386756673742165761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18741989591171115828110507 28112984386756673742165761)
              ·
                refine ⟨21084738290067505306624321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28112984386756673742165761 21084738290067505306624321)
                ·
                  refine ⟨15813553717550628979968241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21084738290067505306624321 15813553717550628979968241)
                  ·
                    refine ⟨11860165288162971734976181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15813553717550628979968241 11860165288162971734976181)
                    ·
                      refine ⟨1111890495765278600154017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11860165288162971734976181 1111890495765278600154017)
                      ·
                        rfl

theorem cell23_2165399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2165399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165399 prefixEnd_2165399 := by exact prefixLift 2165399
  have htrace : WordTrace (prefixWord ++ tailWord_2165399) baseStart_2165399 baseEnd_2165399 := by
    simpa [prefixWord, tailWord_2165399, baseEnd_2165399] using wordTrace_append hprefix tailTrace_2165399
  have hstable : (prefixWord ++ tailWord_2165399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165399).length < 2 ^ (prefixWord ++ tailWord_2165399).sum := by decide
  have hdescent : baseEnd_2165399 < baseStart_2165399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165404 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2165404 : Nat := 118140960795 + 2165404 * 2 ^ 59
def prefixEnd_2165404 : Nat := 4983230072969 + 3 ^ 40 * 2165404 * 2
def baseEnd_2165404 : Nat := 1111893063168551080591495

theorem tailTrace_2165404 : CollatzResearch.WordTrace tailWord_2165404 prefixEnd_2165404 1111893063168551080591495 := by
  unfold tailWord_2165404
  simp only [CollatzResearch.WordTrace]
  refine ⟨39489386123559302202655633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52652514831412402936874177 39489386123559302202655633)
  ·
    refine ⟨29617039592669476651991725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39489386123559302202655633 29617039592669476651991725)
    ·
      refine ⟨11106389847251053744496897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29617039592669476651991725 11106389847251053744496897)
      ·
        refine ⟨8329792385438290308372673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11106389847251053744496897 8329792385438290308372673)
        ·
          refine ⟨6247344289078717731279505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8329792385438290308372673 6247344289078717731279505)
          ·
            refine ⟨4685508216809038298459629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6247344289078717731279505 4685508216809038298459629)
            ·
              refine ⟨1757065581303389361922361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4685508216809038298459629 1757065581303389361922361)
              ·
                refine ⟨1317799185977542021441771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757065581303389361922361 1317799185977542021441771)
                ·
                  refine ⟨1976698778966313032162657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317799185977542021441771 1976698778966313032162657)
                  ·
                    refine ⟨1482524084224734774121993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1976698778966313032162657 1482524084224734774121993)
                    ·
                      refine ⟨1111893063168551080591495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482524084224734774121993 1111893063168551080591495)
                      ·
                        rfl

theorem cell23_2165404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2165404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165404 prefixEnd_2165404 := by exact prefixLift 2165404
  have htrace : WordTrace (prefixWord ++ tailWord_2165404) baseStart_2165404 baseEnd_2165404 := by
    simpa [prefixWord, tailWord_2165404, baseEnd_2165404] using wordTrace_append hprefix tailTrace_2165404
  have hstable : (prefixWord ++ tailWord_2165404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165404).length < 2 ^ (prefixWord ++ tailWord_2165404).sum := by decide
  have hdescent : baseEnd_2165404 < baseStart_2165404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165406 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2165406 : Nat := 118140960795 + 2165406 * 2 ^ 59
def prefixEnd_2165406 : Nat := 4983230072969 + 3 ^ 40 * 2165406 * 2
def baseEnd_2165406 : Nat := 370631363376620024255495

theorem tailTrace_2165406 : CollatzResearch.WordTrace tailWord_2165406 prefixEnd_2165406 370631363376620024255495 := by
  unfold tailWord_2165406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9872355649138919843360509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52652563462074239164589381 9872355649138919843360509)
  ·
    refine ⟨3702133368427094941260191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9872355649138919843360509 3702133368427094941260191)
    ·
      refine ⟨5553200052640642411890287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3702133368427094941260191 5553200052640642411890287)
      ·
        refine ⟨8329800078960963617835431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5553200052640642411890287 8329800078960963617835431)
        ·
          refine ⟨12494700118441445426753147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8329800078960963617835431 12494700118441445426753147)
          ·
            refine ⟨18742050177662168140129721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12494700118441445426753147 18742050177662168140129721)
            ·
              refine ⟨14056537633246626105097291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18742050177662168140129721 14056537633246626105097291)
              ·
                refine ⟨21084806449869939157645937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14056537633246626105097291 21084806449869939157645937)
                ·
                  refine ⟨15813604837402454368234453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21084806449869939157645937 15813604837402454368234453)
                  ·
                    refine ⟨370631363376620024255495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15813604837402454368234453 370631363376620024255495)
                    ·
                      rfl

theorem cell23_2165406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2165406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165406 prefixEnd_2165406 := by exact prefixLift 2165406
  have htrace : WordTrace (prefixWord ++ tailWord_2165406) baseStart_2165406 baseEnd_2165406 := by
    simpa [prefixWord, tailWord_2165406, baseEnd_2165406] using wordTrace_append hprefix tailTrace_2165406
  have hstable : (prefixWord ++ tailWord_2165406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165406).length < 2 ^ (prefixWord ++ tailWord_2165406).sum := by decide
  have hdescent : baseEnd_2165406 < baseStart_2165406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165476 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_2165476 : Nat := 118140960795 + 2165476 * 2 ^ 59
def prefixEnd_2165476 : Nat := 4983230072969 + 3 ^ 40 * 2165476 * 2
def baseEnd_2165476 : Nat := 1111930033775674798891163

theorem tailTrace_2165476 : CollatzResearch.WordTrace tailWord_2165476 prefixEnd_2165476 1111930033775674798891163 := by
  unfold tailWord_2165476
  simp only [CollatzResearch.WordTrace]
  refine ⟨39490699151428880350966141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52654265535238507134621521 39490699151428880350966141)
  ·
    refine ⟨14809012181785830131612303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39490699151428880350966141 14809012181785830131612303)
    ·
      refine ⟨22213518272678745197418455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14809012181785830131612303 22213518272678745197418455)
      ·
        refine ⟨33320277409018117796127683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22213518272678745197418455 33320277409018117796127683)
        ·
          refine ⟨49980416113527176694191525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33320277409018117796127683 49980416113527176694191525)
          ·
            refine ⟨9371328021286345630160911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49980416113527176694191525 9371328021286345630160911)
            ·
              refine ⟨14056992031929518445241367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9371328021286345630160911 14056992031929518445241367)
              ·
                refine ⟨21085488047894277667862051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14056992031929518445241367 21085488047894277667862051)
                ·
                  refine ⟨31628232071841416501793077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21085488047894277667862051 31628232071841416501793077)
                  ·
                    refine ⟨2965146756735132797043101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31628232071841416501793077 2965146756735132797043101)
                    ·
                      refine ⟨1111930033775674798891163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965146756735132797043101 1111930033775674798891163)
                      ·
                        rfl

theorem cell23_2165476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_2165476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165476 prefixEnd_2165476 := by exact prefixLift 2165476
  have htrace : WordTrace (prefixWord ++ tailWord_2165476) baseStart_2165476 baseEnd_2165476 := by
    simpa [prefixWord, tailWord_2165476, baseEnd_2165476] using wordTrace_append hprefix tailTrace_2165476
  have hstable : (prefixWord ++ tailWord_2165476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165476).length < 2 ^ (prefixWord ++ tailWord_2165476).sum := by decide
  have hdescent : baseEnd_2165476 < baseStart_2165476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165509 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_2165509 : Nat := 118140960795 + 2165509 * 2 ^ 59
def prefixEnd_2165509 : Nat := 4983230072969 + 3 ^ 40 * 2165509 * 2
def baseEnd_2165509 : Nat := 370648992879091056592837

theorem tailTrace_2165509 : CollatzResearch.WordTrace tailWord_2165509 prefixEnd_2165509 370648992879091056592837 := by
  unfold tailWord_2165509
  simp only [CollatzResearch.WordTrace]
  refine ⟨78982601911738207337883581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52655067941158804891922387 78982601911738207337883581)
  ·
    refine ⟨29618475716901827751706343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78982601911738207337883581 29618475716901827751706343)
    ·
      refine ⟨44427713575352741627559515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29618475716901827751706343 44427713575352741627559515)
      ·
        refine ⟨66641570363029112441339273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44427713575352741627559515 66641570363029112441339273)
        ·
          refine ⟨49981177772271834331004455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66641570363029112441339273 49981177772271834331004455)
          ·
            refine ⟨74971766658407751496506683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49981177772271834331004455 74971766658407751496506683)
            ·
              refine ⟨112457649987611627244760025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74971766658407751496506683 112457649987611627244760025)
              ·
                refine ⟨84343237490708720433570019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112457649987611627244760025 84343237490708720433570019)
                ·
                  refine ⟨126514856236063080650355029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84343237490708720433570019 126514856236063080650355029)
                  ·
                    refine ⟨370648992879091056592837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 126514856236063080650355029 370648992879091056592837)
                    ·
                      rfl

theorem cell23_2165509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_2165509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165509 prefixEnd_2165509 := by exact prefixLift 2165509
  have htrace : WordTrace (prefixWord ++ tailWord_2165509) baseStart_2165509 baseEnd_2165509 := by
    simpa [prefixWord, tailWord_2165509, baseEnd_2165509] using wordTrace_append hprefix tailTrace_2165509
  have hstable : (prefixWord ++ tailWord_2165509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165509).length < 2 ^ (prefixWord ++ tailWord_2165509).sum := by decide
  have hdescent : baseEnd_2165509 < baseStart_2165509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165516 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2165516 : Nat := 118140960795 + 2165516 * 2 ^ 59
def prefixEnd_2165516 : Nat := 4983230072969 + 3 ^ 40 * 2165516 * 2
def baseEnd_2165516 : Nat := 1111950573001854642390979

theorem tailTrace_2165516 : CollatzResearch.WordTrace tailWord_2165516 prefixEnd_2165516 1111950573001854642390979 := by
  unfold tailWord_2165516
  simp only [CollatzResearch.WordTrace]
  refine ⟨39491428611356423766694201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52655238148475231688925601 39491428611356423766694201)
  ·
    refine ⟨29618571458517317825020651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39491428611356423766694201 29618571458517317825020651)
    ·
      refine ⟨44427857187775976737530977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29618571458517317825020651 44427857187775976737530977)
      ·
        refine ⟨33320892890831982553148233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44427857187775976737530977 33320892890831982553148233)
        ·
          refine ⟨24990669668123986914861175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33320892890831982553148233 24990669668123986914861175)
          ·
            refine ⟨37486004502185980372291763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24990669668123986914861175 37486004502185980372291763)
            ·
              refine ⟨56229006753278970558437645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37486004502185980372291763 56229006753278970558437645)
              ·
                refine ⟨21085877532479613959414117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56229006753278970558437645 21085877532479613959414117)
                ·
                  refine ⟨3953602037339927617390147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21085877532479613959414117 3953602037339927617390147)
                  ·
                    refine ⟨5930403056009891426085221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3953602037339927617390147 5930403056009891426085221)
                    ·
                      refine ⟨1111950573001854642390979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5930403056009891426085221 1111950573001854642390979)
                      ·
                        rfl

theorem cell23_2165516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2165516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165516 prefixEnd_2165516 := by exact prefixLift 2165516
  have htrace : WordTrace (prefixWord ++ tailWord_2165516) baseStart_2165516 baseEnd_2165516 := by
    simpa [prefixWord, tailWord_2165516, baseEnd_2165516] using wordTrace_append hprefix tailTrace_2165516
  have hstable : (prefixWord ++ tailWord_2165516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165516).length < 2 ^ (prefixWord ++ tailWord_2165516).sum := by decide
  have hdescent : baseEnd_2165516 < baseStart_2165516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165553 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_2165553 : Nat := 118140960795 + 2165553 * 2 ^ 59
def prefixEnd_2165553 : Nat := 4983230072969 + 3 ^ 40 * 2165553 * 2
def baseEnd_2165553 : Nat := 1111969571786070997628309

theorem tailTrace_2165553 : CollatzResearch.WordTrace tailWord_2165553 prefixEnd_2165553 1111969571786070997628309 := by
  unfold tailWord_2165553
  simp only [CollatzResearch.WordTrace]
  refine ⟨78984206723578802852485313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52656137815719201901656875 78984206723578802852485313)
  ·
    refine ⟨59238155042684102139363985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78984206723578802852485313 59238155042684102139363985)
    ·
      refine ⟨44428616282013076604522989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59238155042684102139363985 44428616282013076604522989)
      ·
        refine ⟨16660731105754903726696121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44428616282013076604522989 16660731105754903726696121)
        ·
          refine ⟨12495548329316177795022091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16660731105754903726696121 12495548329316177795022091)
          ·
            refine ⟨18743322493974266692533137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12495548329316177795022091 18743322493974266692533137)
            ·
              refine ⟨14057491870480700019399853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18743322493974266692533137 14057491870480700019399853)
              ·
                refine ⟨5271559451430262507274945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14057491870480700019399853 5271559451430262507274945)
                ·
                  refine ⟨3953669588572696880456209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5271559451430262507274945 3953669588572696880456209)
                  ·
                    refine ⟨2965252191429522660342157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953669588572696880456209 2965252191429522660342157)
                    ·
                      refine ⟨1111969571786070997628309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965252191429522660342157 1111969571786070997628309)
                      ·
                        rfl

theorem cell23_2165553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_2165553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165553 prefixEnd_2165553 := by exact prefixLift 2165553
  have htrace : WordTrace (prefixWord ++ tailWord_2165553) baseStart_2165553 baseEnd_2165553 := by
    simpa [prefixWord, tailWord_2165553, baseEnd_2165553] using wordTrace_append hprefix tailTrace_2165553
  have hstable : (prefixWord ++ tailWord_2165553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165553).length < 2 ^ (prefixWord ++ tailWord_2165553).sum := by decide
  have hdescent : baseEnd_2165553 < baseStart_2165553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165577 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 1, 4]
def baseStart_2165577 : Nat := 118140960795 + 2165577 * 2 ^ 59
def prefixEnd_2165577 : Nat := 4983230072969 + 3 ^ 40 * 2165577 * 2
def baseEnd_2165577 : Nat := 370660631773926301242733

theorem tailTrace_2165577 : CollatzResearch.WordTrace tailWord_2165577 prefixEnd_2165577 370660631773926301242733 := by
  unfold tailWord_2165577
  simp only [CollatzResearch.WordTrace]
  refine ⟨78985082075491854951358985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52656721383661236634239323 78985082075491854951358985)
  ·
    refine ⟨59238811556618891213519239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78985082075491854951358985 59238811556618891213519239)
    ·
      refine ⟨88858217334928336820278859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59238811556618891213519239 88858217334928336820278859)
      ·
        refine ⟨133287326002392505230418289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88858217334928336820278859 133287326002392505230418289)
        ·
          refine ⟨99965494501794378922813717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133287326002392505230418289 99965494501794378922813717)
          ·
            refine ⟨4685882554771611512006893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99965494501794378922813717 4685882554771611512006893)
            ·
              refine ⟨1757205958039354317002585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4685882554771611512006893 1757205958039354317002585)
              ·
                refine ⟨1317904468529515737751939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757205958039354317002585 1317904468529515737751939)
                ·
                  refine ⟨1976856702794273606627909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317904468529515737751939 1976856702794273606627909)
                  ·
                    refine ⟨370660631773926301242733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976856702794273606627909 370660631773926301242733)
                    ·
                      rfl

theorem cell23_2165577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 4].length) (baseStart_2165577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165577 prefixEnd_2165577 := by exact prefixLift 2165577
  have htrace : WordTrace (prefixWord ++ tailWord_2165577) baseStart_2165577 baseEnd_2165577 := by
    simpa [prefixWord, tailWord_2165577, baseEnd_2165577] using wordTrace_append hprefix tailTrace_2165577
  have hstable : (prefixWord ++ tailWord_2165577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165577).length < 2 ^ (prefixWord ++ tailWord_2165577).sum := by decide
  have hdescent : baseEnd_2165577 < baseStart_2165577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165603 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 3, 5]
def baseStart_2165603 : Nat := 118140960795 + 2165603 * 2 ^ 59
def prefixEnd_2165603 : Nat := 4983230072969 + 3 ^ 40 * 2165603 * 2
def baseEnd_2165603 : Nat := 370665081939598600667693

theorem tailTrace_2165603 : CollatzResearch.WordTrace tailWord_2165603 prefixEnd_2165603 370665081939598600667693 := by
  unfold tailWord_2165603
  simp only [CollatzResearch.WordTrace]
  refine ⟨78986030373397661391805463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52657353582265107594536975 78986030373397661391805463)
  ·
    refine ⟨118479045560096492087708195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78986030373397661391805463 118479045560096492087708195)
    ·
      refine ⟨177718568340144738131562293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118479045560096492087708195 177718568340144738131562293)
      ·
        refine ⟨16661115781888569199833965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177718568340144738131562293 16661115781888569199833965)
        ·
          refine ⟨6247918418208213449937737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16661115781888569199833965 6247918418208213449937737)
          ·
            refine ⟨4685938813656160087453303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6247918418208213449937737 4685938813656160087453303)
            ·
              refine ⟨7028908220484240131179955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685938813656160087453303 7028908220484240131179955)
              ·
                refine ⟨10543362330726360196769933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7028908220484240131179955 10543362330726360196769933)
                ·
                  refine ⟨3953760874022385073788725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10543362330726360196769933 3953760874022385073788725)
                  ·
                    refine ⟨370665081939598600667693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3953760874022385073788725 370665081939598600667693)
                    ·
                      rfl

theorem cell23_2165603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 5].length) (baseStart_2165603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165603 prefixEnd_2165603 := by exact prefixLift 2165603
  have htrace : WordTrace (prefixWord ++ tailWord_2165603) baseStart_2165603 baseEnd_2165603 := by
    simpa [prefixWord, tailWord_2165603, baseEnd_2165603] using wordTrace_append hprefix tailTrace_2165603
  have hstable : (prefixWord ++ tailWord_2165603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165603).length < 2 ^ (prefixWord ++ tailWord_2165603).sum := by decide
  have hdescent : baseEnd_2165603 < baseStart_2165603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165616 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_2165616 : Nat := 118140960795 + 2165616 * 2 ^ 59
def prefixEnd_2165616 : Nat := 4983230072969 + 3 ^ 40 * 2165616 * 2
def baseEnd_2165616 : Nat := 370667307022434750380173

theorem tailTrace_2165616 : CollatzResearch.WordTrace tailWord_2165616 prefixEnd_2165616 370667307022434750380173 := by
  unfold tailWord_2165616
  simp only [CollatzResearch.WordTrace]
  refine ⟨39493252261175282306014351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52657669681567043074685801 39493252261175282306014351)
  ·
    refine ⟨59239878391762923459021527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39493252261175282306014351 59239878391762923459021527)
    ·
      refine ⟨88859817587644385188532291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59239878391762923459021527 88859817587644385188532291)
      ·
        refine ⟨133289726381466577782798437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88859817587644385188532291 133289726381466577782798437)
        ·
          refine ⟨24991823696524983334274707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133289726381466577782798437 24991823696524983334274707)
          ·
            refine ⟨37487735544787475001412061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24991823696524983334274707 37487735544787475001412061)
            ·
              refine ⟨14057900829295303125529523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37487735544787475001412061 14057900829295303125529523)
              ·
                refine ⟨21086851243942954688294285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14057900829295303125529523 21086851243942954688294285)
                ·
                  refine ⟨7907569216478608008110357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21086851243942954688294285 7907569216478608008110357)
                  ·
                    refine ⟨370667307022434750380173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7907569216478608008110357 370667307022434750380173)
                    ·
                      rfl

theorem cell23_2165616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_2165616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165616 prefixEnd_2165616 := by exact prefixLift 2165616
  have htrace : WordTrace (prefixWord ++ tailWord_2165616) baseStart_2165616 baseEnd_2165616 := by
    simpa [prefixWord, tailWord_2165616, baseEnd_2165616] using wordTrace_append hprefix tailTrace_2165616
  have hstable : (prefixWord ++ tailWord_2165616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165616).length < 2 ^ (prefixWord ++ tailWord_2165616).sum := by decide
  have hdescent : baseEnd_2165616 < baseStart_2165616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165623 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_2165623 : Nat := 118140960795 + 2165623 * 2 ^ 59
def prefixEnd_2165623 : Nat := 4983230072969 + 3 ^ 40 * 2165623 * 2
def baseEnd_2165623 : Nat := 1112005515431885723752987

theorem tailTrace_2165623 : CollatzResearch.WordTrace tailWord_2165623 prefixEnd_2165623 1112005515431885723752987 := by
  unfold tailWord_2165623
  simp only [CollatzResearch.WordTrace]
  refine ⟨78986759833325204807533523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52657839888883469871689015 78986759833325204807533523)
  ·
    refine ⟨118480139749987807211300285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78986759833325204807533523 118480139749987807211300285)
    ·
      refine ⟨44430052406245427704237607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118480139749987807211300285 44430052406245427704237607)
      ·
        refine ⟨66645078609368141556356411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44430052406245427704237607 66645078609368141556356411)
        ·
          refine ⟨99967617914052212334534617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66645078609368141556356411 99967617914052212334534617)
          ·
            refine ⟨74975713435539159250900963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99967617914052212334534617 74975713435539159250900963)
            ·
              refine ⟨112463570153308738876351445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74975713435539159250900963 112463570153308738876351445)
              ·
                refine ⟨2635864925468173567414487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112463570153308738876351445 2635864925468173567414487)
                ·
                  refine ⟨3953797388202260351121731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635864925468173567414487 3953797388202260351121731)
                  ·
                    refine ⟨5930696082303390526682597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3953797388202260351121731 5930696082303390526682597)
                    ·
                      refine ⟨1112005515431885723752987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5930696082303390526682597 1112005515431885723752987)
                      ·
                        rfl

theorem cell23_2165623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_2165623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165623 prefixEnd_2165623 := by exact prefixLift 2165623
  have htrace : WordTrace (prefixWord ++ tailWord_2165623) baseStart_2165623 baseEnd_2165623 := by
    simpa [prefixWord, tailWord_2165623, baseEnd_2165623] using wordTrace_append hprefix tailTrace_2165623
  have hstable : (prefixWord ++ tailWord_2165623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165623).length < 2 ^ (prefixWord ++ tailWord_2165623).sum := by decide
  have hdescent : baseEnd_2165623 < baseStart_2165623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165643 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 3]
def baseStart_2165643 : Nat := 118140960795 + 2165643 * 2 ^ 59
def prefixEnd_2165643 : Nat := 4983230072969 + 3 ^ 40 * 2165643 * 2
def baseEnd_2165643 : Nat := 1112015785044975645502895

theorem tailTrace_2165643 : CollatzResearch.WordTrace tailWord_2165643 prefixEnd_2165643 1112015785044975645502895 := by
  unfold tailWord_2165643
  simp only [CollatzResearch.WordTrace]
  refine ⟨78987489293252748223261583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52658326195501832148841055 78987489293252748223261583)
  ·
    refine ⟨118481233939879122334892375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78987489293252748223261583 118481233939879122334892375)
    ·
      refine ⟨177721850909818683502338563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118481233939879122334892375 177721850909818683502338563)
      ·
        refine ⟨266582776364728025253507845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177721850909818683502338563 266582776364728025253507845)
        ·
          refine ⟨49984270568386504735032721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266582776364728025253507845 49984270568386504735032721)
          ·
            refine ⟨37488202926289878551274541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49984270568386504735032721 37488202926289878551274541)
            ·
              refine ⟨14058076097358704456727953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37488202926289878551274541 14058076097358704456727953)
              ·
                refine ⟨10543557073019028342545965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14058076097358704456727953 10543557073019028342545965)
                ·
                  refine ⟨3953833902382135628454737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10543557073019028342545965 3953833902382135628454737)
                  ·
                    refine ⟨2965375426786601721341053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3953833902382135628454737 2965375426786601721341053)
                    ·
                      refine ⟨1112015785044975645502895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965375426786601721341053 1112015785044975645502895)
                      ·
                        rfl

theorem cell23_2165643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 3].length) (baseStart_2165643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165643 prefixEnd_2165643 := by exact prefixLift 2165643
  have htrace : WordTrace (prefixWord ++ tailWord_2165643) baseStart_2165643 baseEnd_2165643 := by
    simpa [prefixWord, tailWord_2165643, baseEnd_2165643] using wordTrace_append hprefix tailTrace_2165643
  have hstable : (prefixWord ++ tailWord_2165643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165643).length < 2 ^ (prefixWord ++ tailWord_2165643).sum := by decide
  have hdescent : baseEnd_2165643 < baseStart_2165643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165653 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_2165653 : Nat := 118140960795 + 2165653 * 2 ^ 59
def prefixEnd_2165653 : Nat := 4983230072969 + 3 ^ 40 * 2165653 * 2
def baseEnd_2165653 : Nat := 1112020919851520606377849

theorem tailTrace_2165653 : CollatzResearch.WordTrace tailWord_2165653 prefixEnd_2165653 1112020919851520606377849 := by
  unfold tailWord_2165653
  simp only [CollatzResearch.WordTrace]
  refine ⟨78987854023216519931125613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52658569348811013287417075 78987854023216519931125613)
  ·
    refine ⟨29620445258706194974172105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78987854023216519931125613 29620445258706194974172105)
    ·
      refine ⟨22215333944029646230629079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29620445258706194974172105 22215333944029646230629079)
      ·
        refine ⟨33323000916044469345943619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22215333944029646230629079 33323000916044469345943619)
        ·
          refine ⟨49984501374066704018915429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33323000916044469345943619 49984501374066704018915429)
          ·
            refine ⟨9372094007637507003546643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49984501374066704018915429 9372094007637507003546643)
            ·
              refine ⟨14058141011456260505319965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9372094007637507003546643 14058141011456260505319965)
              ·
                refine ⟨5271802879296097689494987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14058141011456260505319965 5271802879296097689494987)
                ·
                  refine ⟨7907704318944146534242481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271802879296097689494987 7907704318944146534242481)
                  ·
                    refine ⟨5930778239208109900681861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7907704318944146534242481 5930778239208109900681861)
                    ·
                      refine ⟨1112020919851520606377849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5930778239208109900681861 1112020919851520606377849)
                      ·
                        rfl

theorem cell23_2165653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_2165653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165653 prefixEnd_2165653 := by exact prefixLift 2165653
  have htrace : WordTrace (prefixWord ++ tailWord_2165653) baseStart_2165653 baseEnd_2165653 := by
    simpa [prefixWord, tailWord_2165653, baseEnd_2165653] using wordTrace_append hprefix tailTrace_2165653
  have hstable : (prefixWord ++ tailWord_2165653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165653).length < 2 ^ (prefixWord ++ tailWord_2165653).sum := by decide
  have hdescent : baseEnd_2165653 < baseStart_2165653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165673 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_2165673 : Nat := 118140960795 + 2165673 * 2 ^ 59
def prefixEnd_2165673 : Nat := 4983230072969 + 3 ^ 40 * 2165673 * 2
def baseEnd_2165673 : Nat := 1112031189464610528127757

theorem tailTrace_2165673 : CollatzResearch.WordTrace tailWord_2165673 prefixEnd_2165673 1112031189464610528127757 := by
  unfold tailWord_2165673
  simp only [CollatzResearch.WordTrace]
  refine ⟨78988583483144063346853673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52659055655429375564569115 78988583483144063346853673)
  ·
    refine ⟨59241437612358047510140255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78988583483144063346853673 59241437612358047510140255)
    ·
      refine ⟨88862156418537071265210383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59241437612358047510140255 88862156418537071265210383)
      ·
        refine ⟨133293234627805606897815575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88862156418537071265210383 133293234627805606897815575)
        ·
          refine ⟨199939851941708410346723363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133293234627805606897815575 199939851941708410346723363)
          ·
            refine ⟨299909777912562615520085045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199939851941708410346723363 299909777912562615520085045)
            ·
              refine ⟨28116541679302745205007973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 299909777912562615520085045 28116541679302745205007973)
              ·
                refine ⟨5271851564869264725938995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28116541679302745205007973 5271851564869264725938995)
                ·
                  refine ⟨7907777347303897088908493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5271851564869264725938995 7907777347303897088908493)
                  ·
                    refine ⟨2965416505238961408340685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7907777347303897088908493 2965416505238961408340685)
                    ·
                      refine ⟨1112031189464610528127757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965416505238961408340685 1112031189464610528127757)
                      ·
                        rfl

theorem cell23_2165673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_2165673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165673 prefixEnd_2165673 := by exact prefixLift 2165673
  have htrace : WordTrace (prefixWord ++ tailWord_2165673) baseStart_2165673 baseEnd_2165673 := by
    simpa [prefixWord, tailWord_2165673, baseEnd_2165673] using wordTrace_append hprefix tailTrace_2165673
  have hstable : (prefixWord ++ tailWord_2165673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165673).length < 2 ^ (prefixWord ++ tailWord_2165673).sum := by decide
  have hdescent : baseEnd_2165673 < baseStart_2165673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165676 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_2165676 : Nat := 118140960795 + 2165676 * 2 ^ 59
def prefixEnd_2165676 : Nat := 4983230072969 + 3 ^ 40 * 2165676 * 2
def baseEnd_2165676 : Nat := 370677576635524672130081

theorem tailTrace_2165676 : CollatzResearch.WordTrace tailWord_2165676 prefixEnd_2165676 370677576635524672130081 := by
  unfold tailWord_2165676
  simp only [CollatzResearch.WordTrace]
  refine ⟨39494346451066597429606441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52659128601422129906141921 39494346451066597429606441)
  ·
    refine ⟨29620759838299948072204831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39494346451066597429606441 29620759838299948072204831)
    ·
      refine ⟨44431139757449922108307247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29620759838299948072204831 44431139757449922108307247)
      ·
        refine ⟨66646709636174883162460871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44431139757449922108307247 66646709636174883162460871)
        ·
          refine ⟨99970064454262324743691307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66646709636174883162460871 99970064454262324743691307)
          ·
            refine ⟨149955096681393487115536961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99970064454262324743691307 149955096681393487115536961)
            ·
              refine ⟨112466322511045115336652721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149955096681393487115536961 112466322511045115336652721)
              ·
                refine ⟨84349741883283836502489541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112466322511045115336652721 84349741883283836502489541)
                ·
                  refine ⟨15815576603115719344216789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84349741883283836502489541 15815576603115719344216789)
                  ·
                    refine ⟨370677576635524672130081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15815576603115719344216789 370677576635524672130081)
                    ·
                      rfl

theorem cell23_2165676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_2165676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165676 prefixEnd_2165676 := by exact prefixLift 2165676
  have htrace : WordTrace (prefixWord ++ tailWord_2165676) baseStart_2165676 baseEnd_2165676 := by
    simpa [prefixWord, tailWord_2165676, baseEnd_2165676] using wordTrace_append hprefix tailTrace_2165676
  have hstable : (prefixWord ++ tailWord_2165676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165676).length < 2 ^ (prefixWord ++ tailWord_2165676).sum := by decide
  have hdescent : baseEnd_2165676 < baseStart_2165676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165684 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2165684 : Nat := 118140960795 + 2165684 * 2 ^ 59
def prefixEnd_2165684 : Nat := 4983230072969 + 3 ^ 40 * 2165684 * 2
def baseEnd_2165684 : Nat := 370678945917269995030069

theorem tailTrace_2165684 : CollatzResearch.WordTrace tailWord_2165684 prefixEnd_2165684 370678945917269995030069 := by
  unfold tailWord_2165684
  simp only [CollatzResearch.WordTrace]
  refine ⟨39494492343052106112752053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52659323124069474817002737 39494492343052106112752053)
  ·
    refine ⟨3702608657161134948070505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39494492343052106112752053 3702608657161134948070505)
    ·
      refine ⟨2776956492870851211052879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3702608657161134948070505 2776956492870851211052879)
      ·
        refine ⟨4165434739306276816579319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776956492870851211052879 4165434739306276816579319)
        ·
          refine ⟨6248152108959415224868979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165434739306276816579319 6248152108959415224868979)
          ·
            refine ⟨9372228163439122837303469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6248152108959415224868979 9372228163439122837303469)
            ·
              refine ⟨3514585561289671063988801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9372228163439122837303469 3514585561289671063988801)
              ·
                refine ⟨2635939170967253297991601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514585561289671063988801 2635939170967253297991601)
                ·
                  refine ⟨1976954378225439973493701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635939170967253297991601 1976954378225439973493701)
                  ·
                    refine ⟨370678945917269995030069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1976954378225439973493701 370678945917269995030069)
                    ·
                      rfl

theorem cell23_2165684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2165684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165684 prefixEnd_2165684 := by exact prefixLift 2165684
  have htrace : WordTrace (prefixWord ++ tailWord_2165684) baseStart_2165684 baseEnd_2165684 := by
    simpa [prefixWord, tailWord_2165684, baseEnd_2165684] using wordTrace_append hprefix tailTrace_2165684
  have hstable : (prefixWord ++ tailWord_2165684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165684).length < 2 ^ (prefixWord ++ tailWord_2165684).sum := by decide
  have hdescent : baseEnd_2165684 < baseStart_2165684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165690 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_2165690 : Nat := 118140960795 + 2165690 * 2 ^ 59
def prefixEnd_2165690 : Nat := 4983230072969 + 3 ^ 40 * 2165690 * 2
def baseEnd_2165690 : Nat := 1112039918635736961615179

theorem tailTrace_2165690 : CollatzResearch.WordTrace tailWord_2165690 prefixEnd_2165690 1112039918635736961615179 := by
  unfold tailWord_2165690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19747300881020618812555631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52659469016054983500148349 19747300881020618812555631)
  ·
    refine ⟨29620951321530928218833447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19747300881020618812555631 29620951321530928218833447)
    ·
      refine ⟨44431426982296392328250171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29620951321530928218833447 44431426982296392328250171)
      ·
        refine ⟨66647140473444588492375257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44431426982296392328250171 66647140473444588492375257)
        ·
          refine ⟨49985355355083441369281443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66647140473444588492375257 49985355355083441369281443)
          ·
            refine ⟨74978033032625162053922165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49985355355083441369281443 74978033032625162053922165)
            ·
              refine ⟨7029190596808608942555203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74978033032625162053922165 7029190596808608942555203)
              ·
                refine ⟨10543785895212913413832805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029190596808608942555203 10543785895212913413832805)
                ·
                  refine ⟨1976959855352421265093651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10543785895212913413832805 1976959855352421265093651)
                  ·
                    refine ⟨2965439783028631897640477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1976959855352421265093651 2965439783028631897640477)
                    ·
                      refine ⟨1112039918635736961615179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965439783028631897640477 1112039918635736961615179)
                      ·
                        rfl

theorem cell23_2165690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_2165690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165690 prefixEnd_2165690 := by exact prefixLift 2165690
  have htrace : WordTrace (prefixWord ++ tailWord_2165690) baseStart_2165690 baseEnd_2165690 := by
    simpa [prefixWord, tailWord_2165690, baseEnd_2165690] using wordTrace_append hprefix tailTrace_2165690
  have hstable : (prefixWord ++ tailWord_2165690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165690).length < 2 ^ (prefixWord ++ tailWord_2165690).sum := by decide
  have hdescent : baseEnd_2165690 < baseStart_2165690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165758 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2165758 : Nat := 118140960795 + 2165758 * 2 ^ 59
def prefixEnd_2165758 : Nat := 4983230072969 + 3 ^ 40 * 2165758 * 2
def baseEnd_2165758 : Nat := 1112074835320242695564867

theorem tailTrace_2165758 : CollatzResearch.WordTrace tailWord_2165758 prefixEnd_2165758 1112074835320242695564867 := by
  unfold tailWord_2165758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9873960460979515357962241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52661122458557415242465285 9873960460979515357962241)
  ·
    refine ⟨7405470345734636518471681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9873960460979515357962241 7405470345734636518471681)
    ·
      refine ⟨5554102759300977388853761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7405470345734636518471681 5554102759300977388853761)
      ·
        refine ⟨4165577069475733041640321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5554102759300977388853761 4165577069475733041640321)
        ·
          refine ⟨3124182802106799781230241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4165577069475733041640321 3124182802106799781230241)
          ·
            refine ⟨2343137101580099835922681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124182802106799781230241 2343137101580099835922681)
            ·
              refine ⟨1757352826185074876942011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343137101580099835922681 1757352826185074876942011)
              ·
                refine ⟨2636029239277612315413017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757352826185074876942011 2636029239277612315413017)
                ·
                  refine ⟨1977021929458209236559763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636029239277612315413017 1977021929458209236559763)
                  ·
                    refine ⟨2965532894187313854839645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1977021929458209236559763 2965532894187313854839645)
                    ·
                      refine ⟨1112074835320242695564867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965532894187313854839645 1112074835320242695564867)
                      ·
                        rfl

theorem cell23_2165758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2165758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165758 prefixEnd_2165758 := by exact prefixLift 2165758
  have htrace : WordTrace (prefixWord ++ tailWord_2165758) baseStart_2165758 baseEnd_2165758 := by
    simpa [prefixWord, tailWord_2165758, baseEnd_2165758] using wordTrace_append hprefix tailTrace_2165758
  have hstable : (prefixWord ++ tailWord_2165758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165758).length < 2 ^ (prefixWord ++ tailWord_2165758).sum := by decide
  have hdescent : baseEnd_2165758 < baseStart_2165758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165813 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2165813 : Nat := 118140960795 + 2165813 * 2 ^ 59
def prefixEnd_2165813 : Nat := 4983230072969 + 3 ^ 40 * 2165813 * 2
def baseEnd_2165813 : Nat := 370701025585413326792371

theorem tailTrace_2165813 : CollatzResearch.WordTrace tailWord_2165813 prefixEnd_2165813 370701025585413326792371 := by
  unfold tailWord_2165813
  simp only [CollatzResearch.WordTrace]
  refine ⟨78993689702636867256950093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52662459801757911504633395 78993689702636867256950093)
  ·
    refine ⟨29622633638488825221356285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78993689702636867256950093 29622633638488825221356285)
    ·
      refine ⟨11108487614433309458008607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29622633638488825221356285 11108487614433309458008607)
      ·
        refine ⟨16662731421649964187012911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11108487614433309458008607 16662731421649964187012911)
        ·
          refine ⟨24994097132474946280519367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16662731421649964187012911 24994097132474946280519367)
          ·
            refine ⟨37491145698712419420779051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24994097132474946280519367 37491145698712419420779051)
            ·
              refine ⟨56236718548068629131168577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37491145698712419420779051 56236718548068629131168577)
              ·
                refine ⟨42177538911051471848376433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56236718548068629131168577 42177538911051471848376433)
                ·
                  refine ⟨31633154183288603886282325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42177538911051471848376433 31633154183288603886282325)
                  ·
                    refine ⟨370701025585413326792371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31633154183288603886282325 370701025585413326792371)
                    ·
                      rfl

theorem cell23_2165813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2165813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165813 prefixEnd_2165813 := by exact prefixLift 2165813
  have htrace : WordTrace (prefixWord ++ tailWord_2165813) baseStart_2165813 baseEnd_2165813 := by
    simpa [prefixWord, tailWord_2165813, baseEnd_2165813] using wordTrace_append hprefix tailTrace_2165813
  have hstable : (prefixWord ++ tailWord_2165813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165813).length < 2 ^ (prefixWord ++ tailWord_2165813).sum := by decide
  have hdescent : baseEnd_2165813 < baseStart_2165813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165833 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_2165833 : Nat := 118140960795 + 2165833 * 2 ^ 59
def prefixEnd_2165833 : Nat := 4983230072969 + 3 ^ 40 * 2165833 * 2
def baseEnd_2165833 : Nat := 1112113346369329902127021

theorem tailTrace_2165833 : CollatzResearch.WordTrace tailWord_2165833 prefixEnd_2165833 1112113346369329902127021 := by
  unfold tailWord_2165833
  simp only [CollatzResearch.WordTrace]
  refine ⟨78994419162564410672678153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52662946108376273781785435 78994419162564410672678153)
  ·
    refine ⟨59245814371923308004508615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78994419162564410672678153 59245814371923308004508615)
    ·
      refine ⟨88868721557884962006762923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59245814371923308004508615 88868721557884962006762923)
      ·
        refine ⟨133303082336827443010144385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88868721557884962006762923 133303082336827443010144385)
        ·
          refine ⟨99977311752620582257608289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133303082336827443010144385 99977311752620582257608289)
          ·
            refine ⟨74982983814465436693206217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99977311752620582257608289 74982983814465436693206217)
            ·
              refine ⟨56237237860849077519904663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74982983814465436693206217 56237237860849077519904663)
              ·
                refine ⟨84355856791273616279856995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56237237860849077519904663 84355856791273616279856995)
                ·
                  refine ⟨126533785186910424419785493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84355856791273616279856995 126533785186910424419785493)
                  ·
                    refine ⟨5931271180636426144677445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126533785186910424419785493 5931271180636426144677445)
                    ·
                      refine ⟨1112113346369329902127021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5931271180636426144677445 1112113346369329902127021)
                      ·
                        rfl

theorem cell23_2165833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_2165833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165833 prefixEnd_2165833 := by exact prefixLift 2165833
  have htrace : WordTrace (prefixWord ++ tailWord_2165833) baseStart_2165833 baseEnd_2165833 := by
    simpa [prefixWord, tailWord_2165833, baseEnd_2165833] using wordTrace_append hprefix tailTrace_2165833
  have hstable : (prefixWord ++ tailWord_2165833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165833).length < 2 ^ (prefixWord ++ tailWord_2165833).sum := by decide
  have hdescent : baseEnd_2165833 < baseStart_2165833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165837 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2165837 : Nat := 118140960795 + 2165837 * 2 ^ 59
def prefixEnd_2165837 : Nat := 4983230072969 + 3 ^ 40 * 2165837 * 2
def baseEnd_2165837 : Nat := 1112115400291947886477003

theorem tailTrace_2165837 : CollatzResearch.WordTrace tailWord_2165837 prefixEnd_2165837 1112115400291947886477003 := by
  unfold tailWord_2165837
  simp only [CollatzResearch.WordTrace]
  refine ⟨78994565054549919355823765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52663043369699946237215843 78994565054549919355823765)
  ·
    refine ⟨3702870236932027469804239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78994565054549919355823765 3702870236932027469804239)
    ·
      refine ⟨5554305355398041204706359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3702870236932027469804239 5554305355398041204706359)
      ·
        refine ⟨8331458033097061807059539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554305355398041204706359 8331458033097061807059539)
        ·
          refine ⟨12497187049645592710589309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8331458033097061807059539 12497187049645592710589309)
          ·
            refine ⟨4686445143617097266470991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12497187049645592710589309 4686445143617097266470991)
            ·
              refine ⟨7029667715425645899706487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686445143617097266470991 7029667715425645899706487)
              ·
                refine ⟨10544501573138468849559731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029667715425645899706487 10544501573138468849559731)
                ·
                  refine ⟨15816752359707703274339597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10544501573138468849559731 15816752359707703274339597)
                  ·
                    refine ⟨5931282134890388727877349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15816752359707703274339597 5931282134890388727877349)
                    ·
                      refine ⟨1112115400291947886477003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5931282134890388727877349 1112115400291947886477003)
                      ·
                        rfl

theorem cell23_2165837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2165837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165837 prefixEnd_2165837 := by exact prefixLift 2165837
  have htrace : WordTrace (prefixWord ++ tailWord_2165837) baseStart_2165837 baseEnd_2165837 := by
    simpa [prefixWord, tailWord_2165837, baseEnd_2165837] using wordTrace_append hprefix tailTrace_2165837
  have hstable : (prefixWord ++ tailWord_2165837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165837).length < 2 ^ (prefixWord ++ tailWord_2165837).sum := by decide
  have hdescent : baseEnd_2165837 < baseStart_2165837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165873 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_2165873 : Nat := 118140960795 + 2165873 * 2 ^ 59
def prefixEnd_2165873 : Nat := 4983230072969 + 3 ^ 40 * 2165873 * 2
def baseEnd_2165873 : Nat := 370711295198503248542279

theorem tailTrace_2165873 : CollatzResearch.WordTrace tailWord_2165873 prefixEnd_2165873 370711295198503248542279 := by
  unfold tailWord_2165873
  simp only [CollatzResearch.WordTrace]
  refine ⟨78995878082419497504134273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52663918721612998336089515 78995878082419497504134273)
  ·
    refine ⟨59246908561814623128100705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78995878082419497504134273 59246908561814623128100705)
    ·
      refine ⟨44435181421360967346075529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59246908561814623128100705 44435181421360967346075529)
      ·
        refine ⟨33326386066020725509556647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44435181421360967346075529 33326386066020725509556647)
        ·
          refine ⟨49989579099031088264334971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33326386066020725509556647 49989579099031088264334971)
          ·
            refine ⟨74984368648546632396502457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49989579099031088264334971 74984368648546632396502457)
            ·
              refine ⟨56238276486409974297376843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74984368648546632396502457 56238276486409974297376843)
              ·
                refine ⟨84357414729614961446065265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56238276486409974297376843 84357414729614961446065265)
                ·
                  refine ⟨63268061047211221084548949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84357414729614961446065265 63268061047211221084548949)
                  ·
                    refine ⟨370711295198503248542279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63268061047211221084548949 370711295198503248542279)
                    ·
                      rfl

theorem cell23_2165873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_2165873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165873 prefixEnd_2165873 := by exact prefixLift 2165873
  have htrace : WordTrace (prefixWord ++ tailWord_2165873) baseStart_2165873 baseEnd_2165873 := by
    simpa [prefixWord, tailWord_2165873, baseEnd_2165873] using wordTrace_append hprefix tailTrace_2165873
  have hstable : (prefixWord ++ tailWord_2165873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165873).length < 2 ^ (prefixWord ++ tailWord_2165873).sum := by decide
  have hdescent : baseEnd_2165873 < baseStart_2165873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165883 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_2165883 : Nat := 118140960795 + 2165883 * 2 ^ 59
def prefixEnd_2165883 : Nat := 4983230072969 + 3 ^ 40 * 2165883 * 2
def baseEnd_2165883 : Nat := 1112139020402054706501791

theorem tailTrace_2165883 : CollatzResearch.WordTrace tailWord_2165883 prefixEnd_2165883 1112139020402054706501791 := by
  unfold tailWord_2165883
  simp only [CollatzResearch.WordTrace]
  refine ⟨78996242812383269211998303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52664161874922179474665535 78996242812383269211998303)
  ·
    refine ⟨118494364218574903817997455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78996242812383269211998303 118494364218574903817997455)
    ·
      refine ⟨177741546327862355726996183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118494364218574903817997455 177741546327862355726996183)
      ·
        refine ⟨266612319491793533590494275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177741546327862355726996183 266612319491793533590494275)
        ·
          refine ⟨399918479237690300385741413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266612319491793533590494275 399918479237690300385741413)
          ·
            refine ⟨74984714857066931322326515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399918479237690300385741413 74984714857066931322326515)
            ·
              refine ⟨112477072285600396983489773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74984714857066931322326515 112477072285600396983489773)
              ·
                refine ⟨42178902107100148868808665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112477072285600396983489773 42178902107100148868808665)
                ·
                  refine ⟨31634176580325111651606499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42178902107100148868808665 31634176580325111651606499)
                  ·
                    refine ⟨47451264870487667477409749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31634176580325111651606499 47451264870487667477409749)
                    ·
                      refine ⟨1112139020402054706501791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47451264870487667477409749 1112139020402054706501791)
                      ·
                        rfl

theorem cell23_2165883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_2165883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165883 prefixEnd_2165883 := by exact prefixLift 2165883
  have htrace : WordTrace (prefixWord ++ tailWord_2165883) baseStart_2165883 baseEnd_2165883 := by
    simpa [prefixWord, tailWord_2165883, baseEnd_2165883] using wordTrace_append hprefix tailTrace_2165883
  have hstable : (prefixWord ++ tailWord_2165883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165883).length < 2 ^ (prefixWord ++ tailWord_2165883).sum := by decide
  have hdescent : baseEnd_2165883 < baseStart_2165883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165897 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 1, 5, 2]
def baseStart_2165897 : Nat := 118140960795 + 2165897 * 2 ^ 59
def prefixEnd_2165897 : Nat := 4983230072969 + 3 ^ 40 * 2165897 * 2
def baseEnd_2165897 : Nat := 1112146209131217651726727

theorem tailTrace_2165897 : CollatzResearch.WordTrace tailWord_2165897 prefixEnd_2165897 1112146209131217651726727 := by
  unfold tailWord_2165897
  simp only [CollatzResearch.WordTrace]
  refine ⟨78996753434332549603007945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52664502289555033068671963 78996753434332549603007945)
  ·
    refine ⟨59247565075749412202255959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78996753434332549603007945 59247565075749412202255959)
    ·
      refine ⟨88871347613624118303383939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59247565075749412202255959 88871347613624118303383939)
      ·
        refine ⟨133307021420436177455075909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88871347613624118303383939 133307021420436177455075909)
        ·
          refine ⟨24995066516331783272826733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133307021420436177455075909 24995066516331783272826733)
          ·
            refine ⟨9373149943624418727310025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24995066516331783272826733 9373149943624418727310025)
            ·
              refine ⟨7029862457718314045482519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9373149943624418727310025 7029862457718314045482519)
              ·
                refine ⟨10544793686577471068223779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029862457718314045482519 10544793686577471068223779)
                ·
                  refine ⟨15817190529866206602335669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10544793686577471068223779 15817190529866206602335669)
                  ·
                    refine ⟨1482861612174956868968969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15817190529866206602335669 1482861612174956868968969)
                    ·
                      refine ⟨1112146209131217651726727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482861612174956868968969 1112146209131217651726727)
                      ·
                        rfl

theorem cell23_2165897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 5, 2].length) (baseStart_2165897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165897 prefixEnd_2165897 := by exact prefixLift 2165897
  have htrace : WordTrace (prefixWord ++ tailWord_2165897) baseStart_2165897 baseEnd_2165897 := by
    simpa [prefixWord, tailWord_2165897, baseEnd_2165897] using wordTrace_append hprefix tailTrace_2165897
  have hstable : (prefixWord ++ tailWord_2165897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165897).length < 2 ^ (prefixWord ++ tailWord_2165897).sum := by decide
  have hdescent : baseEnd_2165897 < baseStart_2165897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165904 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 1, 1, 3]
def baseStart_2165904 : Nat := 118140960795 + 2165904 * 2 ^ 59
def prefixEnd_2165904 : Nat := 4983230072969 + 3 ^ 40 * 2165904 * 2
def baseEnd_2165904 : Nat := 1112149803495799124339195

theorem tailTrace_2165904 : CollatzResearch.WordTrace tailWord_2165904 prefixEnd_2165904 1112149803495799124339195 := by
  unfold tailWord_2165904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39498504372653594899256383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52664672496871459865675177 39498504372653594899256383)
  ·
    refine ⟨59247756558980392348884575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39498504372653594899256383 59247756558980392348884575)
    ·
      refine ⟨88871634838470588523326863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59247756558980392348884575 88871634838470588523326863)
      ·
        refine ⟨133307452257705882784990295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88871634838470588523326863 133307452257705882784990295)
        ·
          refine ⟨199961178386558824177485443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133307452257705882784990295 199961178386558824177485443)
          ·
            refine ⟨299941767579838236266228165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199961178386558824177485443 299941767579838236266228165)
            ·
              refine ⟨56239081421219669299917781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299941767579838236266228165 56239081421219669299917781)
              ·
                refine ⟨1318103470809835999216823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56239081421219669299917781 1318103470809835999216823)
                ·
                  refine ⟨1977155206214753998825235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318103470809835999216823 1977155206214753998825235)
                  ·
                    refine ⟨2965732809322130998237853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1977155206214753998825235 2965732809322130998237853)
                    ·
                      refine ⟨1112149803495799124339195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965732809322130998237853 1112149803495799124339195)
                      ·
                        rfl

theorem cell23_2165904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 1, 3].length) (baseStart_2165904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165904 prefixEnd_2165904 := by exact prefixLift 2165904
  have htrace : WordTrace (prefixWord ++ tailWord_2165904) baseStart_2165904 baseEnd_2165904 := by
    simpa [prefixWord, tailWord_2165904, baseEnd_2165904] using wordTrace_append hprefix tailTrace_2165904
  have hstable : (prefixWord ++ tailWord_2165904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165904).length < 2 ^ (prefixWord ++ tailWord_2165904).sum := by decide
  have hdescent : baseEnd_2165904 < baseStart_2165904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165914 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2165914 : Nat := 118140960795 + 2165914 * 2 ^ 59
def prefixEnd_2165914 : Nat := 4983230072969 + 3 ^ 40 * 2165914 * 2
def baseEnd_2165914 : Nat := 1112154938302344085214149

theorem tailTrace_2165914 : CollatzResearch.WordTrace tailWord_2165914 prefixEnd_2165914 1112154938302344085214149 := by
  unfold tailWord_2165914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19749343368817740376594199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52664915650180641004251197 19749343368817740376594199)
  ·
    refine ⟨29624015053226610564891299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19749343368817740376594199 29624015053226610564891299)
    ·
      refine ⟨44436022579839915847336949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29624015053226610564891299 44436022579839915847336949)
      ·
        refine ⟨4165877116859992110687839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44436022579839915847336949 4165877116859992110687839)
        ·
          refine ⟨6248815675289988166031759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165877116859992110687839 6248815675289988166031759)
          ·
            refine ⟨9373223512934982249047639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6248815675289988166031759 9373223512934982249047639)
            ·
              refine ⟨14059835269402473373571459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9373223512934982249047639 14059835269402473373571459)
              ·
                refine ⟨21089752904103710060357189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14059835269402473373571459 21089752904103710060357189)
                ·
                  refine ⟨3954328669519445636316973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21089752904103710060357189 3954328669519445636316973)
                  ·
                    refine ⟨1482873251069792113618865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3954328669519445636316973 1482873251069792113618865)
                    ·
                      refine ⟨1112154938302344085214149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482873251069792113618865 1112154938302344085214149)
                      ·
                        rfl

theorem cell23_2165914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2165914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165914 prefixEnd_2165914 := by exact prefixLift 2165914
  have htrace : WordTrace (prefixWord ++ tailWord_2165914) baseStart_2165914 baseEnd_2165914 := by
    simpa [prefixWord, tailWord_2165914, baseEnd_2165914] using wordTrace_append hprefix tailTrace_2165914
  have hstable : (prefixWord ++ tailWord_2165914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165914).length < 2 ^ (prefixWord ++ tailWord_2165914).sum := by decide
  have hdescent : baseEnd_2165914 < baseStart_2165914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165947 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 3]
def baseStart_2165947 : Nat := 118140960795 + 2165947 * 2 ^ 59
def prefixEnd_2165947 : Nat := 4983230072969 + 3 ^ 40 * 2165947 * 2
def baseEnd_2165947 : Nat := 1112171883163942456101497

theorem tailTrace_2165947 : CollatzResearch.WordTrace tailWord_2165947 prefixEnd_2165947 1112171883163942456101497 := by
  unfold tailWord_2165947
  simp only [CollatzResearch.WordTrace]
  refine ⟨78998577084151408142328095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52665718056100938761552063 78998577084151408142328095)
  ·
    refine ⟨118497865626227112213492143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78998577084151408142328095 118497865626227112213492143)
    ·
      refine ⟨177746798439340668320238215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118497865626227112213492143 177746798439340668320238215)
      ·
        refine ⟨266620197659011002480357323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177746798439340668320238215 266620197659011002480357323)
        ·
          refine ⟨399930296488516503720535985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266620197659011002480357323 399930296488516503720535985)
          ·
            refine ⟨299947722366387377790401989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399930296488516503720535985 299947722366387377790401989)
            ·
              refine ⟨56240197943697633335700373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299947722366387377790401989 56240197943697633335700373)
              ·
                refine ⟨2636259278610826562610955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56240197943697633335700373 2636259278610826562610955)
                ·
                  refine ⟨3954388917916239843916433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636259278610826562610955 3954388917916239843916433)
                  ·
                    refine ⟨2965791688437179882937325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954388917916239843916433 2965791688437179882937325)
                    ·
                      refine ⟨1112171883163942456101497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965791688437179882937325 1112171883163942456101497)
                      ·
                        rfl

theorem cell23_2165947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 3].length) (baseStart_2165947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165947 prefixEnd_2165947 := by exact prefixLift 2165947
  have htrace : WordTrace (prefixWord ++ tailWord_2165947) baseStart_2165947 baseEnd_2165947 := by
    simpa [prefixWord, tailWord_2165947, baseEnd_2165947] using wordTrace_append hprefix tailTrace_2165947
  have hstable : (prefixWord ++ tailWord_2165947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165947).length < 2 ^ (prefixWord ++ tailWord_2165947).sum := by decide
  have hdescent : baseEnd_2165947 < baseStart_2165947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165972 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2165972 : Nat := 118140960795 + 2165972 * 2 ^ 59
def prefixEnd_2165972 : Nat := 4983230072969 + 3 ^ 40 * 2165972 * 2
def baseEnd_2165972 : Nat := 1112184720180304858288883

theorem tailTrace_2165972 : CollatzResearch.WordTrace tailWord_2165972 prefixEnd_2165972 1112184720180304858288883 := by
  unfold tailWord_2165972
  simp only [CollatzResearch.WordTrace]
  refine ⟨39499744454530418705994085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52666325939373891607992113 39499744454530418705994085)
  ·
    refine ⟨7406202085224453507373891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39499744454530418705994085 7406202085224453507373891)
    ·
      refine ⟨11109303127836680261060837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406202085224453507373891 11109303127836680261060837)
      ·
        refine ⟨2082994336469377548948907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11109303127836680261060837 2082994336469377548948907)
        ·
          refine ⟨3124491504704066323423361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082994336469377548948907 3124491504704066323423361)
          ·
            refine ⟨2343368628528049742567521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124491504704066323423361 2343368628528049742567521)
            ·
              refine ⟨1757526471396037306925641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343368628528049742567521 1757526471396037306925641)
              ·
                refine ⟨1318144853547027980194231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757526471396037306925641 1318144853547027980194231)
                ·
                  refine ⟨1977217280320541970291347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318144853547027980194231 1977217280320541970291347)
                  ·
                    refine ⟨2965825920480812955437021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1977217280320541970291347 2965825920480812955437021)
                    ·
                      refine ⟨1112184720180304858288883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965825920480812955437021 1112184720180304858288883)
                      ·
                        rfl

theorem cell23_2165972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2165972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165972 prefixEnd_2165972 := by exact prefixLift 2165972
  have htrace : WordTrace (prefixWord ++ tailWord_2165972) baseStart_2165972 baseEnd_2165972 := by
    simpa [prefixWord, tailWord_2165972, baseEnd_2165972] using wordTrace_append hprefix tailTrace_2165972
  have hstable : (prefixWord ++ tailWord_2165972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165972).length < 2 ^ (prefixWord ++ tailWord_2165972).sum := by decide
  have hdescent : baseEnd_2165972 < baseStart_2165972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165994 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2165994 : Nat := 118140960795 + 2165994 * 2 ^ 59
def prefixEnd_2165994 : Nat := 4983230072969 + 3 ^ 40 * 2165994 * 2
def baseEnd_2165994 : Nat := 1112196016754703772213781

theorem tailTrace_2165994 : CollatzResearch.WordTrace tailWord_2165994 prefixEnd_2165994 1112196016754703772213781 := by
  unfold tailWord_2165994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19750072828745283792322259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52666860876654090112859357 19750072828745283792322259)
  ·
    refine ⟨29625109243117925688483389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19750072828745283792322259 29625109243117925688483389)
    ·
      refine ⟨11109415966169222133181271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29625109243117925688483389 11109415966169222133181271)
      ·
        refine ⟨16664123949253833199771907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11109415966169222133181271 16664123949253833199771907)
        ·
          refine ⟨24996185923880749799657861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16664123949253833199771907 24996185923880749799657861)
          ·
            refine ⟨4686784860727640587435849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24996185923880749799657861 4686784860727640587435849)
            ·
              refine ⟨3515088645545730440576887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4686784860727640587435849 3515088645545730440576887)
              ·
                refine ⟨5272632968318595660865331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515088645545730440576887 5272632968318595660865331)
                ·
                  refine ⟨7908949452477893491297997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272632968318595660865331 7908949452477893491297997)
                  ·
                    refine ⟨2965856044679210059236749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7908949452477893491297997 2965856044679210059236749)
                    ·
                      refine ⟨1112196016754703772213781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2965856044679210059236749 1112196016754703772213781)
                      ·
                        rfl

theorem cell23_2165994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2165994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2165994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2165994 prefixEnd_2165994 := by exact prefixLift 2165994
  have htrace : WordTrace (prefixWord ++ tailWord_2165994) baseStart_2165994 baseEnd_2165994 := by
    simpa [prefixWord, tailWord_2165994, baseEnd_2165994] using wordTrace_append hprefix tailTrace_2165994
  have hstable : (prefixWord ++ tailWord_2165994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165994).length < 2 ^ (prefixWord ++ tailWord_2165994).sum := by decide
  have hdescent : baseEnd_2165994 < baseStart_2165994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166010 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_2166010 : Nat := 118140960795 + 2166010 * 2 ^ 59
def prefixEnd_2166010 : Nat := 4983230072969 + 3 ^ 40 * 2166010 * 2
def baseEnd_2166010 : Nat := 370734744148391903204569

theorem tailTrace_2166010 : CollatzResearch.WordTrace tailWord_2166010 prefixEnd_2166010 370734744148391903204569 := by
  unfold tailWord_2166010
  simp only [CollatzResearch.WordTrace]
  refine ⟨19750218720730792475467871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52667249921948779934580989 19750218720730792475467871)
  ·
    refine ⟨29625328081096188713201807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19750218720730792475467871 29625328081096188713201807)
    ·
      refine ⟨44437992121644283069802711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29625328081096188713201807 44437992121644283069802711)
      ·
        refine ⟨66656988182466424604704067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44437992121644283069802711 66656988182466424604704067)
        ·
          refine ⟨99985482273699636907056101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66656988182466424604704067 99985482273699636907056101)
          ·
            refine ⟨18747277926318681920073019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99985482273699636907056101 18747277926318681920073019)
            ·
              refine ⟨28120916889478022880109529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18747277926318681920073019 28120916889478022880109529)
              ·
                refine ⟨21090687667108517160082147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28120916889478022880109529 21090687667108517160082147)
                ·
                  refine ⟨31636031500662775740123221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21090687667108517160082147 31636031500662775740123221)
                  ·
                    refine ⟨370734744148391903204569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31636031500662775740123221 370734744148391903204569)
                    ·
                      rfl

theorem cell23_2166010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_2166010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166010 prefixEnd_2166010 := by exact prefixLift 2166010
  have htrace : WordTrace (prefixWord ++ tailWord_2166010) baseStart_2166010 baseEnd_2166010 := by
    simpa [prefixWord, tailWord_2166010, baseEnd_2166010] using wordTrace_append hprefix tailTrace_2166010
  have hstable : (prefixWord ++ tailWord_2166010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166010).length < 2 ^ (prefixWord ++ tailWord_2166010).sum := by decide
  have hdescent : baseEnd_2166010 < baseStart_2166010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166051 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 1, 4, 2]
def baseStart_2166051 : Nat := 118140960795 + 2166051 * 2 ^ 59
def prefixEnd_2166051 : Nat := 4983230072969 + 3 ^ 40 * 2166051 * 2
def baseEnd_2166051 : Nat := 1112225285152010049201019

theorem tailTrace_2166051 : CollatzResearch.WordTrace tailWord_2166051 prefixEnd_2166051 1112225285152010049201019 := by
  unfold tailWord_2166051
  simp only [CollatzResearch.WordTrace]
  refine ⟨79002370275774633904114007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52668246850516422602742671 79002370275774633904114007)
  ·
    refine ⟨118503555413661950856171011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79002370275774633904114007 118503555413661950856171011)
    ·
      refine ⟨177755333120492926284256517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118503555413661950856171011 177755333120492926284256517)
      ·
        refine ⟨33329124960092423678298097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177755333120492926284256517 33329124960092423678298097)
        ·
          refine ⟨24996843720069317758723573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33329124960092423678298097 24996843720069317758723573)
          ·
            refine ⟨2343454098756498539880335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24996843720069317758723573 2343454098756498539880335)
            ·
              refine ⟨3515181148134747809820503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343454098756498539880335 3515181148134747809820503)
              ·
                refine ⟨5272771722202121714730755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515181148134747809820503 5272771722202121714730755)
                ·
                  refine ⟨7909157583303182572096133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272771722202121714730755 7909157583303182572096133)
                  ·
                    refine ⟨1482967046869346732268025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7909157583303182572096133 1482967046869346732268025)
                    ·
                      refine ⟨1112225285152010049201019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482967046869346732268025 1112225285152010049201019)
                      ·
                        rfl

theorem cell23_2166051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_2166051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166051 prefixEnd_2166051 := by exact prefixLift 2166051
  have htrace : WordTrace (prefixWord ++ tailWord_2166051) baseStart_2166051 baseEnd_2166051 := by
    simpa [prefixWord, tailWord_2166051, baseEnd_2166051] using wordTrace_append hprefix tailTrace_2166051
  have hstable : (prefixWord ++ tailWord_2166051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166051).length < 2 ^ (prefixWord ++ tailWord_2166051).sum := by decide
  have hdescent : baseEnd_2166051 < baseStart_2166051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166087 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 4, 5]
def baseStart_2166087 : Nat := 118140960795 + 2166087 * 2 ^ 59
def prefixEnd_2166087 : Nat := 4983230072969 + 3 ^ 40 * 2166087 * 2
def baseEnd_2166087 : Nat := 370747923485190636116951

theorem tailTrace_2166087 : CollatzResearch.WordTrace tailWord_2166087 prefixEnd_2166087 370747923485190636116951 := by
  unfold tailWord_2166087
  simp only [CollatzResearch.WordTrace]
  refine ⟨79003683303644212052424515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52669122202429474701616343 79003683303644212052424515)
  ·
    refine ⟨118505524955466318078636773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79003683303644212052424515 118505524955466318078636773)
    ·
      refine ⟨22219785929149934639744395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118505524955466318078636773 22219785929149934639744395)
      ·
        refine ⟨33329678893724901959616593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22219785929149934639744395 33329678893724901959616593)
        ·
          refine ⟨24997259170293676469712445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33329678893724901959616593 24997259170293676469712445)
          ·
            refine ⟨9373972188860128676142167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24997259170293676469712445 9373972188860128676142167)
            ·
              refine ⟨14060958283290193014213251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9373972188860128676142167 14060958283290193014213251)
              ·
                refine ⟨21091437424935289521319877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14060958283290193014213251 21091437424935289521319877)
                ·
                  refine ⟨3954644517175366785247477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21091437424935289521319877 3954644517175366785247477)
                  ·
                    refine ⟨370747923485190636116951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3954644517175366785247477 370747923485190636116951)
                    ·
                      rfl

theorem cell23_2166087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_2166087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166087 prefixEnd_2166087 := by exact prefixLift 2166087
  have htrace : WordTrace (prefixWord ++ tailWord_2166087) baseStart_2166087 baseEnd_2166087 := by
    simpa [prefixWord, tailWord_2166087, baseEnd_2166087] using wordTrace_append hprefix tailTrace_2166087
  have hstable : (prefixWord ++ tailWord_2166087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166087).length < 2 ^ (prefixWord ++ tailWord_2166087).sum := by decide
  have hdescent : baseEnd_2166087 < baseStart_2166087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166094 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_2166094 : Nat := 118140960795 + 2166094 * 2 ^ 59
def prefixEnd_2166094 : Nat := 4983230072969 + 3 ^ 40 * 2166094 * 2
def baseEnd_2166094 : Nat := 1112247364820153380963321

theorem tailTrace_2166094 : CollatzResearch.WordTrace tailWord_2166094 prefixEnd_2166094 1112247364820153380963321 := by
  unfold tailWord_2166094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875492326827356530991167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52669292409745901498619557 9875492326827356530991167)
  ·
    refine ⟨14813238490241034796486751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9875492326827356530991167 14813238490241034796486751)
    ·
      refine ⟨22219857735361552194730127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14813238490241034796486751 22219857735361552194730127)
      ·
        refine ⟨33329786603042328292095191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22219857735361552194730127 33329786603042328292095191)
        ·
          refine ⟨49994679904563492438142787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33329786603042328292095191 49994679904563492438142787)
          ·
            refine ⟨74992019856845238657214181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49994679904563492438142787 74992019856845238657214181)
            ·
              refine ⟨14061003723158482248227659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74992019856845238657214181 14061003723158482248227659)
              ·
                refine ⟨21091505584737723372341489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14061003723158482248227659 21091505584737723372341489)
                ·
                  refine ⟨15818629188553292529256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21091505584737723372341489 15818629188553292529256117)
                  ·
                    refine ⟨1482996486426871174617761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15818629188553292529256117 1482996486426871174617761)
                    ·
                      refine ⟨1112247364820153380963321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1482996486426871174617761 1112247364820153380963321)
                      ·
                        rfl

theorem cell23_2166094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_2166094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166094 prefixEnd_2166094 := by exact prefixLift 2166094
  have htrace : WordTrace (prefixWord ++ tailWord_2166094) baseStart_2166094 baseEnd_2166094 := by
    simpa [prefixWord, tailWord_2166094, baseEnd_2166094] using wordTrace_append hprefix tailTrace_2166094
  have hstable : (prefixWord ++ tailWord_2166094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166094).length < 2 ^ (prefixWord ++ tailWord_2166094).sum := by decide
  have hdescent : baseEnd_2166094 < baseStart_2166094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166097 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_2166097 : Nat := 118140960795 + 2166097 * 2 ^ 59
def prefixEnd_2166097 : Nat := 4983230072969 + 3 ^ 40 * 2166097 * 2
def baseEnd_2166097 : Nat := 1112248905262116869225807

theorem tailTrace_2166097 : CollatzResearch.WordTrace tailWord_2166097 prefixEnd_2166097 1112248905262116869225807 := by
  unfold tailWord_2166097
  simp only [CollatzResearch.WordTrace]
  refine ⟨79004048033607983760288545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52669365355738655840192363 79004048033607983760288545)
  ·
    refine ⟨59253036025205987820216409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79004048033607983760288545 59253036025205987820216409)
    ·
      refine ⟨44439777018904490865162307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59253036025205987820216409 44439777018904490865162307)
      ·
        refine ⟨66659665528356736297743461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44439777018904490865162307 66659665528356736297743461)
        ·
          refine ⟨12498687286566888055826899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66659665528356736297743461 12498687286566888055826899)
          ·
            refine ⟨18748030929850332083740349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12498687286566888055826899 18748030929850332083740349)
            ·
              refine ⟨7030511598693874531402631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18748030929850332083740349 7030511598693874531402631)
              ·
                refine ⟨10545767398040811797103947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7030511598693874531402631 10545767398040811797103947)
                ·
                  refine ⟨15818651097061217695655921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10545767398040811797103947 15818651097061217695655921)
                  ·
                    refine ⟨11863988322795913271741941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15818651097061217695655921 11863988322795913271741941)
                    ·
                      refine ⟨1112248905262116869225807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11863988322795913271741941 1112248905262116869225807)
                      ·
                        rfl

theorem cell23_2166097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_2166097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166097 prefixEnd_2166097 := by exact prefixLift 2166097
  have htrace : WordTrace (prefixWord ++ tailWord_2166097) baseStart_2166097 baseEnd_2166097 := by
    simpa [prefixWord, tailWord_2166097, baseEnd_2166097] using wordTrace_append hprefix tailTrace_2166097
  have hstable : (prefixWord ++ tailWord_2166097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166097).length < 2 ^ (prefixWord ++ tailWord_2166097).sum := by decide
  have hdescent : baseEnd_2166097 < baseStart_2166097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166124 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_2166124 : Nat := 118140960795 + 2166124 * 2 ^ 59
def prefixEnd_2166124 : Nat := 4983230072969 + 3 ^ 40 * 2166124 * 2
def baseEnd_2166124 : Nat := 1112262769239788263588183

theorem tailTrace_2166124 : CollatzResearch.WordTrace tailWord_2166124 prefixEnd_2166124 1112262769239788263588183 := by
  unfold tailWord_2166124
  simp only [CollatzResearch.WordTrace]
  refine ⟨39502516402255083685760713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52670021869673444914347617 39502516402255083685760713)
  ·
    refine ⟨29626887301691312764320535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39502516402255083685760713 29626887301691312764320535)
    ·
      refine ⟨44440330952536969146480803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29626887301691312764320535 44440330952536969146480803)
      ·
        refine ⟨66660496428805453719721205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44440330952536969146480803 66660496428805453719721205)
        ·
          refine ⟨6249421540200511286223863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66660496428805453719721205 6249421540200511286223863)
          ·
            refine ⟨9374132310300766929335795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6249421540200511286223863 9374132310300766929335795)
            ·
              refine ⟨14061198465451150394003693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9374132310300766929335795 14061198465451150394003693)
              ·
                refine ⟨5272949424544181397751385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14061198465451150394003693 5272949424544181397751385)
                ·
                  refine ⟨3954712068408136048313539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5272949424544181397751385 3954712068408136048313539)
                  ·
                    refine ⟨5932068102612204072470309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3954712068408136048313539 5932068102612204072470309)
                    ·
                      refine ⟨1112262769239788263588183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5932068102612204072470309 1112262769239788263588183)
                      ·
                        rfl

theorem cell23_2166124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_2166124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166124 prefixEnd_2166124 := by exact prefixLift 2166124
  have htrace : WordTrace (prefixWord ++ tailWord_2166124) baseStart_2166124 baseEnd_2166124 := by
    simpa [prefixWord, tailWord_2166124, baseEnd_2166124] using wordTrace_append hprefix tailTrace_2166124
  have hstable : (prefixWord ++ tailWord_2166124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166124).length < 2 ^ (prefixWord ++ tailWord_2166124).sum := by decide
  have hdescent : baseEnd_2166124 < baseStart_2166124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166142 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_2166142 : Nat := 118140960795 + 2166142 * 2 ^ 59
def prefixEnd_2166142 : Nat := 4983230072969 + 3 ^ 40 * 2166142 * 2
def baseEnd_2166142 : Nat := 123585779099063243684789

theorem tailTrace_2166142 : CollatzResearch.WordTrace tailWord_2166142 prefixEnd_2166142 123585779099063243684789 := by
  unfold tailWord_2166142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875711164805619555709585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52670459545629970963784453 9875711164805619555709585)
  ·
    refine ⟨7406783373604214666782189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9875711164805619555709585 7406783373604214666782189)
    ·
      refine ⟨2777543765101580500043321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7406783373604214666782189 2777543765101580500043321)
      ·
        refine ⟨2083157823826185375032491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2777543765101580500043321 2083157823826185375032491)
        ·
          refine ⟨3124736735739278062548737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2083157823826185375032491 3124736735739278062548737)
          ·
            refine ⟨2343552551804458546911553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3124736735739278062548737 2343552551804458546911553)
            ·
              refine ⟨1757664413853343910183665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343552551804458546911553 1757664413853343910183665)
              ·
                refine ⟨1318248310390007932637749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757664413853343910183665 1318248310390007932637749)
                ·
                  refine ⟨123585779099063243684789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318248310390007932637749 123585779099063243684789)
                  ·
                    rfl

theorem cell23_2166142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_2166142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166142 prefixEnd_2166142 := by exact prefixLift 2166142
  have htrace : WordTrace (prefixWord ++ tailWord_2166142) baseStart_2166142 baseEnd_2166142 := by
    simpa [prefixWord, tailWord_2166142, baseEnd_2166142] using wordTrace_append hprefix tailTrace_2166142
  have hstable : (prefixWord ++ tailWord_2166142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166142).length < 2 ^ (prefixWord ++ tailWord_2166142).sum := by decide
  have hdescent : baseEnd_2166142 < baseStart_2166142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166158 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2166158 : Nat := 118140960795 + 2166158 * 2 ^ 59
def prefixEnd_2166158 : Nat := 4983230072969 + 3 ^ 40 * 2166158 * 2
def baseEnd_2166158 : Nat := 1112280227582041130563027

theorem tailTrace_2166158 : CollatzResearch.WordTrace tailWord_2166158 prefixEnd_2166158 1112280227582041130563027 := by
  unfold tailWord_2166158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875784110798373897282391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52670848590924660785506085 9875784110798373897282391)
  ·
    refine ⟨14813676166197560845923587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9875784110798373897282391 14813676166197560845923587)
    ·
      refine ⟨22220514249296341268885381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14813676166197560845923587 22220514249296341268885381)
      ·
        refine ⟨4166346421743063987916009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22220514249296341268885381 4166346421743063987916009)
        ·
          refine ⟨3124759816307297990937007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4166346421743063987916009 3124759816307297990937007)
          ·
            refine ⟨4687139724460946986405511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124759816307297990937007 4687139724460946986405511)
            ·
              refine ⟨7030709586691420479608267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4687139724460946986405511 7030709586691420479608267)
              ·
                refine ⟨10546064380037130719412401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7030709586691420479608267 10546064380037130719412401)
                ·
                  refine ⟨7909548285027848039559301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10546064380037130719412401 7909548285027848039559301)
                  ·
                    refine ⟨1483040303442721507417369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7909548285027848039559301 1483040303442721507417369)
                    ·
                      refine ⟨1112280227582041130563027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483040303442721507417369 1112280227582041130563027)
                      ·
                        rfl

theorem cell23_2166158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2166158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166158 prefixEnd_2166158 := by exact prefixLift 2166158
  have htrace : WordTrace (prefixWord ++ tailWord_2166158) baseStart_2166158 baseEnd_2166158 := by
    simpa [prefixWord, tailWord_2166158, baseEnd_2166158] using wordTrace_append hprefix tailTrace_2166158
  have hstable : (prefixWord ++ tailWord_2166158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166158).length < 2 ^ (prefixWord ++ tailWord_2166158).sum := by decide
  have hdescent : baseEnd_2166158 < baseStart_2166158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166178 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2166178 : Nat := 118140960795 + 2166178 * 2 ^ 59
def prefixEnd_2166178 : Nat := 4983230072969 + 3 ^ 40 * 2166178 * 2
def baseEnd_2166178 : Nat := 1112290497195131052312935

theorem tailTrace_2166178 : CollatzResearch.WordTrace tailWord_2166178 prefixEnd_2166178 1112290497195131052312935 := by
  unfold tailWord_2166178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19751750586578633648496797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52671334897543023062658125 19751750586578633648496797)
  ·
    refine ⟨7406906469966987618186299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19751750586578633648496797 7406906469966987618186299)
    ·
      refine ⟨11110359704950481427279449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406906469966987618186299 11110359704950481427279449)
      ·
        refine ⟨8332769778712861070459587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11110359704950481427279449 8332769778712861070459587)
        ·
          refine ⟨12499154668069291605689381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8332769778712861070459587 12499154668069291605689381)
          ·
            refine ⟨2343591500262992176066759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12499154668069291605689381 2343591500262992176066759)
            ·
              refine ⟨3515387250394488264100139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343591500262992176066759 3515387250394488264100139)
              ·
                refine ⟨5273080875591732396150209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515387250394488264100139 5273080875591732396150209)
                ·
                  refine ⟨3954810656693799297112657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5273080875591732396150209 3954810656693799297112657)
                  ·
                    refine ⟨2966107992520349472834493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3954810656693799297112657 2966107992520349472834493)
                    ·
                      refine ⟨1112290497195131052312935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2966107992520349472834493 1112290497195131052312935)
                      ·
                        rfl

theorem cell23_2166178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2166178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166178 prefixEnd_2166178 := by exact prefixLift 2166178
  have htrace : WordTrace (prefixWord ++ tailWord_2166178) baseStart_2166178 baseEnd_2166178 := by
    simpa [prefixWord, tailWord_2166178, baseEnd_2166178] using wordTrace_append hprefix tailTrace_2166178
  have hstable : (prefixWord ++ tailWord_2166178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166178).length < 2 ^ (prefixWord ++ tailWord_2166178).sum := by decide
  have hdescent : baseEnd_2166178 < baseStart_2166178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166207 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 3, 6]
def baseStart_2166207 : Nat := 118140960795 + 2166207 * 2 ^ 59
def prefixEnd_2166207 : Nat := 4983230072969 + 3 ^ 40 * 2166207 * 2
def baseEnd_2166207 : Nat := 370768462711370479616767

theorem tailTrace_2166207 : CollatzResearch.WordTrace tailWord_2166207 prefixEnd_2166207 370768462711370479616767 := by
  unfold tailWord_2166207
  simp only [CollatzResearch.WordTrace]
  refine ⟨79008060063209472546792875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52672040042139648364528583 79008060063209472546792875)
  ·
    refine ⟨118512090094814208820189313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79008060063209472546792875 118512090094814208820189313)
    ·
      refine ⟨88884067571110656615141985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118512090094814208820189313 88884067571110656615141985)
      ·
        refine ⟨66663050678332992461356489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88884067571110656615141985 66663050678332992461356489)
        ·
          refine ⟨49997288008749744346017367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66663050678332992461356489 49997288008749744346017367)
          ·
            refine ⟨74995932013124616519026051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49997288008749744346017367 74995932013124616519026051)
            ·
              refine ⟨112493898019686924778539077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74995932013124616519026051 112493898019686924778539077)
              ·
                refine ⟨21092605878691298395976077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112493898019686924778539077 21092605878691298395976077)
                ·
                  refine ⟨7909727204509236898491029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21092605878691298395976077 7909727204509236898491029)
                  ·
                    refine ⟨370768462711370479616767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7909727204509236898491029 370768462711370479616767)
                    ·
                      rfl

theorem cell23_2166207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_2166207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166207 prefixEnd_2166207 := by exact prefixLift 2166207
  have htrace : WordTrace (prefixWord ++ tailWord_2166207) baseStart_2166207 baseEnd_2166207 := by
    simpa [prefixWord, tailWord_2166207, baseEnd_2166207] using wordTrace_append hprefix tailTrace_2166207
  have hstable : (prefixWord ++ tailWord_2166207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166207).length < 2 ^ (prefixWord ++ tailWord_2166207).sum := by decide
  have hdescent : baseEnd_2166207 < baseStart_2166207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166208 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 1, 1, 3]
def baseStart_2166208 : Nat := 118140960795 + 2166208 * 2 ^ 59
def prefixEnd_2166208 : Nat := 4983230072969 + 3 ^ 40 * 2166208 * 2
def baseEnd_2166208 : Nat := 1112305901614765934937797

theorem tailTrace_2166208 : CollatzResearch.WordTrace tailWord_2166208 prefixEnd_2166208 1112305901614765934937797 := by
  unfold tailWord_2166208
  simp only [CollatzResearch.WordTrace]
  refine ⟨39504048268102924858789639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52672064357470566478386185 39504048268102924858789639)
  ·
    refine ⟨59256072402154387288184459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39504048268102924858789639 59256072402154387288184459)
    ·
      refine ⟨88884108603231580932276689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59256072402154387288184459 88884108603231580932276689)
      ·
        refine ⟨66663081452423685699207517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88884108603231580932276689 66663081452423685699207517)
        ·
          refine ⟨24998655544658882137202819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66663081452423685699207517 24998655544658882137202819)
          ·
            refine ⟨37497983316988323205804229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24998655544658882137202819 37497983316988323205804229)
            ·
              refine ⟨7030871871935310601088293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37497983316988323205804229 7030871871935310601088293)
              ·
                refine ⟨1318288475987870737704055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7030871871935310601088293 1318288475987870737704055)
                ·
                  refine ⟨1977432713981806106556083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318288475987870737704055 1977432713981806106556083)
                  ·
                    refine ⟨2966149070972709159834125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1977432713981806106556083 2966149070972709159834125)
                    ·
                      refine ⟨1112305901614765934937797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2966149070972709159834125 1112305901614765934937797)
                      ·
                        rfl

theorem cell23_2166208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_2166208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166208 prefixEnd_2166208 := by exact prefixLift 2166208
  have htrace : WordTrace (prefixWord ++ tailWord_2166208) baseStart_2166208 baseEnd_2166208 := by
    simpa [prefixWord, tailWord_2166208, baseEnd_2166208] using wordTrace_append hprefix tailTrace_2166208
  have hstable : (prefixWord ++ tailWord_2166208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166208).length < 2 ^ (prefixWord ++ tailWord_2166208).sum := by decide
  have hdescent : baseEnd_2166208 < baseStart_2166208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166228 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_2166228 : Nat := 118140960795 + 2166228 * 2 ^ 59
def prefixEnd_2166228 : Nat := 4983230072969 + 3 ^ 40 * 2166228 * 2
def baseEnd_2166228 : Nat := 370772057075951952229235

theorem tailTrace_2166228 : CollatzResearch.WordTrace tailWord_2166228 prefixEnd_2166228 370772057075951952229235 := by
  unfold tailWord_2166228
  simp only [CollatzResearch.WordTrace]
  refine ⟨39504412998066696566653669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52672550664088928755538225 39504412998066696566653669)
  ·
    refine ⟨7407077437137505606247563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39504412998066696566653669 7407077437137505606247563)
    ·
      refine ⟨11110616155706258409371345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7407077437137505606247563 11110616155706258409371345)
      ·
        refine ⟨8332962116779693807028509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11110616155706258409371345 8332962116779693807028509)
        ·
          refine ⟨3124860793792385177635691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8332962116779693807028509 3124860793792385177635691)
          ·
            refine ⟨4687291190688577766453537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124860793792385177635691 4687291190688577766453537)
            ·
              refine ⟨3515468393016433324840153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4687291190688577766453537 3515468393016433324840153)
              ·
                refine ⟨2636601294762324993630115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3515468393016433324840153 2636601294762324993630115)
                ·
                  refine ⟨3954901942143487490445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636601294762324993630115 3954901942143487490445173)
                  ·
                    refine ⟨370772057075951952229235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3954901942143487490445173 370772057075951952229235)
                    ·
                      rfl

theorem cell23_2166228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_2166228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166228 prefixEnd_2166228 := by exact prefixLift 2166228
  have htrace : WordTrace (prefixWord ++ tailWord_2166228) baseStart_2166228 baseEnd_2166228 := by
    simpa [prefixWord, tailWord_2166228, baseEnd_2166228] using wordTrace_append hprefix tailTrace_2166228
  have hstable : (prefixWord ++ tailWord_2166228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166228).length < 2 ^ (prefixWord ++ tailWord_2166228).sum := by decide
  have hdescent : baseEnd_2166228 < baseStart_2166228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166244 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_2166244 : Nat := 118140960795 + 2166244 * 2 ^ 59
def prefixEnd_2166244 : Nat := 4983230072969 + 3 ^ 40 * 2166244 * 2
def baseEnd_2166244 : Nat := 1112324386918327794087631

theorem tailTrace_2166244 : CollatzResearch.WordTrace tailWord_2166244 prefixEnd_2166244 1112324386918327794087631 := by
  unfold tailWord_2166244
  simp only [CollatzResearch.WordTrace]
  refine ⟨39504704782037713932944893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52672939709383618577259857 39504704782037713932944893)
  ·
    refine ⟨14814264293264142724854335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39504704782037713932944893 14814264293264142724854335)
    ·
      refine ⟨22221396439896214087281503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14814264293264142724854335 22221396439896214087281503)
      ·
        refine ⟨33332094659844321130922255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22221396439896214087281503 33332094659844321130922255)
        ·
          refine ⟨49998141989766481696383383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33332094659844321130922255 49998141989766481696383383)
          ·
            refine ⟨74997212984649722544575075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49998141989766481696383383 74997212984649722544575075)
            ·
              refine ⟨112495819476974583816862613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74997212984649722544575075 112495819476974583816862613)
              ·
                refine ⟨5273241537983183616415435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112495819476974583816862613 5273241537983183616415435)
                ·
                  refine ⟨7909862306974775424623153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273241537983183616415435 7909862306974775424623153)
                  ·
                    refine ⟨5932396730231081568467365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7909862306974775424623153 5932396730231081568467365)
                    ·
                      refine ⟨1112324386918327794087631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5932396730231081568467365 1112324386918327794087631)
                      ·
                        rfl

theorem cell23_2166244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_2166244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166244 prefixEnd_2166244 := by exact prefixLift 2166244
  have htrace : WordTrace (prefixWord ++ tailWord_2166244) baseStart_2166244 baseEnd_2166244 := by
    simpa [prefixWord, tailWord_2166244, baseEnd_2166244] using wordTrace_append hprefix tailTrace_2166244
  have hstable : (prefixWord ++ tailWord_2166244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166244).length < 2 ^ (prefixWord ++ tailWord_2166244).sum := by decide
  have hdescent : baseEnd_2166244 < baseStart_2166244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166261 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2166261 : Nat := 118140960795 + 2166261 * 2 ^ 59
def prefixEnd_2166261 : Nat := 4983230072969 + 3 ^ 40 * 2166261 * 2
def baseEnd_2166261 : Nat := 1112333116089454227575053

theorem tailTrace_2166261 : CollatzResearch.WordTrace tailWord_2166261 prefixEnd_2166261 1112333116089454227575053 := by
  unfold tailWord_2166261
  simp only [CollatzResearch.WordTrace]
  refine ⟨79010029605013839769258637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52673353070009226512839091 79010029605013839769258637)
  ·
    refine ⟨29628761101880189913471989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79010029605013839769258637 29628761101880189913471989)
    ·
      refine ⟨2777696353301267804387999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29628761101880189913471989 2777696353301267804387999)
      ·
        refine ⟨4166544529951901706581999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2777696353301267804387999 4166544529951901706581999)
        ·
          refine ⟨6249816794927852559872999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166544529951901706581999 6249816794927852559872999)
          ·
            refine ⟨9374725192391778839809499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6249816794927852559872999 9374725192391778839809499)
            ·
              refine ⟨14062087788587668259714249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9374725192391778839809499 14062087788587668259714249)
              ·
                refine ⟨10546565841440751194785687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14062087788587668259714249 10546565841440751194785687)
                ·
                  refine ⟨15819848762161126792178531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10546565841440751194785687 15819848762161126792178531)
                  ·
                    refine ⟨23729773143241690188267797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15819848762161126792178531 23729773143241690188267797)
                    ·
                      refine ⟨1112333116089454227575053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23729773143241690188267797 1112333116089454227575053)
                      ·
                        rfl

theorem cell23_2166261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2166261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166261 prefixEnd_2166261 := by exact prefixLift 2166261
  have htrace : WordTrace (prefixWord ++ tailWord_2166261) baseStart_2166261 baseEnd_2166261 := by
    simpa [prefixWord, tailWord_2166261, baseEnd_2166261] using wordTrace_append hprefix tailTrace_2166261
  have hstable : (prefixWord ++ tailWord_2166261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166261).length < 2 ^ (prefixWord ++ tailWord_2166261).sum := by decide
  have hdescent : baseEnd_2166261 < baseStart_2166261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166267 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 9]
def baseStart_2166267 : Nat := 118140960795 + 2166267 * 2 ^ 59
def prefixEnd_2166267 : Nat := 4983230072969 + 3 ^ 40 * 2166267 * 2
def baseEnd_2166267 : Nat := 370778732324460401366675

theorem tailTrace_2166267 : CollatzResearch.WordTrace tailWord_2166267 prefixEnd_2166267 370778732324460401366675 := by
  unfold tailWord_2166267
  simp only [CollatzResearch.WordTrace]
  refine ⟨79010248442992102793977055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52673498961994735195984703 79010248442992102793977055)
  ·
    refine ⟨118515372664488154190965583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79010248442992102793977055 118515372664488154190965583)
    ·
      refine ⟨177773058996732231286448375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118515372664488154190965583 177773058996732231286448375)
      ·
        refine ⟨266659588495098346929672563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177773058996732231286448375 266659588495098346929672563)
        ·
          refine ⟨399989382742647520394508845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266659588495098346929672563 399989382742647520394508845)
          ·
            refine ⟨149996018528492820147940817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 399989382742647520394508845 149996018528492820147940817)
            ·
              refine ⟨112497013896369615110955613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149996018528492820147940817 112497013896369615110955613)
              ·
                refine ⟨42186380211138605666608355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112497013896369615110955613 42186380211138605666608355)
                ·
                  refine ⟨63279570316707908499912533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42186380211138605666608355 63279570316707908499912533)
                  ·
                    refine ⟨370778732324460401366675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63279570316707908499912533 370778732324460401366675)
                    ·
                      rfl

theorem cell23_2166267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_2166267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166267 prefixEnd_2166267 := by exact prefixLift 2166267
  have htrace : WordTrace (prefixWord ++ tailWord_2166267) baseStart_2166267 baseEnd_2166267 := by
    simpa [prefixWord, tailWord_2166267, baseEnd_2166267] using wordTrace_append hprefix tailTrace_2166267
  have hstable : (prefixWord ++ tailWord_2166267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166267).length < 2 ^ (prefixWord ++ tailWord_2166267).sum := by decide
  have hdescent : baseEnd_2166267 < baseStart_2166267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166321 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 5, 4, 2]
def baseStart_2166321 : Nat := 118140960795 + 2166321 * 2 ^ 59
def prefixEnd_2166321 : Nat := 4983230072969 + 3 ^ 40 * 2166321 * 2
def baseEnd_2166321 : Nat := 1112363924928723992824777

theorem tailTrace_2166321 : CollatzResearch.WordTrace tailWord_2166321 prefixEnd_2166321 1112363924928723992824777 := by
  unfold tailWord_2166321
  simp only [CollatzResearch.WordTrace]
  refine ⟨79012217984796470016442817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52674811989864313344295211 79012217984796470016442817)
  ·
    refine ⟨59259163488597352512332113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79012217984796470016442817 59259163488597352512332113)
    ·
      refine ⟨44444372616448014384249085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59259163488597352512332113 44444372616448014384249085)
      ·
        refine ⟨16666639731168005394093407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44444372616448014384249085 16666639731168005394093407)
        ·
          refine ⟨24999959596752008091140111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16666639731168005394093407 24999959596752008091140111)
          ·
            refine ⟨37499939395128012136710167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24999959596752008091140111 37499939395128012136710167)
            ·
              refine ⟨56249909092692018205065251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37499939395128012136710167 56249909092692018205065251)
              ·
                refine ⟨84374863639038027307597877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56249909092692018205065251 84374863639038027307597877)
                ·
                  refine ⟨7910143466159815060087301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84374863639038027307597877 7910143466159815060087301)
                  ·
                    refine ⟨1483151899904965323766369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7910143466159815060087301 1483151899904965323766369)
                    ·
                      refine ⟨1112363924928723992824777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483151899904965323766369 1112363924928723992824777)
                      ·
                        rfl

theorem cell23_2166321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_2166321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166321 prefixEnd_2166321 := by exact prefixLift 2166321
  have htrace : WordTrace (prefixWord ++ tailWord_2166321) baseStart_2166321 baseEnd_2166321 := by
    simpa [prefixWord, tailWord_2166321, baseEnd_2166321] using wordTrace_append hprefix tailTrace_2166321
  have hstable : (prefixWord ++ tailWord_2166321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166321).length < 2 ^ (prefixWord ++ tailWord_2166321).sum := by decide
  have hdescent : baseEnd_2166321 < baseStart_2166321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166371 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2166371 : Nat := 118140960795 + 2166371 * 2 ^ 59
def prefixEnd_2166371 : Nat := 4983230072969 + 3 ^ 40 * 2166371 * 2
def baseEnd_2166371 : Nat := 1112389598961448797199547

theorem tailTrace_2166371 : CollatzResearch.WordTrace tailWord_2166371 prefixEnd_2166371 1112389598961448797199547 := by
  unfold tailWord_2166371
  simp only [CollatzResearch.WordTrace]
  refine ⟨79014041634615328555762967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52676027756410219037175311 79014041634615328555762967)
  ·
    refine ⟨118521062451922992833644451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79014041634615328555762967 118521062451922992833644451)
    ·
      refine ⟨177781593677884489250466677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118521062451922992833644451 177781593677884489250466677)
      ·
        refine ⟨16667024407301670867231251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177781593677884489250466677 16667024407301670867231251)
        ·
          refine ⟨25000536610952506300846877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16667024407301670867231251 25000536610952506300846877)
          ·
            refine ⟨9375201229107189862817579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25000536610952506300846877 9375201229107189862817579)
            ·
              refine ⟨14062801843660784794226369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9375201229107189862817579 14062801843660784794226369)
              ·
                refine ⟨10547101382745588595669777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14062801843660784794226369 10547101382745588595669777)
                ·
                  refine ⟨7910326037059191446752333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10547101382745588595669777 7910326037059191446752333)
                  ·
                    refine ⟨2966372263897196792532125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7910326037059191446752333 2966372263897196792532125)
                    ·
                      refine ⟨1112389598961448797199547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2966372263897196792532125 1112389598961448797199547)
                      ·
                        rfl

theorem cell23_2166371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2166371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166371 prefixEnd_2166371 := by exact prefixLift 2166371
  have htrace : WordTrace (prefixWord ++ tailWord_2166371) baseStart_2166371 baseEnd_2166371 := by
    simpa [prefixWord, tailWord_2166371, baseEnd_2166371] using wordTrace_append hprefix tailTrace_2166371
  have hstable : (prefixWord ++ tailWord_2166371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166371).length < 2 ^ (prefixWord ++ tailWord_2166371).sum := by decide
  have hdescent : baseEnd_2166371 < baseStart_2166371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166372 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_2166372 : Nat := 118140960795 + 2166372 * 2 ^ 59
def prefixEnd_2166372 : Nat := 4983230072969 + 3 ^ 40 * 2166372 * 2
def baseEnd_2166372 : Nat := 1112390112442103293287043

theorem tailTrace_2166372 : CollatzResearch.WordTrace tailWord_2166372 prefixEnd_2166372 1112390112442103293287043 := by
  unfold tailWord_2166372
  simp only [CollatzResearch.WordTrace]
  refine ⟨39507039053805852863274685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52676052071741137151032913 39507039053805852863274685)
  ·
    refine ⟨14815139645177194823728007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39507039053805852863274685 14815139645177194823728007)
    ·
      refine ⟨22222709467765792235592011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14815139645177194823728007 22222709467765792235592011)
      ·
        refine ⟨33334064201648688353388017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22222709467765792235592011 33334064201648688353388017)
        ·
          refine ⟨25000548151236516265041013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33334064201648688353388017 25000548151236516265041013)
          ·
            refine ⟨2343801389178423399847595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25000548151236516265041013 2343801389178423399847595)
            ·
              refine ⟨3515702083767635099771393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343801389178423399847595 3515702083767635099771393)
              ·
                refine ⟨2636776562825726324828545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3515702083767635099771393 2636776562825726324828545)
                ·
                  refine ⟨1977582422119294743621409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636776562825726324828545 1977582422119294743621409)
                  ·
                    refine ⟨1483186816589471057716057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1977582422119294743621409 1483186816589471057716057)
                    ·
                      refine ⟨1112390112442103293287043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483186816589471057716057 1112390112442103293287043)
                      ·
                        rfl

theorem cell23_2166372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_2166372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166372 prefixEnd_2166372 := by exact prefixLift 2166372
  have htrace : WordTrace (prefixWord ++ tailWord_2166372) baseStart_2166372 baseEnd_2166372 := by
    simpa [prefixWord, tailWord_2166372, baseEnd_2166372] using wordTrace_append hprefix tailTrace_2166372
  have hstable : (prefixWord ++ tailWord_2166372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166372).length < 2 ^ (prefixWord ++ tailWord_2166372).sum := by decide
  have hdescent : baseEnd_2166372 < baseStart_2166372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166378 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_2166378 : Nat := 118140960795 + 2166378 * 2 ^ 59
def prefixEnd_2166378 : Nat := 4983230072969 + 3 ^ 40 * 2166378 * 2
def baseEnd_2166378 : Nat := 123599243702892252201335

theorem tailTrace_2166378 : CollatzResearch.WordTrace tailWord_2166378 prefixEnd_2166378 123599243702892252201335 := by
  unfold tailWord_2166378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19753574236397492187816947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52676197963726645834178525 19753574236397492187816947)
  ·
    refine ⟨29630361354596238281725421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19753574236397492187816947 29630361354596238281725421)
    ·
      refine ⟨11111385507973589355647033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29630361354596238281725421 11111385507973589355647033)
      ·
        refine ⟨8333539130980192016735275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11111385507973589355647033 8333539130980192016735275)
        ·
          refine ⟨12500308696470288025102913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8333539130980192016735275 12500308696470288025102913)
          ·
            refine ⟨9375231522352716018827185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12500308696470288025102913 9375231522352716018827185)
            ·
              refine ⟨7031423641764537014120389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9375231522352716018827185 7031423641764537014120389)
              ·
                refine ⟨1318391932830850690147573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7031423641764537014120389 1318391932830850690147573)
                ·
                  refine ⟨123599243702892252201335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318391932830850690147573 123599243702892252201335)
                  ·
                    rfl

theorem cell23_2166378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_2166378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166378 prefixEnd_2166378 := by exact prefixLift 2166378
  have htrace : WordTrace (prefixWord ++ tailWord_2166378) baseStart_2166378 baseEnd_2166378 := by
    simpa [prefixWord, tailWord_2166378, baseEnd_2166378] using wordTrace_append hprefix tailTrace_2166378
  have hstable : (prefixWord ++ tailWord_2166378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166378).length < 2 ^ (prefixWord ++ tailWord_2166378).sum := by decide
  have hdescent : baseEnd_2166378 < baseStart_2166378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166389 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2166389 : Nat := 118140960795 + 2166389 * 2 ^ 59
def prefixEnd_2166389 : Nat := 4983230072969 + 3 ^ 40 * 2166389 * 2
def baseEnd_2166389 : Nat := 1112398841613229726774465

theorem tailTrace_2166389 : CollatzResearch.WordTrace tailWord_2166389 prefixEnd_2166389 1112398841613229726774465 := by
  unfold tailWord_2166389
  simp only [CollatzResearch.WordTrace]
  refine ⟨79014698148550117629918221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52676465432366745086612147 79014698148550117629918221)
  ·
    refine ⟨29630511805706294111219333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79014698148550117629918221 29630511805706294111219333)
    ·
      refine ⟨5555720963569930145853625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29630511805706294111219333 5555720963569930145853625)
      ·
        refine ⟨4166790722677447609390219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5555720963569930145853625 4166790722677447609390219)
        ·
          refine ⟨6250186084016171414085329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166790722677447609390219 6250186084016171414085329)
          ·
            refine ⟨4687639563012128560563997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6250186084016171414085329 4687639563012128560563997)
            ·
              refine ⟨1757864836129548210211499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4687639563012128560563997 1757864836129548210211499)
              ·
                refine ⟨2636797254194322315317249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757864836129548210211499 2636797254194322315317249)
                ·
                  refine ⟨1977597940645741736487937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636797254194322315317249 1977597940645741736487937)
                  ·
                    refine ⟨1483198455484306302365953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1977597940645741736487937 1483198455484306302365953)
                    ·
                      refine ⟨1112398841613229726774465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483198455484306302365953 1112398841613229726774465)
                      ·
                        rfl

theorem cell23_2166389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2166389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166389 prefixEnd_2166389 := by exact prefixLift 2166389
  have htrace : WordTrace (prefixWord ++ tailWord_2166389) baseStart_2166389 baseEnd_2166389 := by
    simpa [prefixWord, tailWord_2166389, baseEnd_2166389] using wordTrace_append hprefix tailTrace_2166389
  have hstable : (prefixWord ++ tailWord_2166389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166389).length < 2 ^ (prefixWord ++ tailWord_2166389).sum := by decide
  have hdescent : baseEnd_2166389 < baseStart_2166389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166411 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 4]
def baseStart_2166411 : Nat := 118140960795 + 2166411 * 2 ^ 59
def prefixEnd_2166411 : Nat := 4983230072969 + 3 ^ 40 * 2166411 * 2
def baseEnd_2166411 : Nat := 1112410138187628640699363

theorem tailTrace_2166411 : CollatzResearch.WordTrace tailWord_2166411 prefixEnd_2166411 1112410138187628640699363 := by
  unfold tailWord_2166411
  simp only [CollatzResearch.WordTrace]
  refine ⟨79015500554470415387219087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52677000369646943591479391 79015500554470415387219087)
  ·
    refine ⟨118523250831705623080828631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79015500554470415387219087 118523250831705623080828631)
    ·
      refine ⟨177784876247558434621242947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118523250831705623080828631 177784876247558434621242947)
      ·
        refine ⟨266677314371337651931864421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177784876247558434621242947 266677314371337651931864421)
        ·
          refine ⟨50001996444625809737224579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266677314371337651931864421 50001996444625809737224579)
          ·
            refine ⟨75002994666938714605836869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50001996444625809737224579 75002994666938714605836869)
            ·
              refine ⟨14063061500051008988594413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75002994666938714605836869 14063061500051008988594413)
              ·
                refine ⟨5273648062519128370722905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14063061500051008988594413 5273648062519128370722905)
                ·
                  refine ⟨3955236046889346278042179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5273648062519128370722905 3955236046889346278042179)
                  ·
                    refine ⟨5932854070334019417063269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3955236046889346278042179 5932854070334019417063269)
                    ·
                      refine ⟨1112410138187628640699363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5932854070334019417063269 1112410138187628640699363)
                      ·
                        rfl

theorem cell23_2166411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 4].length) (baseStart_2166411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166411 prefixEnd_2166411 := by exact prefixLift 2166411
  have htrace : WordTrace (prefixWord ++ tailWord_2166411) baseStart_2166411 baseEnd_2166411 := by
    simpa [prefixWord, tailWord_2166411, baseEnd_2166411] using wordTrace_append hprefix tailTrace_2166411
  have hstable : (prefixWord ++ tailWord_2166411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166411).length < 2 ^ (prefixWord ++ tailWord_2166411).sum := by decide
  have hdescent : baseEnd_2166411 < baseStart_2166411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166421 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_2166421 : Nat := 118140960795 + 2166421 * 2 ^ 59
def prefixEnd_2166421 : Nat := 4983230072969 + 3 ^ 40 * 2166421 * 2
def baseEnd_2166421 : Nat := 370805090998057867191439

theorem tailTrace_2166421 : CollatzResearch.WordTrace tailWord_2166421 prefixEnd_2166421 370805090998057867191439 := by
  unfold tailWord_2166421
  simp only [CollatzResearch.WordTrace]
  refine ⟨79015865284434187095083117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52677243522956124730055411 79015865284434187095083117)
  ·
    refine ⟨29630949481662820160656169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79015865284434187095083117 29630949481662820160656169)
    ·
      refine ⟨22223212111247115120492127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29630949481662820160656169 22223212111247115120492127)
      ·
        refine ⟨33334818166870672680738191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22223212111247115120492127 33334818166870672680738191)
        ·
          refine ⟨50002227250306009021107287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33334818166870672680738191 50002227250306009021107287)
          ·
            refine ⟨75003340875459013531660931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50002227250306009021107287 75003340875459013531660931)
            ·
              refine ⟨112505011313188520297491397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75003340875459013531660931 112505011313188520297491397)
              ·
                refine ⟨21094689621222847555779637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112505011313188520297491397 21094689621222847555779637)
                ·
                  refine ⟨1977627151989641958354341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21094689621222847555779637 1977627151989641958354341)
                  ·
                    refine ⟨370805090998057867191439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1977627151989641958354341 370805090998057867191439)
                    ·
                      rfl

theorem cell23_2166421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_2166421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166421 prefixEnd_2166421 := by exact prefixLift 2166421
  have htrace : WordTrace (prefixWord ++ tailWord_2166421) baseStart_2166421 baseEnd_2166421 := by
    simpa [prefixWord, tailWord_2166421, baseEnd_2166421] using wordTrace_append hprefix tailTrace_2166421
  have hstable : (prefixWord ++ tailWord_2166421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166421).length < 2 ^ (prefixWord ++ tailWord_2166421).sum := by decide
  have hdescent : baseEnd_2166421 < baseStart_2166421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166440 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2166440 : Nat := 118140960795 + 2166440 * 2 ^ 59
def prefixEnd_2166440 : Nat := 4983230072969 + 3 ^ 40 * 2166440 * 2
def baseEnd_2166440 : Nat := 1112425029126609027236731

theorem tailTrace_2166440 : CollatzResearch.WordTrace tailWord_2166440 prefixEnd_2166440 1112425029126609027236731 := by
  unfold tailWord_2166440
  simp only [CollatzResearch.WordTrace]
  refine ⟨39508279135682676670012387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52677705514243568893349849 39508279135682676670012387)
  ·
    refine ⟨59262418703524015005018581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39508279135682676670012387 59262418703524015005018581)
    ·
      refine ⟨1388962938363844101680123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 59262418703524015005018581 1388962938363844101680123)
      ·
        refine ⟨2083444407545766152520185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388962938363844101680123 2083444407545766152520185)
        ·
          refine ⟨1562583305659324614390139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083444407545766152520185 1562583305659324614390139)
          ·
            refine ⟨2343874958488986921585209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562583305659324614390139 2343874958488986921585209)
            ·
              refine ⟨1757906218866740191188907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343874958488986921585209 1757906218866740191188907)
              ·
                refine ⟨2636859328300110286783361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757906218866740191188907 2636859328300110286783361)
                ·
                  refine ⟨1977644496225082715087521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636859328300110286783361 1977644496225082715087521)
                  ·
                    refine ⟨1483233372168812036315641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1977644496225082715087521 1483233372168812036315641)
                    ·
                      refine ⟨1112425029126609027236731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483233372168812036315641 1112425029126609027236731)
                      ·
                        rfl

theorem cell23_2166440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2166440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166440 prefixEnd_2166440 := by exact prefixLift 2166440
  have htrace : WordTrace (prefixWord ++ tailWord_2166440) baseStart_2166440 baseEnd_2166440 := by
    simpa [prefixWord, tailWord_2166440, baseEnd_2166440] using wordTrace_append hprefix tailTrace_2166440
  have hstable : (prefixWord ++ tailWord_2166440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166440).length < 2 ^ (prefixWord ++ tailWord_2166440).sum := by decide
  have hdescent : baseEnd_2166440 < baseStart_2166440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166451 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 6]
def baseStart_2166451 : Nat := 118140960795 + 2166451 * 2 ^ 59
def prefixEnd_2166451 : Nat := 4983230072969 + 3 ^ 40 * 2166451 * 2
def baseEnd_2166451 : Nat := 123603408601534276022131

theorem tailTrace_2166451 : CollatzResearch.WordTrace tailWord_2166451 prefixEnd_2166451 123603408601534276022131 := by
  unfold tailWord_2166451
  simp only [CollatzResearch.WordTrace]
  refine ⟨79016959474325502218675207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52677972982883668145783471 79016959474325502218675207)
  ·
    refine ⟨118525439211488253328012811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79016959474325502218675207 118525439211488253328012811)
    ·
      refine ⟨177788158817232379992019217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118525439211488253328012811 177788158817232379992019217)
      ·
        refine ⟨133341119112924284994014413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177788158817232379992019217 133341119112924284994014413)
        ·
          refine ⟨50002919667346606872755405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133341119112924284994014413 50002919667346606872755405)
          ·
            refine ⟨18751094875254977577283277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50002919667346606872755405 18751094875254977577283277)
            ·
              refine ⟨7031660578220616591481229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18751094875254977577283277 7031660578220616591481229)
              ·
                refine ⟨2636872716832731221805461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7031660578220616591481229 2636872716832731221805461)
                ·
                  refine ⟨123603408601534276022131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2636872716832731221805461 123603408601534276022131)
                  ·
                    rfl

theorem cell23_2166451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 6].length) (baseStart_2166451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166451 prefixEnd_2166451 := by exact prefixLift 2166451
  have htrace : WordTrace (prefixWord ++ tailWord_2166451) baseStart_2166451 baseEnd_2166451 := by
    simpa [prefixWord, tailWord_2166451, baseEnd_2166451] using wordTrace_append hprefix tailTrace_2166451
  have hstable : (prefixWord ++ tailWord_2166451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166451).length < 2 ^ (prefixWord ++ tailWord_2166451).sum := by decide
  have hdescent : baseEnd_2166451 < baseStart_2166451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166532 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_2166532 : Nat := 118140960795 + 2166532 * 2 ^ 59
def prefixEnd_2166532 : Nat := 4983230072969 + 3 ^ 40 * 2166532 * 2
def baseEnd_2166532 : Nat := 370824089782274222428769

theorem tailTrace_2166532 : CollatzResearch.WordTrace tailWord_2166532 prefixEnd_2166532 370824089782274222428769 := by
  unfold tailWord_2166532
  simp only [CollatzResearch.WordTrace]
  refine ⟨39509956893516026526186925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52679942524688035368249233 39509956893516026526186925)
  ·
    refine ⟨14816233835068509947320097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39509956893516026526186925 14816233835068509947320097)
    ·
      refine ⟨11112175376301382460490073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14816233835068509947320097 11112175376301382460490073)
      ·
        refine ⟨8334131532226036845367555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11112175376301382460490073 8334131532226036845367555)
        ·
          refine ⟨12501197298339055268051333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334131532226036845367555 12501197298339055268051333)
          ·
            refine ⟨2343974493438572862759625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12501197298339055268051333 2343974493438572862759625)
            ·
              refine ⟨1757980870078929647069719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343974493438572862759625 1757980870078929647069719)
              ·
                refine ⟨2636971305118394470604579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757980870078929647069719 2636971305118394470604579)
                ·
                  refine ⟨3955456957677591705906869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636971305118394470604579 3955456957677591705906869)
                  ·
                    refine ⟨370824089782274222428769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3955456957677591705906869 370824089782274222428769)
                    ·
                      rfl

theorem cell23_2166532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_2166532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166532 prefixEnd_2166532 := by exact prefixLift 2166532
  have htrace : WordTrace (prefixWord ++ tailWord_2166532) baseStart_2166532 baseEnd_2166532 := by
    simpa [prefixWord, tailWord_2166532, baseEnd_2166532] using wordTrace_append hprefix tailTrace_2166532
  have hstable : (prefixWord ++ tailWord_2166532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166532).length < 2 ^ (prefixWord ++ tailWord_2166532).sum := by decide
  have hdescent : baseEnd_2166532 < baseStart_2166532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166562 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2166562 : Nat := 118140960795 + 2166562 * 2 ^ 59
def prefixEnd_2166562 : Nat := 4983230072969 + 3 ^ 40 * 2166562 * 2
def baseEnd_2166562 : Nat := 370829224588819183303723

theorem tailTrace_2166562 : CollatzResearch.WordTrace tailWord_2166562 prefixEnd_2166562 370829224588819183303723 := by
  unfold tailWord_2166562
  simp only [CollatzResearch.WordTrace]
  refine ⟨19755251994230842043991485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52680671984615578783977293 19755251994230842043991485)
  ·
    refine ⟨7408219497836565766496807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19755251994230842043991485 7408219497836565766496807)
    ·
      refine ⟨11112329246754848649745211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408219497836565766496807 11112329246754848649745211)
      ·
        refine ⟨16668493870132272974617817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11112329246754848649745211 16668493870132272974617817)
        ·
          refine ⟨12501370402599204730963363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16668493870132272974617817 12501370402599204730963363)
          ·
            refine ⟨18752055603898807096445045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12501370402599204730963363 18752055603898807096445045)
            ·
              refine ⟨1758005212865513165291723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18752055603898807096445045 1758005212865513165291723)
              ·
                refine ⟨2637007819298269747937585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758005212865513165291723 2637007819298269747937585)
                ·
                  refine ⟨1977755864473702310953189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637007819298269747937585 1977755864473702310953189)
                  ·
                    refine ⟨370829224588819183303723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1977755864473702310953189 370829224588819183303723)
                    ·
                      rfl

theorem cell23_2166562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2166562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166562 prefixEnd_2166562 := by exact prefixLift 2166562
  have htrace : WordTrace (prefixWord ++ tailWord_2166562) baseStart_2166562 baseEnd_2166562 := by
    simpa [prefixWord, tailWord_2166562, baseEnd_2166562] using wordTrace_append hprefix tailTrace_2166562
  have hstable : (prefixWord ++ tailWord_2166562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166562).length < 2 ^ (prefixWord ++ tailWord_2166562).sum := by decide
  have hdescent : baseEnd_2166562 < baseStart_2166562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166565 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_2166565 : Nat := 118140960795 + 2166565 * 2 ^ 59
def prefixEnd_2166565 : Nat := 4983230072969 + 3 ^ 40 * 2166565 * 2
def baseEnd_2166565 : Nat := 1112489214208421038173655

theorem tailTrace_2166565 : CollatzResearch.WordTrace tailWord_2166565 prefixEnd_2166565 1112489214208421038173655 := by
  unfold tailWord_2166565
  simp only [CollatzResearch.WordTrace]
  refine ⟨79021117395912499688325149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52680744930608333125550099 79021117395912499688325149)
  ·
    refine ⟨29632919023467187383121931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79021117395912499688325149 29632919023467187383121931)
    ·
      refine ⟨44449378535200781074682897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29632919023467187383121931 44449378535200781074682897)
      ·
        refine ⟨33337033901400585806012173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44449378535200781074682897 33337033901400585806012173)
        ·
          refine ⟨12501387713025219677254565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33337033901400585806012173 12501387713025219677254565)
          ·
            refine ⟨2344010196192228689485231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12501387713025219677254565 2344010196192228689485231)
            ·
              refine ⟨3516015294288343034227847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344010196192228689485231 3516015294288343034227847)
              ·
                refine ⟨5274022941432514551341771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516015294288343034227847 5274022941432514551341771)
                ·
                  refine ⟨7911034412148771827012657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274022941432514551341771 7911034412148771827012657)
                  ·
                    refine ⟨5933275809111578870259493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7911034412148771827012657 5933275809111578870259493)
                    ·
                      refine ⟨1112489214208421038173655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5933275809111578870259493 1112489214208421038173655)
                      ·
                        rfl

theorem cell23_2166565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_2166565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166565 prefixEnd_2166565 := by exact prefixLift 2166565
  have htrace : WordTrace (prefixWord ++ tailWord_2166565) baseStart_2166565 baseEnd_2166565 := by
    simpa [prefixWord, tailWord_2166565, baseEnd_2166565] using wordTrace_append hprefix tailTrace_2166565
  have hstable : (prefixWord ++ tailWord_2166565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166565).length < 2 ^ (prefixWord ++ tailWord_2166565).sum := by decide
  have hdescent : baseEnd_2166565 < baseStart_2166565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166586 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2]
def baseStart_2166586 : Nat := 118140960795 + 2166586 * 2 ^ 59
def prefixEnd_2166586 : Nat := 4983230072969 + 3 ^ 40 * 2166586 * 2
def baseEnd_2166586 : Nat := 1112499997302165456011059

theorem tailTrace_2166586 : CollatzResearch.WordTrace tailWord_2166586 prefixEnd_2166586 1112499997302165456011059 := by
  unfold tailWord_2166586
  simp only [CollatzResearch.WordTrace]
  refine ⟨19755470832209105068709903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52681255552557613516559741 19755470832209105068709903)
  ·
    refine ⟨29633206248313657603064855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19755470832209105068709903 29633206248313657603064855)
    ·
      refine ⟨44449809372470486404597283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29633206248313657603064855 44449809372470486404597283)
      ·
        refine ⟨66674714058705729606895925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44449809372470486404597283 66674714058705729606895925)
        ·
          refine ⟨6250754443003662150646493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66674714058705729606895925 6250754443003662150646493)
          ·
            refine ⟨2344032916126373306492435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6250754443003662150646493 2344032916126373306492435)
            ·
              refine ⟨3516049374189559959738653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344032916126373306492435 3516049374189559959738653)
              ·
                refine ⟨1318518515321084984901995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3516049374189559959738653 1318518515321084984901995)
                ·
                  refine ⟨1977777772981627477352993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318518515321084984901995 1977777772981627477352993)
                  ·
                    refine ⟨1483333329736220608014745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1977777772981627477352993 1483333329736220608014745)
                    ·
                      refine ⟨1112499997302165456011059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483333329736220608014745 1112499997302165456011059)
                      ·
                        rfl

theorem cell23_2166586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_2166586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166586 prefixEnd_2166586 := by exact prefixLift 2166586
  have htrace : WordTrace (prefixWord ++ tailWord_2166586) baseStart_2166586 baseEnd_2166586 := by
    simpa [prefixWord, tailWord_2166586, baseEnd_2166586] using wordTrace_append hprefix tailTrace_2166586
  have hstable : (prefixWord ++ tailWord_2166586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166586).length < 2 ^ (prefixWord ++ tailWord_2166586).sum := by decide
  have hdescent : baseEnd_2166586 < baseStart_2166586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166625 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_2166625 : Nat := 118140960795 + 2166625 * 2 ^ 59
def prefixEnd_2166625 : Nat := 4983230072969 + 3 ^ 40 * 2166625 * 2
def baseEnd_2166625 : Nat := 1112520023047690803423379

theorem tailTrace_2166625 : CollatzResearch.WordTrace tailWord_2166625 prefixEnd_2166625 1112520023047690803423379 := by
  unfold tailWord_2166625
  simp only [CollatzResearch.WordTrace]
  refine ⟨79023305775695129935509329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52682203850463419957006219 79023305775695129935509329)
  ·
    refine ⟨59267479331771347451631997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79023305775695129935509329 59267479331771347451631997)
    ·
      refine ⟨22225304749414255294361999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59267479331771347451631997 22225304749414255294361999)
      ·
        refine ⟨33337957124121382941542999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22225304749414255294361999 33337957124121382941542999)
        ·
          refine ⟨50006935686182074412314499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33337957124121382941542999 50006935686182074412314499)
          ·
            refine ⟨75010403529273111618471749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50006935686182074412314499 75010403529273111618471749)
            ·
              refine ⟨14064450661738708428463453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75010403529273111618471749 14064450661738708428463453)
              ·
                refine ⟨5274168998152015660673795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14064450661738708428463453 5274168998152015660673795)
                ·
                  refine ⟨7911253497228023491010693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274168998152015660673795 7911253497228023491010693)
                  ·
                    refine ⟨1483360030730254404564505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7911253497228023491010693 1483360030730254404564505)
                    ·
                      refine ⟨1112520023047690803423379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483360030730254404564505 1112520023047690803423379)
                      ·
                        rfl

theorem cell23_2166625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_2166625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166625 prefixEnd_2166625 := by exact prefixLift 2166625
  have htrace : WordTrace (prefixWord ++ tailWord_2166625) baseStart_2166625 baseEnd_2166625 := by
    simpa [prefixWord, tailWord_2166625, baseEnd_2166625] using wordTrace_append hprefix tailTrace_2166625
  have hstable : (prefixWord ++ tailWord_2166625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166625).length < 2 ^ (prefixWord ++ tailWord_2166625).sum := by decide
  have hdescent : baseEnd_2166625 < baseStart_2166625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166659 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 2, 2, 2]
def baseStart_2166659 : Nat := 118140960795 + 2166659 * 2 ^ 59
def prefixEnd_2166659 : Nat := 4983230072969 + 3 ^ 40 * 2166659 * 2
def baseEnd_2166659 : Nat := 1112537481389943670398223

theorem tailTrace_2166659 : CollatzResearch.WordTrace tailWord_2166659 prefixEnd_2166659 1112537481389943670398223 := by
  unfold tailWord_2166659
  simp only [CollatzResearch.WordTrace]
  refine ⟨79024545857571953742247031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52683030571714635828164687 79024545857571953742247031)
  ·
    refine ⟨118536818786357930613370547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79024545857571953742247031 118536818786357930613370547)
    ·
      refine ⟨177805228179536895920055821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118536818786357930613370547 177805228179536895920055821)
      ·
        refine ⟨66676960567326335970020933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177805228179536895920055821 66676960567326335970020933)
        ·
          refine ⟨12501930106373687994378925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66676960567326335970020933 12501930106373687994378925)
          ·
            refine ⟨4688223789890132997892097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12501930106373687994378925 4688223789890132997892097)
            ·
              refine ⟨3516167842417599748419073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4688223789890132997892097 3516167842417599748419073)
              ·
                refine ⟨2637125881813199811314305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516167842417599748419073 2637125881813199811314305)
                ·
                  refine ⟨1977844411359899858485729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637125881813199811314305 1977844411359899858485729)
                  ·
                    refine ⟨1483383308519924893864297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1977844411359899858485729 1483383308519924893864297)
                    ·
                      refine ⟨1112537481389943670398223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483383308519924893864297 1112537481389943670398223)
                      ·
                        rfl

theorem cell23_2166659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_2166659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166659 prefixEnd_2166659 := by exact prefixLift 2166659
  have htrace : WordTrace (prefixWord ++ tailWord_2166659) baseStart_2166659 baseEnd_2166659 := by
    simpa [prefixWord, tailWord_2166659, baseEnd_2166659] using wordTrace_append hprefix tailTrace_2166659
  have hstable : (prefixWord ++ tailWord_2166659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166659).length < 2 ^ (prefixWord ++ tailWord_2166659).sum := by decide
  have hdescent : baseEnd_2166659 < baseStart_2166659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166665 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 5]
def baseStart_2166665 : Nat := 118140960795 + 2166665 * 2 ^ 59
def prefixEnd_2166665 : Nat := 4983230072969 + 3 ^ 40 * 2166665 * 2
def baseEnd_2166665 : Nat := 123615618030430071880355

theorem tailTrace_2166665 : CollatzResearch.WordTrace tailWord_2166665 prefixEnd_2166665 123615618030430071880355 := by
  unfold tailWord_2166665
  simp only [CollatzResearch.WordTrace]
  refine ⟨79024764695550216766965449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52683176463700144511310299 79024764695550216766965449)
  ·
    refine ⟨59268573521662662575224087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79024764695550216766965449 59268573521662662575224087)
    ·
      refine ⟨88902860282493993862836131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59268573521662662575224087 88902860282493993862836131)
      ·
        refine ⟨133354290423740990794254197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88902860282493993862836131 133354290423740990794254197)
        ·
          refine ⟨12501964727225717886961331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133354290423740990794254197 12501964727225717886961331)
          ·
            refine ⟨18752947090838576830441997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12501964727225717886961331 18752947090838576830441997)
            ·
              refine ⟨7032355159064466311415749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18752947090838576830441997 7032355159064466311415749)
              ·
                refine ⟨1318566592324587433390453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7032355159064466311415749 1318566592324587433390453)
                ·
                  refine ⟨123615618030430071880355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318566592324587433390453 123615618030430071880355)
                  ·
                    rfl

theorem cell23_2166665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 5].length) (baseStart_2166665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166665 prefixEnd_2166665 := by exact prefixLift 2166665
  have htrace : WordTrace (prefixWord ++ tailWord_2166665) baseStart_2166665 baseEnd_2166665 := by
    simpa [prefixWord, tailWord_2166665, baseEnd_2166665] using wordTrace_append hprefix tailTrace_2166665
  have hstable : (prefixWord ++ tailWord_2166665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166665).length < 2 ^ (prefixWord ++ tailWord_2166665).sum := by decide
  have hdescent : baseEnd_2166665 < baseStart_2166665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166695 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2166695 : Nat := 118140960795 + 2166695 * 2 ^ 59
def prefixEnd_2166695 : Nat := 4983230072969 + 3 ^ 40 * 2166695 * 2
def baseEnd_2166695 : Nat := 370851988897835176516019

theorem tailTrace_2166695 : CollatzResearch.WordTrace tailWord_2166695 prefixEnd_2166695 370851988897835176516019 := by
  unfold tailWord_2166695
  simp only [CollatzResearch.WordTrace]
  refine ⟨79025858885441531890557539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52683905923627687927038359 79025858885441531890557539)
  ·
    refine ⟨118538788328162297835836309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79025858885441531890557539 118538788328162297835836309)
    ·
      refine ⟨5556505702882607711054827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118538788328162297835836309 5556505702882607711054827)
      ·
        refine ⟨8334758554323911566582241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5556505702882607711054827 8334758554323911566582241)
        ·
          refine ⟨6251068915742933674936681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8334758554323911566582241 6251068915742933674936681)
          ·
            refine ⟨4688301686807200256202511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6251068915742933674936681 4688301686807200256202511)
            ·
              refine ⟨7032452530210800384303767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688301686807200256202511 7032452530210800384303767)
              ·
                refine ⟨10548678795316200576455651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032452530210800384303767 10548678795316200576455651)
                ·
                  refine ⟨15823018192974300864683477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10548678795316200576455651 15823018192974300864683477)
                  ·
                    refine ⟨370851988897835176516019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15823018192974300864683477 370851988897835176516019)
                    ·
                      rfl

theorem cell23_2166695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2166695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166695 prefixEnd_2166695 := by exact prefixLift 2166695
  have htrace : WordTrace (prefixWord ++ tailWord_2166695) baseStart_2166695 baseEnd_2166695 := by
    simpa [prefixWord, tailWord_2166695, baseEnd_2166695] using wordTrace_append hprefix tailTrace_2166695
  have hstable : (prefixWord ++ tailWord_2166695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166695).length < 2 ^ (prefixWord ++ tailWord_2166695).sum := by decide
  have hdescent : baseEnd_2166695 < baseStart_2166695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166715 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 2, 4, 2]
def baseStart_2166715 : Nat := 118140960795 + 2166715 * 2 ^ 59
def prefixEnd_2166715 : Nat := 4983230072969 + 3 ^ 40 * 2166715 * 2
def baseEnd_2166715 : Nat := 1112566236306595451297965

theorem tailTrace_2166715 : CollatzResearch.WordTrace tailWord_2166715 prefixEnd_2166715 1112566236306595451297965 := by
  unfold tailWord_2166715
  simp only [CollatzResearch.WordTrace]
  refine ⟨79026588345369075306285599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52684392230246050204190399 79026588345369075306285599)
  ·
    refine ⟨118539882518053612959428399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79026588345369075306285599 118539882518053612959428399)
    ·
      refine ⟨177809823777080419439142599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118539882518053612959428399 177809823777080419439142599)
      ·
        refine ⟨266714735665620629158713899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177809823777080419439142599 266714735665620629158713899)
        ·
          refine ⟨400072103498430943738070849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266714735665620629158713899 400072103498430943738070849)
          ·
            refine ⟨300054077623823207803553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400072103498430943738070849 300054077623823207803553137)
            ·
              refine ⟨225040558217867405852664853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300054077623823207803553137 225040558217867405852664853)
              ·
                refine ⟨10548776166462534649343665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225040558217867405852664853 10548776166462534649343665)
                ·
                  refine ⟨7911582124846900987007749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10548776166462534649343665 7911582124846900987007749)
                  ·
                    refine ⟨1483421648408793935063953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7911582124846900987007749 1483421648408793935063953)
                    ·
                      refine ⟨1112566236306595451297965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483421648408793935063953 1112566236306595451297965)
                      ·
                        rfl

theorem cell23_2166715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4, 2].length) (baseStart_2166715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166715 prefixEnd_2166715 := by exact prefixLift 2166715
  have htrace : WordTrace (prefixWord ++ tailWord_2166715) baseStart_2166715 baseEnd_2166715 := by
    simpa [prefixWord, tailWord_2166715, baseEnd_2166715] using wordTrace_append hprefix tailTrace_2166715
  have hstable : (prefixWord ++ tailWord_2166715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166715).length < 2 ^ (prefixWord ++ tailWord_2166715).sum := by decide
  have hdescent : baseEnd_2166715 < baseStart_2166715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166732 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2166732 : Nat := 118140960795 + 2166732 * 2 ^ 59
def prefixEnd_2166732 : Nat := 4983230072969 + 3 ^ 40 * 2166732 * 2
def baseEnd_2166732 : Nat := 1112574965477721884785387

theorem tailTrace_2166732 : CollatzResearch.WordTrace tailWord_2166732 prefixEnd_2166732 1112574965477721884785387 := by
  unfold tailWord_2166732
  simp only [CollatzResearch.WordTrace]
  refine ⟨39513604193153743604827225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52684805590871658139769633 39513604193153743604827225)
  ·
    refine ⟨29635203144865307703620419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39513604193153743604827225 29635203144865307703620419)
    ·
      refine ⟨44452804717297961555430629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29635203144865307703620419 44452804717297961555430629)
      ·
        refine ⟨8334900884493367791643243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44452804717297961555430629 8334900884493367791643243)
        ·
          refine ⟨12502351326740051687464865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334900884493367791643243 12502351326740051687464865)
          ·
            refine ⟨9376763495055038765598649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502351326740051687464865 9376763495055038765598649)
            ·
              refine ⟨7032572621291279074198987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9376763495055038765598649 7032572621291279074198987)
              ·
                refine ⟨10548858931936918611298481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7032572621291279074198987 10548858931936918611298481)
                ·
                  refine ⟨7911644198952688958473861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10548858931936918611298481 7911644198952688958473861)
                  ·
                    refine ⟨1483433287303629179713849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7911644198952688958473861 1483433287303629179713849)
                    ·
                      refine ⟨1112574965477721884785387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483433287303629179713849 1112574965477721884785387)
                      ·
                        rfl

theorem cell23_2166732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2166732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166732 prefixEnd_2166732 := by exact prefixLift 2166732
  have htrace : WordTrace (prefixWord ++ tailWord_2166732) baseStart_2166732 baseEnd_2166732 := by
    simpa [prefixWord, tailWord_2166732, baseEnd_2166732] using wordTrace_append hprefix tailTrace_2166732
  have hstable : (prefixWord ++ tailWord_2166732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166732).length < 2 ^ (prefixWord ++ tailWord_2166732).sum := by decide
  have hdescent : baseEnd_2166732 < baseStart_2166732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166775 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 9, 2]
def baseStart_2166775 : Nat := 118140960795 + 2166775 * 2 ^ 59
def prefixEnd_2166775 : Nat := 4983230072969 + 3 ^ 40 * 2166775 * 2
def baseEnd_2166775 : Nat := 1112597045145865216547689

theorem tailTrace_2166775 : CollatzResearch.WordTrace tailWord_2166775 prefixEnd_2166775 1112597045145865216547689 := by
  unfold tailWord_2166775
  simp only [CollatzResearch.WordTrace]
  refine ⟨79028776725151705553469779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52685851150101137035646519 79028776725151705553469779)
  ·
    refine ⟨118543165087727558330204669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79028776725151705553469779 118543165087727558330204669)
    ·
      refine ⟨44453686907897834373826751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118543165087727558330204669 44453686907897834373826751)
      ·
        refine ⟨66680530361846751560740127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44453686907897834373826751 66680530361846751560740127)
        ·
          refine ⟨100020795542770127341110191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66680530361846751560740127 100020795542770127341110191)
          ·
            refine ⟨150031193314155191011665287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100020795542770127341110191 150031193314155191011665287)
            ·
              refine ⟨225046789971232786517497931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150031193314155191011665287 225046789971232786517497931)
              ·
                refine ⟨337570184956849179776246897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225046789971232786517497931 337570184956849179776246897)
                ·
                  refine ⟨253177638717636884832185173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337570184956849179776246897 253177638717636884832185173)
                  ·
                    refine ⟨1483462726861153622063585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 253177638717636884832185173 1483462726861153622063585)
                    ·
                      refine ⟨1112597045145865216547689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483462726861153622063585 1112597045145865216547689)
                      ·
                        rfl

theorem cell23_2166775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_2166775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166775 prefixEnd_2166775 := by exact prefixLift 2166775
  have htrace : WordTrace (prefixWord ++ tailWord_2166775) baseStart_2166775 baseEnd_2166775 := by
    simpa [prefixWord, tailWord_2166775, baseEnd_2166775] using wordTrace_append hprefix tailTrace_2166775
  have hstable : (prefixWord ++ tailWord_2166775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166775).length < 2 ^ (prefixWord ++ tailWord_2166775).sum := by decide
  have hdescent : baseEnd_2166775 < baseStart_2166775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166778 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_2166778 : Nat := 118140960795 + 2166778 * 2 ^ 59
def prefixEnd_2166778 : Nat := 4983230072969 + 3 ^ 40 * 2166778 * 2
def baseEnd_2166778 : Nat := 1112598585587828704810175

theorem tailTrace_2166778 : CollatzResearch.WordTrace tailWord_2166778 prefixEnd_2166778 1112598585587828704810175 := by
  unfold tailWord_2166778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19757221536035209266457247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52685924096093891377219325 19757221536035209266457247)
  ·
    refine ⟨29635832304052813899685871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19757221536035209266457247 29635832304052813899685871)
    ·
      refine ⟨44453748456079220849528807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29635832304052813899685871 44453748456079220849528807)
      ·
        refine ⟨66680622684118831274293211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44453748456079220849528807 66680622684118831274293211)
        ·
          refine ⟨100020934026178246911439817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66680622684118831274293211 100020934026178246911439817)
          ·
            refine ⟨75015700519633685183579863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100020934026178246911439817 75015700519633685183579863)
            ·
              refine ⟨112523550779450527775369795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75015700519633685183579863 112523550779450527775369795)
              ·
                refine ⟨168785326169175791663054693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112523550779450527775369795 168785326169175791663054693)
                ·
                  refine ⟨31647248656720460936822755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168785326169175791663054693 31647248656720460936822755)
                  ·
                    refine ⟨47470872985080691405234133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31647248656720460936822755 47470872985080691405234133)
                    ·
                      refine ⟨1112598585587828704810175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47470872985080691405234133 1112598585587828704810175)
                      ·
                        rfl

theorem cell23_2166778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_2166778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166778 prefixEnd_2166778 := by exact prefixLift 2166778
  have htrace : WordTrace (prefixWord ++ tailWord_2166778) baseStart_2166778 baseEnd_2166778 := by
    simpa [prefixWord, tailWord_2166778, baseEnd_2166778] using wordTrace_append hprefix tailTrace_2166778
  have hstable : (prefixWord ++ tailWord_2166778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166778).length < 2 ^ (prefixWord ++ tailWord_2166778).sum := by decide
  have hdescent : baseEnd_2166778 < baseStart_2166778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166785 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2166785 : Nat := 118140960795 + 2166785 * 2 ^ 59
def prefixEnd_2166785 : Nat := 4983230072969 + 3 ^ 40 * 2166785 * 2
def baseEnd_2166785 : Nat := 370867393317470059140881

theorem tailTrace_2166785 : CollatzResearch.WordTrace tailWord_2166785 prefixEnd_2166785 370867393317470059140881 := by
  unfold tailWord_2166785
  simp only [CollatzResearch.WordTrace]
  refine ⟨79029141455115477261333809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52686094303410318174222539 79029141455115477261333809)
  ·
    refine ⟨59271856091336607946000357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79029141455115477261333809 59271856091336607946000357)
    ·
      refine ⟨11113473017125613989875067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59271856091336607946000357 11113473017125613989875067)
      ·
        refine ⟨16670209525688420984812601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11113473017125613989875067 16670209525688420984812601)
        ·
          refine ⟨12502657144266315738609451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16670209525688420984812601 12502657144266315738609451)
          ·
            refine ⟨18753985716399473607914177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12502657144266315738609451 18753985716399473607914177)
            ·
              refine ⟨14065489287299605205935633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18753985716399473607914177 14065489287299605205935633)
              ·
                refine ⟨10549116965474703904451725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14065489287299605205935633 10549116965474703904451725)
                ·
                  refine ⟨3955918862053013964169397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10549116965474703904451725 3955918862053013964169397)
                  ·
                    refine ⟨370867393317470059140881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3955918862053013964169397 370867393317470059140881)
                    ·
                      rfl

theorem cell23_2166785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2166785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166785 prefixEnd_2166785 := by exact prefixLift 2166785
  have htrace : WordTrace (prefixWord ++ tailWord_2166785) baseStart_2166785 baseEnd_2166785 := by
    simpa [prefixWord, tailWord_2166785, baseEnd_2166785] using wordTrace_append hprefix tailTrace_2166785
  have hstable : (prefixWord ++ tailWord_2166785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166785).length < 2 ^ (prefixWord ++ tailWord_2166785).sum := by decide
  have hdescent : baseEnd_2166785 < baseStart_2166785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166792 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_2166792 : Nat := 118140960795 + 2166792 * 2 ^ 59
def prefixEnd_2166792 : Nat := 4983230072969 + 3 ^ 40 * 2166792 * 2
def baseEnd_2166792 : Nat := 1112605774316991650035111

theorem tailTrace_2166792 : CollatzResearch.WordTrace tailWord_2166792 prefixEnd_2166792 1112605774316991650035111 := by
  unfold tailWord_2166792
  simp only [CollatzResearch.WordTrace]
  refine ⟨39514698383045058728419315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52686264510726744971225753 39514698383045058728419315)
  ·
    refine ⟨59272047574567588092628973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39514698383045058728419315 59272047574567588092628973)
    ·
      refine ⟨22227017840462845534735865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59272047574567588092628973 22227017840462845534735865)
      ·
        refine ⟨16670263380347134151051899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22227017840462845534735865 16670263380347134151051899)
        ·
          refine ⟨25005395070520701226577849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16670263380347134151051899 25005395070520701226577849)
          ·
            refine ⟨18754046302890525919933387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25005395070520701226577849 18754046302890525919933387)
            ·
              refine ⟨28131069454335788879900081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18754046302890525919933387 28131069454335788879900081)
              ·
                refine ⟨21098302090751841659925061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28131069454335788879900081 21098302090751841659925061)
                ·
                  refine ⟨3955931642015970311235949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21098302090751841659925061 3955931642015970311235949)
                  ·
                    refine ⟨1483474365755988866713481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3955931642015970311235949 1483474365755988866713481)
                    ·
                      refine ⟨1112605774316991650035111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483474365755988866713481 1112605774316991650035111)
                      ·
                        rfl

theorem cell23_2166792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_2166792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166792 prefixEnd_2166792 := by exact prefixLift 2166792
  have htrace : WordTrace (prefixWord ++ tailWord_2166792) baseStart_2166792 baseEnd_2166792 := by
    simpa [prefixWord, tailWord_2166792, baseEnd_2166792] using wordTrace_append hprefix tailTrace_2166792
  have hstable : (prefixWord ++ tailWord_2166792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166792).length < 2 ^ (prefixWord ++ tailWord_2166792).sum := by decide
  have hdescent : baseEnd_2166792 < baseStart_2166792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166815 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 1, 6]
def baseStart_2166815 : Nat := 118140960795 + 2166815 * 2 ^ 59
def prefixEnd_2166815 : Nat := 4983230072969 + 3 ^ 40 * 2166815 * 2
def baseEnd_2166815 : Nat := 370872528124015020015835

theorem tailTrace_2166815 : CollatzResearch.WordTrace tailWord_2166815 prefixEnd_2166815 370872528124015020015835 := by
  unfold tailWord_2166815
  simp only [CollatzResearch.WordTrace]
  refine ⟨79030235645006792384925899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52686823763337861589950599 79030235645006792384925899)
  ·
    refine ⟨118545353467510188577388849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79030235645006792384925899 118545353467510188577388849)
    ·
      refine ⟨88909015100632641433041637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118545353467510188577388849 88909015100632641433041637)
      ·
        refine ⟨16670440331368620268695307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88909015100632641433041637 16670440331368620268695307)
        ·
          refine ⟨25005660497052930403042961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16670440331368620268695307 25005660497052930403042961)
          ·
            refine ⟨18754245372789697802282221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25005660497052930403042961 18754245372789697802282221)
            ·
              refine ⟨7032842014796136675855833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18754245372789697802282221 7032842014796136675855833)
              ·
                refine ⟨5274631511097102506891875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032842014796136675855833 5274631511097102506891875)
                ·
                  refine ⟨7911947266645653760337813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274631511097102506891875 7911947266645653760337813)
                  ·
                    refine ⟨370872528124015020015835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7911947266645653760337813 370872528124015020015835)
                    ·
                      rfl

theorem cell23_2166815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_2166815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166815 prefixEnd_2166815 := by exact prefixLift 2166815
  have htrace : WordTrace (prefixWord ++ tailWord_2166815) baseStart_2166815 baseEnd_2166815 := by
    simpa [prefixWord, tailWord_2166815, baseEnd_2166815] using wordTrace_append hprefix tailTrace_2166815
  have hstable : (prefixWord ++ tailWord_2166815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166815).length < 2 ^ (prefixWord ++ tailWord_2166815).sum := by decide
  have hdescent : baseEnd_2166815 < baseStart_2166815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166832 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 2, 4]
def baseStart_2166832 : Nat := 118140960795 + 2166832 * 2 ^ 59
def prefixEnd_2166832 : Nat := 4983230072969 + 3 ^ 40 * 2166832 * 2
def baseEnd_2166832 : Nat := 370875437847723831178309

theorem tailTrace_2166832 : CollatzResearch.WordTrace tailWord_2166832 prefixEnd_2166832 370875437847723831178309 := by
  unfold tailWord_2166832
  simp only [CollatzResearch.WordTrace]
  refine ⟨39515427842972602144147375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52687237123963469525529833 39515427842972602144147375)
  ·
    refine ⟨59273141764458903216221063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39515427842972602144147375 59273141764458903216221063)
    ·
      refine ⟨88909712646688354824331595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59273141764458903216221063 88909712646688354824331595)
      ·
        refine ⟨133364568970032532236497393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88909712646688354824331595 133364568970032532236497393)
        ·
          refine ⟨100023426727524399177373045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133364568970032532236497393 100023426727524399177373045)
          ·
            refine ⟨9377196255705412422878723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100023426727524399177373045 9377196255705412422878723)
            ·
              refine ⟨14065794383558118634318085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9377196255705412422878723 14065794383558118634318085)
              ·
                refine ⟨2637336446917147243934641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14065794383558118634318085 2637336446917147243934641)
                ·
                  refine ⟨1978002335187860432950981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637336446917147243934641 1978002335187860432950981)
                  ·
                    refine ⟨370875437847723831178309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1978002335187860432950981 370875437847723831178309)
                    ·
                      rfl

theorem cell23_2166832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_2166832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166832 prefixEnd_2166832 := by exact prefixLift 2166832
  have htrace : WordTrace (prefixWord ++ tailWord_2166832) baseStart_2166832 baseEnd_2166832 := by
    simpa [prefixWord, tailWord_2166832, baseEnd_2166832] using wordTrace_append hprefix tailTrace_2166832
  have hstable : (prefixWord ++ tailWord_2166832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166832).length < 2 ^ (prefixWord ++ tailWord_2166832).sum := by decide
  have hdescent : baseEnd_2166832 < baseStart_2166832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166833 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 1, 1, 3]
def baseStart_2166833 : Nat := 118140960795 + 2166833 * 2 ^ 59
def prefixEnd_2166833 : Nat := 4983230072969 + 3 ^ 40 * 2166833 * 2
def baseEnd_2166833 : Nat := 1112626827023825989622423

theorem tailTrace_2166833 : CollatzResearch.WordTrace tailWord_2166833 prefixEnd_2166833 1112626827023825989622423 := by
  unfold tailWord_2166833
  simp only [CollatzResearch.WordTrace]
  refine ⟨79030892158941581459081153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52687261439294387639387435 79030892158941581459081153)
  ·
    refine ⟨59273169119206186094310865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79030892158941581459081153 59273169119206186094310865)
    ·
      refine ⟨44454876839404639570733149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59273169119206186094310865 44454876839404639570733149)
      ·
        refine ⟨16670578814776739839024931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44454876839404639570733149 16670578814776739839024931)
        ·
          refine ⟨25005868222165109758537397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16670578814776739839024931 25005868222165109758537397)
          ·
            refine ⟨2344300145827979039862881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25005868222165109758537397 2344300145827979039862881)
            ·
              refine ⟨1758225109370984279897161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344300145827979039862881 1758225109370984279897161)
              ·
                refine ⟨1318668832028238209922871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758225109370984279897161 1318668832028238209922871)
                ·
                  refine ⟨1978003248042357314884307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318668832028238209922871 1978003248042357314884307)
                  ·
                    refine ⟨2967004872063535972326461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1978003248042357314884307 2967004872063535972326461)
                    ·
                      refine ⟨1112626827023825989622423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967004872063535972326461 1112626827023825989622423)
                      ·
                        rfl

theorem cell23_2166833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_2166833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166833 prefixEnd_2166833 := by exact prefixLift 2166833
  have htrace : WordTrace (prefixWord ++ tailWord_2166833) baseStart_2166833 baseEnd_2166833 := by
    simpa [prefixWord, tailWord_2166833, baseEnd_2166833] using wordTrace_append hprefix tailTrace_2166833
  have hstable : (prefixWord ++ tailWord_2166833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166833).length < 2 ^ (prefixWord ++ tailWord_2166833).sum := by decide
  have hdescent : baseEnd_2166833 < baseStart_2166833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166849 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2166849 : Nat := 118140960795 + 2166849 * 2 ^ 59
def prefixEnd_2166849 : Nat := 4983230072969 + 3 ^ 40 * 2166849 * 2
def baseEnd_2166849 : Nat := 370878347571432642340783

theorem tailTrace_2166849 : CollatzResearch.WordTrace tailWord_2166849 prefixEnd_2166849 370878347571432642340783 := by
  unfold tailWord_2166849
  simp only [CollatzResearch.WordTrace]
  refine ⟨79031475726883616191663601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52687650484589077461109067 79031475726883616191663601)
  ·
    refine ⟨59273606795162712143747701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79031475726883616191663601 59273606795162712143747701)
    ·
      refine ⟨5556900637046504263476347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59273606795162712143747701 5556900637046504263476347)
      ·
        refine ⟨8335350955569756395214521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5556900637046504263476347 8335350955569756395214521)
        ·
          refine ⟨6251513216677317296410891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8335350955569756395214521 6251513216677317296410891)
          ·
            refine ⟨9377269825015975944616337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251513216677317296410891 9377269825015975944616337)
            ·
              refine ⟨7032952368761981958462253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9377269825015975944616337 7032952368761981958462253)
              ·
                refine ⟨2637357138285743234423345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7032952368761981958462253 2637357138285743234423345)
                ·
                  refine ⟨1978017853714307425817509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637357138285743234423345 1978017853714307425817509)
                  ·
                    refine ⟨370878347571432642340783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1978017853714307425817509 370878347571432642340783)
                    ·
                      rfl

theorem cell23_2166849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2166849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166849 prefixEnd_2166849 := by exact prefixLift 2166849
  have htrace : WordTrace (prefixWord ++ tailWord_2166849) baseStart_2166849 baseEnd_2166849 := by
    simpa [prefixWord, tailWord_2166849, baseEnd_2166849] using wordTrace_append hprefix tailTrace_2166849
  have hstable : (prefixWord ++ tailWord_2166849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166849).length < 2 ^ (prefixWord ++ tailWord_2166849).sum := by decide
  have hdescent : baseEnd_2166849 < baseStart_2166849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166862 : List Nat := [4, 1, 1, 1, 1, 5, 3, 7]
def baseStart_2166862 : Nat := 118140960795 + 2166862 * 2 ^ 59
def prefixEnd_2166862 : Nat := 4983230072969 + 3 ^ 40 * 2166862 * 2
def baseEnd_2166862 : Nat := 41208952517140976894807

theorem tailTrace_2166862 : CollatzResearch.WordTrace tailWord_2166862 prefixEnd_2166862 41208952517140976894807 := by
  unfold tailWord_2166862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9878993734479564926485855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52687966583891012941257893 9878993734479564926485855)
  ·
    refine ⟨14818490601719347389728783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9878993734479564926485855 14818490601719347389728783)
    ·
      refine ⟨22227735902579021084593175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14818490601719347389728783 22227735902579021084593175)
      ·
        refine ⟨33341603853868531626889763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22227735902579021084593175 33341603853868531626889763)
        ·
          refine ⟨50012405780802797440334645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33341603853868531626889763 50012405780802797440334645)
          ·
            refine ⟨4688663041950262260031373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50012405780802797440334645 4688663041950262260031373)
            ·
              refine ⟨1758248640731348347511765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4688663041950262260031373 1758248640731348347511765)
              ·
                refine ⟨41208952517140976894807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1758248640731348347511765 41208952517140976894807)
                ·
                  rfl

theorem cell23_2166862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_2166862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166862 prefixEnd_2166862 := by exact prefixLift 2166862
  have htrace : WordTrace (prefixWord ++ tailWord_2166862) baseStart_2166862 baseEnd_2166862 := by
    simpa [prefixWord, tailWord_2166862, baseEnd_2166862] using wordTrace_append hprefix tailTrace_2166862
  have hstable : (prefixWord ++ tailWord_2166862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166862).length < 2 ^ (prefixWord ++ tailWord_2166862).sum := by decide
  have hdescent : baseEnd_2166862 < baseStart_2166862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166872 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2166872 : Nat := 118140960795 + 2166872 * 2 ^ 59
def prefixEnd_2166872 : Nat := 4983230072969 + 3 ^ 40 * 2166872 * 2
def baseEnd_2166872 : Nat := 1112646852769351337034743

theorem tailTrace_2166872 : CollatzResearch.WordTrace tailWord_2166872 prefixEnd_2166872 1112646852769351337034743 := by
  unfold tailWord_2166872
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516157302900145559875435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52688209737200194079833913 39516157302900145559875435)
  ·
    refine ⟨59274235954350218339813153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39516157302900145559875435 59274235954350218339813153)
    ·
      refine ⟨44455676965762663754859865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59274235954350218339813153 44455676965762663754859865)
      ·
        refine ⟨33341757724321997816144899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44455676965762663754859865 33341757724321997816144899)
        ·
          refine ⟨50012636586482996724217349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33341757724321997816144899 50012636586482996724217349)
          ·
            refine ⟨9377369359965561885790753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50012636586482996724217349 9377369359965561885790753)
            ·
              refine ⟨7033027019974171414343065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9377369359965561885790753 7033027019974171414343065)
              ·
                refine ⟨5274770264980628560757299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7033027019974171414343065 5274770264980628560757299)
                ·
                  refine ⟨7912155397470942841135949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274770264980628560757299 7912155397470942841135949)
                  ·
                    refine ⟨2967058274051603565425981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7912155397470942841135949 2967058274051603565425981)
                    ·
                      refine ⟨1112646852769351337034743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967058274051603565425981 1112646852769351337034743)
                      ·
                        rfl

theorem cell23_2166872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2166872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166872 prefixEnd_2166872 := by exact prefixLift 2166872
  have htrace : WordTrace (prefixWord ++ tailWord_2166872) baseStart_2166872 baseEnd_2166872 := by
    simpa [prefixWord, tailWord_2166872, baseEnd_2166872] using wordTrace_append hprefix tailTrace_2166872
  have hstable : (prefixWord ++ tailWord_2166872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166872).length < 2 ^ (prefixWord ++ tailWord_2166872).sum := by decide
  have hdescent : baseEnd_2166872 < baseStart_2166872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166876 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_2166876 : Nat := 118140960795 + 2166876 * 2 ^ 59
def prefixEnd_2166876 : Nat := 4983230072969 + 3 ^ 40 * 2166876 * 2
def baseEnd_2166876 : Nat := 1112648906691969321384725

theorem tailTrace_2166876 : CollatzResearch.WordTrace tailWord_2166876 prefixEnd_2166876 1112648906691969321384725 := by
  unfold tailWord_2166876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516230248892899901448241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52688306998523866535264321 39516230248892899901448241)
  ·
    refine ⟨29637172686669674926086181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39516230248892899901448241 29637172686669674926086181)
    ·
      refine ⟨5556969878750564048641159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29637172686669674926086181 5556969878750564048641159)
      ·
        refine ⟨8335454818125846072961739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5556969878750564048641159 8335454818125846072961739)
        ·
          refine ⟨12503182227188769109442609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8335454818125846072961739 12503182227188769109442609)
          ·
            refine ⟨9377386670391576832081957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12503182227188769109442609 9377386670391576832081957)
            ·
              refine ⟨1758260000698420656015367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9377386670391576832081957 1758260000698420656015367)
              ·
                refine ⟨2637390001047630984023051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758260000698420656015367 2637390001047630984023051)
                ·
                  refine ⟨3956085001571446476034577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637390001047630984023051 3956085001571446476034577)
                  ·
                    refine ⟨2967063751178584857025933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3956085001571446476034577 2967063751178584857025933)
                    ·
                      refine ⟨1112648906691969321384725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967063751178584857025933 1112648906691969321384725)
                      ·
                        rfl

theorem cell23_2166876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_2166876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166876 prefixEnd_2166876 := by exact prefixLift 2166876
  have htrace : WordTrace (prefixWord ++ tailWord_2166876) baseStart_2166876 baseEnd_2166876 := by
    simpa [prefixWord, tailWord_2166876, baseEnd_2166876] using wordTrace_append hprefix tailTrace_2166876
  have hstable : (prefixWord ++ tailWord_2166876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166876).length < 2 ^ (prefixWord ++ tailWord_2166876).sum := by decide
  have hdescent : baseEnd_2166876 < baseStart_2166876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166916 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_2166916 : Nat := 118140960795 + 2166916 * 2 ^ 59
def prefixEnd_2166916 : Nat := 4983230072969 + 3 ^ 40 * 2166916 * 2
def baseEnd_2166916 : Nat := 1112669445918149164884541

theorem tailTrace_2166916 : CollatzResearch.WordTrace tailWord_2166916 prefixEnd_2166916 1112669445918149164884541 := by
  unfold tailWord_2166916
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516959708820443317176301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52689279611760591089568401 39516959708820443317176301)
  ·
    refine ⟨14818859890807666243941113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39516959708820443317176301 14818859890807666243941113)
    ·
      refine ⟨11114144918105749682955835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14818859890807666243941113 11114144918105749682955835)
      ·
        refine ⟨16671217377158624524433753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11114144918105749682955835 16671217377158624524433753)
        ·
          refine ⟨12503413032868968393325315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16671217377158624524433753 12503413032868968393325315)
          ·
            refine ⟨18755119549303452589987973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12503413032868968393325315 18755119549303452589987973)
            ·
              refine ⟨3516584915494397360622745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18755119549303452589987973 3516584915494397360622745)
              ·
                refine ⟨2637438686620798020467059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516584915494397360622745 2637438686620798020467059)
                ·
                  refine ⟨3956158029931197030700589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637438686620798020467059 3956158029931197030700589)
                  ·
                    refine ⟨1483559261224198886512721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3956158029931197030700589 1483559261224198886512721)
                    ·
                      refine ⟨1112669445918149164884541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483559261224198886512721 1112669445918149164884541)
                      ·
                        rfl

theorem cell23_2166916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_2166916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166916 prefixEnd_2166916 := by exact prefixLift 2166916
  have htrace : WordTrace (prefixWord ++ tailWord_2166916) baseStart_2166916 baseEnd_2166916 := by
    simpa [prefixWord, tailWord_2166916, baseEnd_2166916] using wordTrace_append hprefix tailTrace_2166916
  have hstable : (prefixWord ++ tailWord_2166916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166916).length < 2 ^ (prefixWord ++ tailWord_2166916).sum := by decide
  have hdescent : baseEnd_2166916 < baseStart_2166916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166962 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2166962 : Nat := 118140960795 + 2166962 * 2 ^ 59
def prefixEnd_2166962 : Nat := 4983230072969 + 3 ^ 40 * 2166962 * 2
def baseEnd_2166962 : Nat := 1112693066028255984909329

theorem tailTrace_2166962 : CollatzResearch.WordTrace tailWord_2166962 prefixEnd_2166962 1112693066028255984909329 := by
  unfold tailWord_2166962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758899293868559122631785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52690398116982824327018093 19758899293868559122631785)
  ·
    refine ⟨14819174470401419341973839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19758899293868559122631785 14819174470401419341973839)
    ·
      refine ⟨22228761705602129012960759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14819174470401419341973839 22228761705602129012960759)
      ·
        refine ⟨33343142558403193519441139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22228761705602129012960759 33343142558403193519441139)
        ·
          refine ⟨50014713837604790279161709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33343142558403193519441139 50014713837604790279161709)
          ·
            refine ⟨18755517689101796354685641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50014713837604790279161709 18755517689101796354685641)
            ·
              refine ⟨14066638266826347266014231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18755517689101796354685641 14066638266826347266014231)
              ·
                refine ⟨21099957400239520899021347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14066638266826347266014231 21099957400239520899021347)
                ·
                  refine ⟨31649936100359281348532021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21099957400239520899021347 31649936100359281348532021)
                  ·
                    refine ⟨2967181509408682626424877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31649936100359281348532021 2967181509408682626424877)
                    ·
                      refine ⟨1112693066028255984909329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967181509408682626424877 1112693066028255984909329)
                      ·
                        rfl

theorem cell23_2166962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2166962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166962 prefixEnd_2166962 := by exact prefixLift 2166962
  have htrace : WordTrace (prefixWord ++ tailWord_2166962) baseStart_2166962 baseEnd_2166962 := by
    simpa [prefixWord, tailWord_2166962, baseEnd_2166962] using wordTrace_append hprefix tailTrace_2166962
  have hstable : (prefixWord ++ tailWord_2166962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166962).length < 2 ^ (prefixWord ++ tailWord_2166962).sum := by decide
  have hdescent : baseEnd_2166962 < baseStart_2166962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166975 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_2166975 : Nat := 118140960795 + 2166975 * 2 ^ 59
def prefixEnd_2166975 : Nat := 4983230072969 + 3 ^ 40 * 2166975 * 2
def baseEnd_2166975 : Nat := 1112699741276764434046769

theorem tailTrace_2166975 : CollatzResearch.WordTrace tailWord_2166975 prefixEnd_2166975 1112699741276764434046769 := by
  unfold tailWord_2166975
  simp only [CollatzResearch.WordTrace]
  refine ⟨79036071324427139710750379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52690714216284759807166919 79036071324427139710750379)
  ·
    refine ⟨118554106986640709566125569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79036071324427139710750379 118554106986640709566125569)
    ·
      refine ⟨88915580239980532174594177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118554106986640709566125569 88915580239980532174594177)
      ·
        refine ⟨66686685179985399130945633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88915580239980532174594177 66686685179985399130945633)
        ·
          refine ⟨50015013884989049348209225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66686685179985399130945633 50015013884989049348209225)
          ·
            refine ⟨37511260413741787011156919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50015013884989049348209225 37511260413741787011156919)
            ·
              refine ⟨56266890620612680516735379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37511260413741787011156919 56266890620612680516735379)
              ·
                refine ⟨84400335930919020775103069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56266890620612680516735379 84400335930919020775103069)
                ·
                  refine ⟨31650125974094632790663651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84400335930919020775103069 31650125974094632790663651)
                  ·
                    refine ⟨47475188961141949185995477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31650125974094632790663651 47475188961141949185995477)
                    ·
                      refine ⟨1112699741276764434046769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47475188961141949185995477 1112699741276764434046769)
                      ·
                        rfl

theorem cell23_2166975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_2166975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2166975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2166975 prefixEnd_2166975 := by exact prefixLift 2166975
  have htrace : WordTrace (prefixWord ++ tailWord_2166975) baseStart_2166975 baseEnd_2166975 := by
    simpa [prefixWord, tailWord_2166975, baseEnd_2166975] using wordTrace_append hprefix tailTrace_2166975
  have hstable : (prefixWord ++ tailWord_2166975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166975).length < 2 ^ (prefixWord ++ tailWord_2166975).sum := by decide
  have hdescent : baseEnd_2166975 < baseStart_2166975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167019 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 2, 4, 2]
def baseStart_2167019 : Nat := 118140960795 + 2167019 * 2 ^ 59
def prefixEnd_2167019 : Nat := 4983230072969 + 3 ^ 40 * 2167019 * 2
def baseEnd_2167019 : Nat := 1112722334425562261896567

theorem tailTrace_2167019 : CollatzResearch.WordTrace tailWord_2167019 prefixEnd_2167019 1112722334425562261896567 := by
  unfold tailWord_2167019
  simp only [CollatzResearch.WordTrace]
  refine ⟨79037676136267735225352111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52691784090845156816901407 79037676136267735225352111)
  ·
    refine ⟨118556514204401602838028167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79037676136267735225352111 118556514204401602838028167)
    ·
      refine ⟨177834771306602404257042251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118556514204401602838028167 177834771306602404257042251)
      ·
        refine ⟨266752156959903606385563377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177834771306602404257042251 266752156959903606385563377)
        ·
          refine ⟨200064117719927704789172533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266752156959903606385563377 200064117719927704789172533)
          ·
            refine ⟨18756011036243222323984925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200064117719927704789172533 18756011036243222323984925)
            ·
              refine ⟨7033504138591208371494347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18756011036243222323984925 7033504138591208371494347)
              ·
                refine ⟨10550256207886812557241521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7033504138591208371494347 10550256207886812557241521)
                ·
                  refine ⟨7912692155915109417931141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10550256207886812557241521 7912692155915109417931141)
                  ·
                    refine ⟨1483629779234083015862089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7912692155915109417931141 1483629779234083015862089)
                    ·
                      refine ⟨1112722334425562261896567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483629779234083015862089 1112722334425562261896567)
                      ·
                        rfl

theorem cell23_2167019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4, 2].length) (baseStart_2167019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167019 prefixEnd_2167019 := by exact prefixLift 2167019
  have htrace : WordTrace (prefixWord ++ tailWord_2167019) baseStart_2167019 baseEnd_2167019 := by
    simpa [prefixWord, tailWord_2167019, baseEnd_2167019] using wordTrace_append hprefix tailTrace_2167019
  have hstable : (prefixWord ++ tailWord_2167019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167019).length < 2 ^ (prefixWord ++ tailWord_2167019).sum := by decide
  have hdescent : baseEnd_2167019 < baseStart_2167019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167036 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_2167036 : Nat := 118140960795 + 2167036 * 2 ^ 59
def prefixEnd_2167036 : Nat := 4983230072969 + 3 ^ 40 * 2167036 * 2
def baseEnd_2167036 : Nat := 1112731063596688695383989

theorem tailTrace_2167036 : CollatzResearch.WordTrace tailWord_2167036 prefixEnd_2167036 1112731063596688695383989 := by
  unfold tailWord_2167036
  simp only [CollatzResearch.WordTrace]
  refine ⟨39519148088603073564360481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52692197451470764752480641 39519148088603073564360481)
  ·
    refine ⟨29639361066452305173270361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39519148088603073564360481 29639361066452305173270361)
    ·
      refine ⟨22229520799839228879952771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29639361066452305173270361 22229520799839228879952771)
      ·
        refine ⟨33344281199758843319929157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22229520799839228879952771 33344281199758843319929157)
        ·
          refine ⟨6252052724954783122486717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33344281199758843319929157 6252052724954783122486717)
          ·
            refine ⟨2344519771858043670932519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6252052724954783122486717 2344519771858043670932519)
            ·
              refine ⟨3516779657787065506398779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344519771858043670932519 3516779657787065506398779)
              ·
                refine ⟨5275169486680598259598169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516779657787065506398779 5275169486680598259598169)
                ·
                  refine ⟨3956377115010448694698627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5275169486680598259598169 3956377115010448694698627)
                  ·
                    refine ⟨5934565672515673042047941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956377115010448694698627 5934565672515673042047941)
                    ·
                      refine ⟨1112731063596688695383989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5934565672515673042047941 1112731063596688695383989)
                      ·
                        rfl

theorem cell23_2167036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_2167036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167036 prefixEnd_2167036 := by exact prefixLift 2167036
  have htrace : WordTrace (prefixWord ++ tailWord_2167036) baseStart_2167036 baseEnd_2167036 := by
    simpa [prefixWord, tailWord_2167036, baseEnd_2167036] using wordTrace_append hprefix tailTrace_2167036
  have hstable : (prefixWord ++ tailWord_2167036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167036).length < 2 ^ (prefixWord ++ tailWord_2167036).sum := by decide
  have hdescent : baseEnd_2167036 < baseStart_2167036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167076 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 6]
def baseStart_2167076 : Nat := 118140960795 + 2167076 * 2 ^ 59
def prefixEnd_2167076 : Nat := 4983230072969 + 3 ^ 40 * 2167076 * 2
def baseEnd_2167076 : Nat := 123639066980318726542645

theorem tailTrace_2167076 : CollatzResearch.WordTrace tailWord_2167076 prefixEnd_2167076 123639066980318726542645 := by
  unfold tailWord_2167076
  simp only [CollatzResearch.WordTrace]
  refine ⟨39519877548530616980088541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52693170064707489306784721 39519877548530616980088541)
  ·
    refine ⟨14819954080698981367533203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39519877548530616980088541 14819954080698981367533203)
    ·
      refine ⟨22229931121048472051299805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14819954080698981367533203 22229931121048472051299805)
      ·
        refine ⟨8336224170393177019237427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22229931121048472051299805 8336224170393177019237427)
        ·
          refine ⟨12504336255589765528856141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8336224170393177019237427 12504336255589765528856141)
          ·
            refine ⟨4689126095846162073321053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12504336255589765528856141 4689126095846162073321053)
            ·
              refine ⟨1758422285942310777495395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4689126095846162073321053 1758422285942310777495395)
              ·
                refine ⟨2637633428913466166243093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758422285942310777495395 2637633428913466166243093)
                ·
                  refine ⟨123639066980318726542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2637633428913466166243093 123639066980318726542645)
                  ·
                    rfl

theorem cell23_2167076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_2167076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167076 prefixEnd_2167076 := by exact prefixLift 2167076
  have htrace : WordTrace (prefixWord ++ tailWord_2167076) baseStart_2167076 baseEnd_2167076 := by
    simpa [prefixWord, tailWord_2167076, baseEnd_2167076] using wordTrace_append hprefix tailTrace_2167076
  have hstable : (prefixWord ++ tailWord_2167076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167076).length < 2 ^ (prefixWord ++ tailWord_2167076).sum := by decide
  have hdescent : baseEnd_2167076 < baseStart_2167076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167120 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 1, 1, 3]
def baseStart_2167120 : Nat := 118140960795 + 2167120 * 2 ^ 59
def prefixEnd_2167120 : Nat := 4983230072969 + 3 ^ 40 * 2167120 * 2
def baseEnd_2167120 : Nat := 1112774195971666366733603

theorem tailTrace_2167120 : CollatzResearch.WordTrace tailWord_2167120 prefixEnd_2167120 1112774195971666366733603 := by
  unfold tailWord_2167120
  simp only [CollatzResearch.WordTrace]
  refine ⟨39520679954450914737389407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52694239939267886316519209 39520679954450914737389407)
  ·
    refine ⟨59281019931676372106084111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39520679954450914737389407 59281019931676372106084111)
    ·
      refine ⟨88921529897514558159126167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59281019931676372106084111 88921529897514558159126167)
      ·
        refine ⟨133382294846271837238689251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88921529897514558159126167 133382294846271837238689251)
        ·
          refine ⟨200073442269407755858033877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133382294846271837238689251 200073442269407755858033877)
          ·
            refine ⟨4689221303189244277922669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200073442269407755858033877 4689221303189244277922669)
            ·
              refine ⟨1758457988695966604221001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4689221303189244277922669 1758457988695966604221001)
              ·
                refine ⟨1318843491521974953165751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758457988695966604221001 1318843491521974953165751)
                ·
                  refine ⟨1978265237282962429748627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318843491521974953165751 1978265237282962429748627)
                  ·
                    refine ⟨2967397855924443644622941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1978265237282962429748627 2967397855924443644622941)
                    ·
                      refine ⟨1112774195971666366733603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967397855924443644622941 1112774195971666366733603)
                      ·
                        rfl

theorem cell23_2167120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 1, 3].length) (baseStart_2167120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167120 prefixEnd_2167120 := by exact prefixLift 2167120
  have htrace : WordTrace (prefixWord ++ tailWord_2167120) baseStart_2167120 baseEnd_2167120 := by
    simpa [prefixWord, tailWord_2167120, baseEnd_2167120] using wordTrace_append hprefix tailTrace_2167120
  have hstable : (prefixWord ++ tailWord_2167120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167120).length < 2 ^ (prefixWord ++ tailWord_2167120).sum := by decide
  have hdescent : baseEnd_2167120 < baseStart_2167120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167129 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_2167129 : Nat := 118140960795 + 2167129 * 2 ^ 59
def prefixEnd_2167129 : Nat := 4983230072969 + 3 ^ 40 * 2167129 * 2
def baseEnd_2167129 : Nat := 1112778817297556831521061

theorem tailTrace_2167129 : CollatzResearch.WordTrace tailWord_2167129 prefixEnd_2167129 1112778817297556831521061 := by
  unfold tailWord_2167129
  simp only [CollatzResearch.WordTrace]
  refine ⟨79041688165869224011856441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52694458777246149341237627 79041688165869224011856441)
  ·
    refine ⟨59281266124401918008892331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79041688165869224011856441 59281266124401918008892331)
    ·
      refine ⟨88921899186602877013338497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59281266124401918008892331 88921899186602877013338497)
      ·
        refine ⟨66691424389952157760003873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88921899186602877013338497 66691424389952157760003873)
        ·
          refine ⟨50018568292464118320002905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66691424389952157760003873 50018568292464118320002905)
          ·
            refine ⟨37513926219348088740002179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50018568292464118320002905 37513926219348088740002179)
            ·
              refine ⟨56270889329022133110003269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37513926219348088740002179 56270889329022133110003269)
              ·
                refine ⟨10550791749191649958125613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56270889329022133110003269 10550791749191649958125613)
                ·
                  refine ⟨3956546905946868734297105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10550791749191649958125613 3956546905946868734297105)
                  ·
                    refine ⟨2967410179460151550722829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3956546905946868734297105 2967410179460151550722829)
                    ·
                      refine ⟨1112778817297556831521061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967410179460151550722829 1112778817297556831521061)
                      ·
                        rfl

theorem cell23_2167129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_2167129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167129 prefixEnd_2167129 := by exact prefixLift 2167129
  have htrace : WordTrace (prefixWord ++ tailWord_2167129) baseStart_2167129 baseEnd_2167129 := by
    simpa [prefixWord, tailWord_2167129, baseEnd_2167129] using wordTrace_append hprefix tailTrace_2167129
  have hstable : (prefixWord ++ tailWord_2167129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167129).length < 2 ^ (prefixWord ++ tailWord_2167129).sum := by decide
  have hdescent : baseEnd_2167129 < baseStart_2167129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167139 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2167139 : Nat := 118140960795 + 2167139 * 2 ^ 59
def prefixEnd_2167139 : Nat := 4983230072969 + 3 ^ 40 * 2167139 * 2
def baseEnd_2167139 : Nat := 1112783952104101792396015

theorem tailTrace_2167139 : CollatzResearch.WordTrace tailWord_2167139 prefixEnd_2167139 1112783952104101792396015 := by
  unfold tailWord_2167139
  simp only [CollatzResearch.WordTrace]
  refine ⟨79042052895832995719720471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52694701930555330479813647 79042052895832995719720471)
  ·
    refine ⟨118563079343749493579580707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79042052895832995719720471 118563079343749493579580707)
    ·
      refine ⟨177844619015624240369371061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118563079343749493579580707 177844619015624240369371061)
      ·
        refine ⟨16672933032714772534628537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177844619015624240369371061 16672933032714772534628537)
        ·
          refine ⟨12504699774536079400971403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16672933032714772534628537 12504699774536079400971403)
          ·
            refine ⟨18757049661804119101457105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12504699774536079400971403 18757049661804119101457105)
            ·
              refine ⟨14067787246353089326092829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18757049661804119101457105 14067787246353089326092829)
              ·
                refine ⟨5275420217382408497284811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14067787246353089326092829 5275420217382408497284811)
                ·
                  refine ⟨7913130326073612745927217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5275420217382408497284811 7913130326073612745927217)
                  ·
                    refine ⟨5934847744555209559445413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7913130326073612745927217 5934847744555209559445413)
                    ·
                      refine ⟨1112783952104101792396015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5934847744555209559445413 1112783952104101792396015)
                      ·
                        rfl

theorem cell23_2167139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2167139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167139 prefixEnd_2167139 := by exact prefixLift 2167139
  have htrace : WordTrace (prefixWord ++ tailWord_2167139) baseStart_2167139 baseEnd_2167139 := by
    simpa [prefixWord, tailWord_2167139, baseEnd_2167139] using wordTrace_append hprefix tailTrace_2167139
  have hstable : (prefixWord ++ tailWord_2167139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167139).length < 2 ^ (prefixWord ++ tailWord_2167139).sum := by decide
  have hdescent : baseEnd_2167139 < baseStart_2167139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167143 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2167143 : Nat := 118140960795 + 2167143 * 2 ^ 59
def prefixEnd_2167143 : Nat := 4983230072969 + 3 ^ 40 * 2167143 * 2
def baseEnd_2167143 : Nat := 1112786006026719776745997

theorem tailTrace_2167143 : CollatzResearch.WordTrace tailWord_2167143 prefixEnd_2167143 1112786006026719776745997 := by
  unfold tailWord_2167143
  simp only [CollatzResearch.WordTrace]
  refine ⟨79042198787818504402866083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52694799191879002935244055 79042198787818504402866083)
  ·
    refine ⟨118563298181727756604299125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79042198787818504402866083 118563298181727756604299125)
    ·
      refine ⟨11115309204536977181653043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118563298181727756604299125 11115309204536977181653043)
      ·
        refine ⟨16672963806805465772479565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11115309204536977181653043 16672963806805465772479565)
        ·
          refine ⟨6252361427552049664679837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16672963806805465772479565 6252361427552049664679837)
          ·
            refine ⟨2344635535332018624254939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6252361427552049664679837 2344635535332018624254939)
            ·
              refine ⟨3516953302998027936382409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344635535332018624254939 3516953302998027936382409)
              ·
                refine ⟨2637714977248520952286807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516953302998027936382409 2637714977248520952286807)
                ·
                  refine ⟨3956572465872781428430211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637714977248520952286807 3956572465872781428430211)
                  ·
                    refine ⟨5934858698809172142645317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956572465872781428430211 5934858698809172142645317)
                    ·
                      refine ⟨1112786006026719776745997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5934858698809172142645317 1112786006026719776745997)
                      ·
                        rfl

theorem cell23_2167143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2167143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167143 prefixEnd_2167143 := by exact prefixLift 2167143
  have htrace : WordTrace (prefixWord ++ tailWord_2167143) baseStart_2167143 baseEnd_2167143 := by
    simpa [prefixWord, tailWord_2167143, baseEnd_2167143] using wordTrace_append hprefix tailTrace_2167143
  have hstable : (prefixWord ++ tailWord_2167143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167143).length < 2 ^ (prefixWord ++ tailWord_2167143).sum := by decide
  have hdescent : baseEnd_2167143 < baseStart_2167143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167162 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_2167162 : Nat := 118140960795 + 2167162 * 2 ^ 59
def prefixEnd_2167162 : Nat := 4983230072969 + 3 ^ 40 * 2167162 * 2
def baseEnd_2167162 : Nat := 370931920719718400802803

theorem tailTrace_2167162 : CollatzResearch.WordTrace tailWord_2167162 prefixEnd_2167162 370931920719718400802803 := by
  unfold tailWord_2167162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19760722943687417661951935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52695261183166447098538493 19760722943687417661951935)
  ·
    refine ⟨29641084415531126492927903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19760722943687417661951935 29641084415531126492927903)
    ·
      refine ⟨44461626623296689739391855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29641084415531126492927903 44461626623296689739391855)
      ·
        refine ⟨66692439934945034609087783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44461626623296689739391855 66692439934945034609087783)
        ·
          refine ⟨100038659902417551913631675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66692439934945034609087783 100038659902417551913631675)
          ·
            refine ⟨150057989853626327870447513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100038659902417551913631675 150057989853626327870447513)
            ·
              refine ⟨112543492390219745902835635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150057989853626327870447513 112543492390219745902835635)
              ·
                refine ⟨168815238585329618854253453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112543492390219745902835635 168815238585329618854253453)
                ·
                  refine ⟨63305714469498607070345045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168815238585329618854253453 63305714469498607070345045)
                  ·
                    refine ⟨370931920719718400802803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63305714469498607070345045 370931920719718400802803)
                    ·
                      rfl

theorem cell23_2167162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_2167162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167162 prefixEnd_2167162 := by exact prefixLift 2167162
  have htrace : WordTrace (prefixWord ++ tailWord_2167162) baseStart_2167162 baseEnd_2167162 := by
    simpa [prefixWord, tailWord_2167162, baseEnd_2167162] using wordTrace_append hprefix tailTrace_2167162
  have hstable : (prefixWord ++ tailWord_2167162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167162).length < 2 ^ (prefixWord ++ tailWord_2167162).sum := by decide
  have hdescent : baseEnd_2167162 < baseStart_2167162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167163 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 1, 2, 3]
def baseStart_2167163 : Nat := 118140960795 + 2167163 * 2 ^ 59
def prefixEnd_2167163 : Nat := 4983230072969 + 3 ^ 40 * 2167163 * 2
def baseEnd_2167163 : Nat := 1112796275639809698495905

theorem tailTrace_2167163 : CollatzResearch.WordTrace tailWord_2167163 prefixEnd_2167163 1112796275639809698495905 := by
  unfold tailWord_2167163
  simp only [CollatzResearch.WordTrace]
  refine ⟨79042928247746047818594143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52695285498497365212396095 79042928247746047818594143)
  ·
    refine ⟨118564392371619071727891215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79042928247746047818594143 118564392371619071727891215)
    ·
      refine ⟨177846588557428607591836823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118564392371619071727891215 177846588557428607591836823)
      ·
        refine ⟨266769882836142911387755235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177846588557428607591836823 266769882836142911387755235)
        ·
          refine ⟨400154824254214367081632853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266769882836142911387755235 400154824254214367081632853)
          ·
            refine ⟨4689314346729074614237885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 400154824254214367081632853 4689314346729074614237885)
            ·
              refine ⟨1758492880023402980339207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4689314346729074614237885 1758492880023402980339207)
              ·
                refine ⟨2637739320035104470508811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758492880023402980339207 2637739320035104470508811)
                ·
                  refine ⟨3956608980052656705763217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637739320035104470508811 3956608980052656705763217)
                  ·
                    refine ⟨2967456735039492529322413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3956608980052656705763217 2967456735039492529322413)
                    ·
                      refine ⟨1112796275639809698495905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967456735039492529322413 1112796275639809698495905)
                      ·
                        rfl

theorem cell23_2167163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 2, 3].length) (baseStart_2167163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167163 prefixEnd_2167163 := by exact prefixLift 2167163
  have htrace : WordTrace (prefixWord ++ tailWord_2167163) baseStart_2167163 baseEnd_2167163 := by
    simpa [prefixWord, tailWord_2167163, baseEnd_2167163] using wordTrace_append hprefix tailTrace_2167163
  have hstable : (prefixWord ++ tailWord_2167163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167163).length < 2 ^ (prefixWord ++ tailWord_2167163).sum := by decide
  have hdescent : baseEnd_2167163 < baseStart_2167163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167177 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 1, 2, 2]
def baseStart_2167177 : Nat := 118140960795 + 2167177 * 2 ^ 59
def prefixEnd_2167177 : Nat := 4983230072969 + 3 ^ 40 * 2167177 * 2
def baseEnd_2167177 : Nat := 1112803464368972643720841

theorem tailTrace_2167177 : CollatzResearch.WordTrace tailWord_2167177 prefixEnd_2167177 1112803464368972643720841 := by
  unfold tailWord_2167177
  simp only [CollatzResearch.WordTrace]
  refine ⟨79043438869695328209603785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52695625913130218806402523 79043438869695328209603785)
  ·
    refine ⟨59282579152271496157202839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79043438869695328209603785 59282579152271496157202839)
    ·
      refine ⟨88923868728407244235804259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59282579152271496157202839 88923868728407244235804259)
      ·
        refine ⟨133385803092610866353706389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88923868728407244235804259 133385803092610866353706389)
        ·
          refine ⟨6252459519966134360329987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133385803092610866353706389 6252459519966134360329987)
          ·
            refine ⟨9378689279949201540494981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6252459519966134360329987 9378689279949201540494981)
            ·
              refine ⟨1758504239990475288842809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9378689279949201540494981 1758504239990475288842809)
              ·
                refine ⟨1318878179992856466632107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758504239990475288842809 1318878179992856466632107)
                ·
                  refine ⟨1978317269989284699948161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318878179992856466632107 1978317269989284699948161)
                  ·
                    refine ⟨1483737952491963524961121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1978317269989284699948161 1483737952491963524961121)
                    ·
                      refine ⟨1112803464368972643720841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483737952491963524961121 1112803464368972643720841)
                      ·
                        rfl

theorem cell23_2167177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 2, 2].length) (baseStart_2167177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167177 prefixEnd_2167177 := by exact prefixLift 2167177
  have htrace : WordTrace (prefixWord ++ tailWord_2167177) baseStart_2167177 baseEnd_2167177 := by
    simpa [prefixWord, tailWord_2167177, baseEnd_2167177] using wordTrace_append hprefix tailTrace_2167177
  have hstable : (prefixWord ++ tailWord_2167177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167177).length < 2 ^ (prefixWord ++ tailWord_2167177).sum := by decide
  have hdescent : baseEnd_2167177 < baseStart_2167177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167199 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2167199 : Nat := 118140960795 + 2167199 * 2 ^ 59
def prefixEnd_2167199 : Nat := 4983230072969 + 3 ^ 40 * 2167199 * 2
def baseEnd_2167199 : Nat := 1112814760943371557645739

theorem tailTrace_2167199 : CollatzResearch.WordTrace tailWord_2167199 prefixEnd_2167199 1112814760943371557645739 := by
  unfold tailWord_2167199
  simp only [CollatzResearch.WordTrace]
  refine ⟨79044241275615625966904651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52696160850410417311269767 79044241275615625966904651)
  ·
    refine ⟨118566361913423438950356977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79044241275615625966904651 118566361913423438950356977)
    ·
      refine ⟨88924771435067579212767733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118566361913423438950356977 88924771435067579212767733)
      ·
        refine ⟨8336697322037585551196975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88924771435067579212767733 8336697322037585551196975)
        ·
          refine ⟨12505045983056378326795463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8336697322037585551196975 12505045983056378326795463)
          ·
            refine ⟨18757568974584567490193195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12505045983056378326795463 18757568974584567490193195)
            ·
              refine ⟨28136353461876851235289793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18757568974584567490193195 28136353461876851235289793)
              ·
                refine ⟨21102265096407638426467345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28136353461876851235289793 21102265096407638426467345)
                ·
                  refine ⟨15826698822305728819850509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21102265096407638426467345 15826698822305728819850509)
                  ·
                    refine ⟨5935012058364648307443941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15826698822305728819850509 5935012058364648307443941)
                    ·
                      refine ⟨1112814760943371557645739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5935012058364648307443941 1112814760943371557645739)
                      ·
                        rfl

theorem cell23_2167199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2167199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167199 prefixEnd_2167199 := by exact prefixLift 2167199
  have htrace : WordTrace (prefixWord ++ tailWord_2167199) baseStart_2167199 baseEnd_2167199 := by
    simpa [prefixWord, tailWord_2167199, baseEnd_2167199] using wordTrace_append hprefix tailTrace_2167199
  have hstable : (prefixWord ++ tailWord_2167199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167199).length < 2 ^ (prefixWord ++ tailWord_2167199).sum := by decide
  have hdescent : baseEnd_2167199 < baseStart_2167199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167239 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 7]
def baseStart_2167239 : Nat := 118140960795 + 2167239 * 2 ^ 59
def prefixEnd_2167239 : Nat := 4983230072969 + 3 ^ 40 * 2167239 * 2
def baseEnd_2167239 : Nat := 123648366685505711238395

theorem tailTrace_2167239 : CollatzResearch.WordTrace tailWord_2167239 prefixEnd_2167239 123648366685505711238395 := by
  unfold tailWord_2167239
  simp only [CollatzResearch.WordTrace]
  refine ⟨79045700195470712798360771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52697133463647141865573847 79045700195470712798360771)
  ·
    refine ⟨118568550293206069197541157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79045700195470712798360771 118568550293206069197541157)
    ·
      refine ⟨22231603179976137974538967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118568550293206069197541157 22231603179976137974538967)
      ·
        refine ⟨33347404769964206961808451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22231603179976137974538967 33347404769964206961808451)
        ·
          refine ⟨50021107154946310442712677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33347404769964206961808451 50021107154946310442712677)
          ·
            refine ⟨9378957591552433208008627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50021107154946310442712677 9378957591552433208008627)
            ·
              refine ⟨14068436387328649812012941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9378957591552433208008627 14068436387328649812012941)
              ·
                refine ⟨5275663645248243679504853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14068436387328649812012941 5275663645248243679504853)
                ·
                  refine ⟨123648366685505711238395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5275663645248243679504853 123648366685505711238395)
                  ·
                    rfl

theorem cell23_2167239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 7].length) (baseStart_2167239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167239 prefixEnd_2167239 := by exact prefixLift 2167239
  have htrace : WordTrace (prefixWord ++ tailWord_2167239) baseStart_2167239 baseEnd_2167239 := by
    simpa [prefixWord, tailWord_2167239, baseEnd_2167239] using wordTrace_append hprefix tailTrace_2167239
  have hstable : (prefixWord ++ tailWord_2167239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167239).length < 2 ^ (prefixWord ++ tailWord_2167239).sum := by decide
  have hdescent : baseEnd_2167239 < baseStart_2167239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167279 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_2167279 : Nat := 118140960795 + 2167279 * 2 ^ 59
def prefixEnd_2167279 : Nat := 4983230072969 + 3 ^ 40 * 2167279 * 2
def baseEnd_2167279 : Nat := 1112855839395731244645371

theorem tailTrace_2167279 : CollatzResearch.WordTrace tailWord_2167279 prefixEnd_2167279 1112855839395731244645371 := by
  unfold tailWord_2167279
  simp only [CollatzResearch.WordTrace]
  refine ⟨79047159115325799629816891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52698106076883866419877927 79047159115325799629816891)
  ·
    refine ⟨118570738672988699444725337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79047159115325799629816891 118570738672988699444725337)
    ·
      refine ⟨88928054004741524583544003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118570738672988699444725337 88928054004741524583544003)
      ·
        refine ⟨133392081007112286875316005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88928054004741524583544003 133392081007112286875316005)
        ·
          refine ⟨25011015188833553789121751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133392081007112286875316005 25011015188833553789121751)
          ·
            refine ⟨37516522783250330683682627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25011015188833553789121751 37516522783250330683682627)
            ·
              refine ⟨56274784174875496025523941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37516522783250330683682627 56274784174875496025523941)
              ·
                refine ⟨10551522032789155504785739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56274784174875496025523941 10551522032789155504785739)
                ·
                  refine ⟨15827283049183733257178609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10551522032789155504785739 15827283049183733257178609)
                  ·
                    refine ⟨11870462286887799942883957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15827283049183733257178609 11870462286887799942883957)
                    ·
                      refine ⟨1112855839395731244645371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11870462286887799942883957 1112855839395731244645371)
                      ·
                        rfl

theorem cell23_2167279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_2167279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167279 prefixEnd_2167279 := by exact prefixLift 2167279
  have htrace : WordTrace (prefixWord ++ tailWord_2167279) baseStart_2167279 baseEnd_2167279 := by
    simpa [prefixWord, tailWord_2167279, baseEnd_2167279] using wordTrace_append hprefix tailTrace_2167279
  have hstable : (prefixWord ++ tailWord_2167279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167279).length < 2 ^ (prefixWord ++ tailWord_2167279).sum := by decide
  have hdescent : baseEnd_2167279 < baseStart_2167279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167306 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2167306 : Nat := 118140960795 + 2167306 * 2 ^ 59
def prefixEnd_2167306 : Nat := 4983230072969 + 3 ^ 40 * 2167306 * 2
def baseEnd_2167306 : Nat := 1112869703373402639007747

theorem tailTrace_2167306 : CollatzResearch.WordTrace tailWord_2167306 prefixEnd_2167306 1112869703373402639007747 := by
  unfold tailWord_2167306
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762035971556995810262443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52698762590818655494033181 19762035971556995810262443)
  ·
    refine ⟨29643053957335493715393665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19762035971556995810262443 29643053957335493715393665)
    ·
      refine ⟨22232290468001620286545249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29643053957335493715393665 22232290468001620286545249)
      ·
        refine ⟨16674217851001215214908937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22232290468001620286545249 16674217851001215214908937)
        ·
          refine ⟨12505663388250911411181703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16674217851001215214908937 12505663388250911411181703)
          ·
            refine ⟨18758495082376367116772555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12505663388250911411181703 18758495082376367116772555)
            ·
              refine ⟨28137742623564550675158833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18758495082376367116772555 28137742623564550675158833)
              ·
                refine ⟨21103306967673413006369125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28137742623564550675158833 21103306967673413006369125)
                ·
                  refine ⟨3956870056438764938694211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21103306967673413006369125 3956870056438764938694211)
                  ·
                    refine ⟨5935305084658147408041317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3956870056438764938694211 5935305084658147408041317)
                    ·
                      refine ⟨1112869703373402639007747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5935305084658147408041317 1112869703373402639007747)
                      ·
                        rfl

theorem cell23_2167306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2167306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167306 prefixEnd_2167306 := by exact prefixLift 2167306
  have htrace : WordTrace (prefixWord ++ tailWord_2167306) baseStart_2167306 baseEnd_2167306 := by
    simpa [prefixWord, tailWord_2167306, baseEnd_2167306] using wordTrace_append hprefix tailTrace_2167306
  have hstable : (prefixWord ++ tailWord_2167306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167306).length < 2 ^ (prefixWord ++ tailWord_2167306).sum := by decide
  have hdescent : baseEnd_2167306 < baseStart_2167306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167341 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2167341 : Nat := 118140960795 + 2167341 * 2 ^ 59
def prefixEnd_2167341 : Nat := 4983230072969 + 3 ^ 40 * 2167341 * 2
def baseEnd_2167341 : Nat := 123654186132923333563343

theorem tailTrace_2167341 : CollatzResearch.WordTrace tailWord_2167341 prefixEnd_2167341 123654186132923333563343 := by
  unfold tailWord_2167341
  simp only [CollatzResearch.WordTrace]
  refine ⟨79049420441101184218573877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52699613627400789479049251 79049420441101184218573877)
  ·
    refine ⟨7410883166353236020491301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79049420441101184218573877 7410883166353236020491301)
    ·
      refine ⟨1389540593691231753842119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7410883166353236020491301 1389540593691231753842119)
      ·
        refine ⟨2084310890536847630763179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1389540593691231753842119 2084310890536847630763179)
        ·
          refine ⟨3126466335805271446144769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084310890536847630763179 3126466335805271446144769)
          ·
            refine ⟨2344849751853953584608577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126466335805271446144769 2344849751853953584608577)
            ·
              refine ⟨1758637313890465188456433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344849751853953584608577 1758637313890465188456433)
              ·
                refine ⟨1318977985417848891342325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758637313890465188456433 1318977985417848891342325)
                ·
                  refine ⟨123654186132923333563343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318977985417848891342325 123654186132923333563343)
                  ·
                    rfl

theorem cell23_2167341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2167341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167341 prefixEnd_2167341 := by exact prefixLift 2167341
  have htrace : WordTrace (prefixWord ++ tailWord_2167341) baseStart_2167341 baseEnd_2167341 := by
    simpa [prefixWord, tailWord_2167341, baseEnd_2167341] using wordTrace_append hprefix tailTrace_2167341
  have hstable : (prefixWord ++ tailWord_2167341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167341).length < 2 ^ (prefixWord ++ tailWord_2167341).sum := by decide
  have hdescent : baseEnd_2167341 < baseStart_2167341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167346 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_2167346 : Nat := 118140960795 + 2167346 * 2 ^ 59
def prefixEnd_2167346 : Nat := 4983230072969 + 3 ^ 40 * 2167346 * 2
def baseEnd_2167346 : Nat := 123654471399953609167507

theorem tailTrace_2167346 : CollatzResearch.WordTrace tailWord_2167346 prefixEnd_2167346 123654471399953609167507 := by
  unfold tailWord_2167346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762400701520767518126473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52699735204055380048337261 19762400701520767518126473)
  ·
    refine ⟨14821800526140575638594855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19762400701520767518126473 14821800526140575638594855)
    ·
      refine ⟨22232700789210863457892283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14821800526140575638594855 22232700789210863457892283)
      ·
        refine ⟨33349051183816295186838425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22232700789210863457892283 33349051183816295186838425)
        ·
          refine ⟨25011788387862221390128819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33349051183816295186838425 25011788387862221390128819)
          ·
            refine ⟨37517682581793332085193229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25011788387862221390128819 37517682581793332085193229)
            ·
              refine ⟨14069130968172499531947461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37517682581793332085193229 14069130968172499531947461)
              ·
                refine ⟨2637962056532343662240149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14069130968172499531947461 2637962056532343662240149)
                ·
                  refine ⟨123654471399953609167507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2637962056532343662240149 123654471399953609167507)
                  ·
                    rfl

theorem cell23_2167346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_2167346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167346 prefixEnd_2167346 := by exact prefixLift 2167346
  have htrace : WordTrace (prefixWord ++ tailWord_2167346) baseStart_2167346 baseEnd_2167346 := by
    simpa [prefixWord, tailWord_2167346, baseEnd_2167346] using wordTrace_append hprefix tailTrace_2167346
  have hstable : (prefixWord ++ tailWord_2167346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167346).length < 2 ^ (prefixWord ++ tailWord_2167346).sum := by decide
  have hdescent : baseEnd_2167346 < baseStart_2167346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167383 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 1, 5, 2]
def baseStart_2167383 : Nat := 118140960795 + 2167383 * 2 ^ 59
def prefixEnd_2167383 : Nat := 4983230072969 + 3 ^ 40 * 2167383 * 2
def baseEnd_2167383 : Nat := 1112909241383798837744893

theorem tailTrace_2167383 : CollatzResearch.WordTrace tailWord_2167383 prefixEnd_2167383 1112909241383798837744893 := by
  unfold tailWord_2167383
  simp only [CollatzResearch.WordTrace]
  refine ⟨79050952306949025391602803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52700634871299350261068535 79050952306949025391602803)
  ·
    refine ⟨118576428460423538087404205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79050952306949025391602803 118576428460423538087404205)
    ·
      refine ⟨44466160672658826782776577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118576428460423538087404205 44466160672658826782776577)
      ·
        refine ⟨33349620504494120087082433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44466160672658826782776577 33349620504494120087082433)
        ·
          refine ⟨25012215378370590065311825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33349620504494120087082433 25012215378370590065311825)
          ·
            refine ⟨18759161533777942548983869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25012215378370590065311825 18759161533777942548983869)
            ·
              refine ⟨7034685575166728455868951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18759161533777942548983869 7034685575166728455868951)
              ·
                refine ⟨10552028362750092683803427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7034685575166728455868951 10552028362750092683803427)
                ·
                  refine ⟨15828042544125139025705141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10552028362750092683803427 15828042544125139025705141)
                  ·
                    refine ⟨1483878988511731783659857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15828042544125139025705141 1483878988511731783659857)
                    ·
                      refine ⟨1112909241383798837744893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483878988511731783659857 1112909241383798837744893)
                      ·
                        rfl

theorem cell23_2167383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_2167383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167383 prefixEnd_2167383 := by exact prefixLift 2167383
  have htrace : WordTrace (prefixWord ++ tailWord_2167383) baseStart_2167383 baseEnd_2167383 := by
    simpa [prefixWord, tailWord_2167383, baseEnd_2167383] using wordTrace_append hprefix tailTrace_2167383
  have hstable : (prefixWord ++ tailWord_2167383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167383).length < 2 ^ (prefixWord ++ tailWord_2167383).sum := by decide
  have hdescent : baseEnd_2167383 < baseStart_2167383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167393 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 1, 5]
def baseStart_2167393 : Nat := 118140960795 + 2167393 * 2 ^ 59
def prefixEnd_2167393 : Nat := 4983230072969 + 3 ^ 40 * 2167393 * 2
def baseEnd_2167393 : Nat := 370971458730114599539949

theorem tailTrace_2167393 : CollatzResearch.WordTrace tailWord_2167393 prefixEnd_2167393 370971458730114599539949 := by
  unfold tailWord_2167393
  simp only [CollatzResearch.WordTrace]
  refine ⟨79051317036912797099466833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52700878024608531399644555 79051317036912797099466833)
  ·
    refine ⟨59288487777684597824600125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79051317036912797099466833 59288487777684597824600125)
    ·
      refine ⟨22233182916631724184225047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59288487777684597824600125 22233182916631724184225047)
      ·
        refine ⟨33349774374947586276337571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22233182916631724184225047 33349774374947586276337571)
        ·
          refine ⟨50024661562421379414506357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33349774374947586276337571 50024661562421379414506357)
          ·
            refine ⟨4689812021477004320109971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50024661562421379414506357 4689812021477004320109971)
            ·
              refine ⟨7034718032215506480164957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4689812021477004320109971 7034718032215506480164957)
              ·
                refine ⟨2638019262080814930061859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7034718032215506480164957 2638019262080814930061859)
                ·
                  refine ⟨3957028893121222395092789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638019262080814930061859 3957028893121222395092789)
                  ·
                    refine ⟨370971458730114599539949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3957028893121222395092789 370971458730114599539949)
                    ·
                      rfl

theorem cell23_2167393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_2167393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167393 prefixEnd_2167393 := by exact prefixLift 2167393
  have htrace : WordTrace (prefixWord ++ tailWord_2167393) baseStart_2167393 baseEnd_2167393 := by
    simpa [prefixWord, tailWord_2167393, baseEnd_2167393] using wordTrace_append hprefix tailTrace_2167393
  have hstable : (prefixWord ++ tailWord_2167393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167393).length < 2 ^ (prefixWord ++ tailWord_2167393).sum := by decide
  have hdescent : baseEnd_2167393 < baseStart_2167393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167416 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_2167416 : Nat := 118140960795 + 2167416 * 2 ^ 59
def prefixEnd_2167416 : Nat := 4983230072969 + 3 ^ 40 * 2167416 * 2
def baseEnd_2167416 : Nat := 1112926186245397208632241

theorem tailTrace_2167416 : CollatzResearch.WordTrace tailWord_2167416 prefixEnd_2167416 1112926186245397208632241 := by
  unfold tailWord_2167416
  simp only [CollatzResearch.WordTrace]
  refine ⟨39526077957914736013777051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52701437277219648018369401 39526077957914736013777051)
  ·
    refine ⟨59289116936872104020665577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39526077957914736013777051 59289116936872104020665577)
    ·
      refine ⟨44466837702654078015499183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59289116936872104020665577 44466837702654078015499183)
      ·
        refine ⟨66700256553981117023248775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44466837702654078015499183 66700256553981117023248775)
        ·
          refine ⟨100050384830971675534873163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66700256553981117023248775 100050384830971675534873163)
          ·
            refine ⟨150075577246457513302309745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100050384830971675534873163 150075577246457513302309745)
            ·
              refine ⟨112556682934843134976732309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150075577246457513302309745 112556682934843134976732309)
              ·
                refine ⟨5276094512570771952034327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112556682934843134976732309 5276094512570771952034327)
                ·
                  refine ⟨7914141768856157928051491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5276094512570771952034327 7914141768856157928051491)
                  ·
                    refine ⟨11871212653284236892077237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7914141768856157928051491 11871212653284236892077237)
                    ·
                      refine ⟨1112926186245397208632241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11871212653284236892077237 1112926186245397208632241)
                      ·
                        rfl

theorem cell23_2167416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_2167416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167416 prefixEnd_2167416 := by exact prefixLift 2167416
  have htrace : WordTrace (prefixWord ++ tailWord_2167416) baseStart_2167416 baseEnd_2167416 := by
    simpa [prefixWord, tailWord_2167416, baseEnd_2167416] using wordTrace_append hprefix tailTrace_2167416
  have hstable : (prefixWord ++ tailWord_2167416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167416).length < 2 ^ (prefixWord ++ tailWord_2167416).sum := by decide
  have hdescent : baseEnd_2167416 < baseStart_2167416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167470 : List Nat := [4, 1, 4, 1, 1, 2, 2, 8]
def baseStart_2167470 : Nat := 118140960795 + 2167470 * 2 ^ 59
def prefixEnd_2167470 : Nat := 4983230072969 + 3 ^ 40 * 2167470 * 2
def baseEnd_2167470 : Nat := 41220515340768148050259

theorem tailTrace_2167470 : CollatzResearch.WordTrace tailWord_2167470 prefixEnd_2167470 41220515340768148050259 := by
  unfold tailWord_2167470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9881765682204229906252483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52702750305089226166679909 9881765682204229906252483)
  ·
    refine ⟨14822648523306344859378725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9881765682204229906252483 14822648523306344859378725)
    ·
      refine ⟨2779246598119939661133511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14822648523306344859378725 2779246598119939661133511)
      ·
        refine ⟨4168869897179909491700267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779246598119939661133511 4168869897179909491700267)
        ·
          refine ⟨6253304845769864237550401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4168869897179909491700267 6253304845769864237550401)
          ·
            refine ⟨4689978634327398178162801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6253304845769864237550401 4689978634327398178162801)
            ·
              refine ⟨3517483975745548633622101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4689978634327398178162801 3517483975745548633622101)
              ·
                refine ⟨41220515340768148050259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3517483975745548633622101 41220515340768148050259)
                ·
                  rfl

theorem cell23_2167470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_2167470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167470 prefixEnd_2167470 := by exact prefixLift 2167470
  have htrace : WordTrace (prefixWord ++ tailWord_2167470) baseStart_2167470 baseEnd_2167470 := by
    simpa [prefixWord, tailWord_2167470, baseEnd_2167470] using wordTrace_append hprefix tailTrace_2167470
  have hstable : (prefixWord ++ tailWord_2167470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167470).length < 2 ^ (prefixWord ++ tailWord_2167470).sum := by decide
  have hdescent : baseEnd_2167470 < baseStart_2167470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167494 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2167494 : Nat := 118140960795 + 2167494 * 2 ^ 59
def prefixEnd_2167494 : Nat := 4983230072969 + 3 ^ 40 * 2167494 * 2
def baseEnd_2167494 : Nat := 1112966237736447903456883

theorem tailTrace_2167494 : CollatzResearch.WordTrace tailWord_2167494 prefixEnd_2167494 1112966237736447903456883 := by
  unfold tailWord_2167494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470468775298340354652923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52703333873031260899262357 2470468775298340354652923)
  ·
    refine ⟨3705703162947510531979385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2470468775298340354652923 3705703162947510531979385)
    ·
      refine ⟨2779277372210632898984539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3705703162947510531979385 2779277372210632898984539)
      ·
        refine ⟨4168916058315949348476809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779277372210632898984539 4168916058315949348476809)
        ·
          refine ⟨3126687043736962011357607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168916058315949348476809 3126687043736962011357607)
          ·
            refine ⟨4690030565605443017036411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126687043736962011357607 4690030565605443017036411)
            ·
              refine ⟨7035045848408164525554617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4690030565605443017036411 7035045848408164525554617)
              ·
                refine ⟨5276284386306123394165963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7035045848408164525554617 5276284386306123394165963)
                ·
                  refine ⟨7914426579459185091248945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5276284386306123394165963 7914426579459185091248945)
                  ·
                    refine ⟨5935819934594388818436709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7914426579459185091248945 5935819934594388818436709)
                    ·
                      refine ⟨1112966237736447903456883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5935819934594388818436709 1112966237736447903456883)
                      ·
                        rfl

theorem cell23_2167494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2167494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167494 prefixEnd_2167494 := by exact prefixLift 2167494
  have htrace : WordTrace (prefixWord ++ tailWord_2167494) baseStart_2167494 baseEnd_2167494 := by
    simpa [prefixWord, tailWord_2167494, baseEnd_2167494] using wordTrace_append hprefix tailTrace_2167494
  have hstable : (prefixWord ++ tailWord_2167494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167494).length < 2 ^ (prefixWord ++ tailWord_2167494).sum := by decide
  have hdescent : baseEnd_2167494 < baseStart_2167494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167501 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2167501 : Nat := 118140960795 + 2167501 * 2 ^ 59
def prefixEnd_2167501 : Nat := 4983230072969 + 3 ^ 40 * 2167501 * 2
def baseEnd_2167501 : Nat := 1112969832101029376069351

theorem tailTrace_2167501 : CollatzResearch.WordTrace tailWord_2167501 prefixEnd_2167501 1112969832101029376069351 := by
  unfold tailWord_2167501
  simp only [CollatzResearch.WordTrace]
  refine ⟨79055256120521531544398357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52703504080347687696265571 79055256120521531544398357)
  ·
    refine ⟨3705715130649446791143673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79055256120521531544398357 3705715130649446791143673)
    ·
      refine ⟨2779286347987085093357755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3705715130649446791143673 2779286347987085093357755)
      ·
        refine ⟨4168929521980627640036633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779286347987085093357755 4168929521980627640036633)
        ·
          refine ⟨3126697141485470730027475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168929521980627640036633 3126697141485470730027475)
          ·
            refine ⟨4690045712228206095041213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126697141485470730027475 4690045712228206095041213)
            ·
              refine ⟨1758767142085577285640455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4690045712228206095041213 1758767142085577285640455)
              ·
                refine ⟨2638150713128365928460683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758767142085577285640455 2638150713128365928460683)
                ·
                  refine ⟨3957226069692548892691025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638150713128365928460683 3957226069692548892691025)
                  ·
                    refine ⟨2967919552269411669518269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3957226069692548892691025 2967919552269411669518269)
                    ·
                      refine ⟨1112969832101029376069351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967919552269411669518269 1112969832101029376069351)
                      ·
                        rfl

theorem cell23_2167501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2167501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167501 prefixEnd_2167501 := by exact prefixLift 2167501
  have htrace : WordTrace (prefixWord ++ tailWord_2167501) baseStart_2167501 baseEnd_2167501 := by
    simpa [prefixWord, tailWord_2167501, baseEnd_2167501] using wordTrace_append hprefix tailTrace_2167501
  have hstable : (prefixWord ++ tailWord_2167501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167501).length < 2 ^ (prefixWord ++ tailWord_2167501).sum := by decide
  have hdescent : baseEnd_2167501 < baseStart_2167501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167537 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 2, 2, 2]
def baseStart_2167537 : Nat := 118140960795 + 2167537 * 2 ^ 59
def prefixEnd_2167537 : Nat := 4983230072969 + 3 ^ 40 * 2167537 * 2
def baseEnd_2167537 : Nat := 1112988317404591235219185

theorem tailTrace_2167537 : CollatzResearch.WordTrace tailWord_2167537 prefixEnd_2167537 1112988317404591235219185 := by
  unfold tailWord_2167537
  simp only [CollatzResearch.WordTrace]
  refine ⟨79056569148391109692708865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52704379432260739795139243 79056569148391109692708865)
  ·
    refine ⟨59292426861293332269531649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79056569148391109692708865 59292426861293332269531649)
    ·
      refine ⟨44469320145969999202148737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59292426861293332269531649 44469320145969999202148737)
      ·
        refine ⟨33351990109477499401611553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44469320145969999202148737 33351990109477499401611553)
        ·
          refine ⟨25013992582108124551208665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33351990109477499401611553 25013992582108124551208665)
          ·
            refine ⟨18760494436581093413406499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25013992582108124551208665 18760494436581093413406499)
            ·
              refine ⟨28140741654871640120109749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18760494436581093413406499 28140741654871640120109749)
              ·
                refine ⟨2638194530144216261260289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28140741654871640120109749 2638194530144216261260289)
                ·
                  refine ⟨1978645897608162195945217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638194530144216261260289 1978645897608162195945217)
                  ·
                    refine ⟨1483984423206121646958913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1978645897608162195945217 1483984423206121646958913)
                    ·
                      refine ⟨1112988317404591235219185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1483984423206121646958913 1112988317404591235219185)
                      ·
                        rfl

theorem cell23_2167537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_2167537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167537 prefixEnd_2167537 := by exact prefixLift 2167537
  have htrace : WordTrace (prefixWord ++ tailWord_2167537) baseStart_2167537 baseEnd_2167537 := by
    simpa [prefixWord, tailWord_2167537, baseEnd_2167537] using wordTrace_append hprefix tailTrace_2167537
  have hstable : (prefixWord ++ tailWord_2167537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167537).length < 2 ^ (prefixWord ++ tailWord_2167537).sum := by decide
  have hdescent : baseEnd_2167537 < baseStart_2167537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167553 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2167553 : Nat := 118140960795 + 2167553 * 2 ^ 59
def prefixEnd_2167553 : Nat := 4983230072969 + 3 ^ 40 * 2167553 * 2
def baseEnd_2167553 : Nat := 1112996533095063172619111

theorem tailTrace_2167553 : CollatzResearch.WordTrace tailWord_2167553 prefixEnd_2167553 1112996533095063172619111 := by
  unfold tailWord_2167553
  simp only [CollatzResearch.WordTrace]
  refine ⟨79057152716333144425291313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52704768477555429616860875 79057152716333144425291313)
  ·
    refine ⟨59292864537249858318968485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79057152716333144425291313 59292864537249858318968485)
    ·
      refine ⟨11117412100734348434806591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59292864537249858318968485 11117412100734348434806591)
      ·
        refine ⟨16676118151101522652209887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11117412100734348434806591 16676118151101522652209887)
        ·
          refine ⟨25014177226652283978314831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16676118151101522652209887 25014177226652283978314831)
          ·
            refine ⟨37521265839978425967472247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25014177226652283978314831 37521265839978425967472247)
            ·
              refine ⟨56281898759967638951208371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37521265839978425967472247 56281898759967638951208371)
              ·
                refine ⟨84422848139951458426812557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56281898759967638951208371 84422848139951458426812557)
                ·
                  refine ⟨31658568052481796910054709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84422848139951458426812557 31658568052481796910054709)
                  ·
                    refine ⟨2967990754920168460317629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31658568052481796910054709 2967990754920168460317629)
                    ·
                      refine ⟨1112996533095063172619111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2967990754920168460317629 1112996533095063172619111)
                      ·
                        rfl

theorem cell23_2167553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2167553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167553 prefixEnd_2167553 := by exact prefixLift 2167553
  have htrace : WordTrace (prefixWord ++ tailWord_2167553) baseStart_2167553 baseEnd_2167553 := by
    simpa [prefixWord, tailWord_2167553, baseEnd_2167553] using wordTrace_append hprefix tailTrace_2167553
  have hstable : (prefixWord ++ tailWord_2167553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167553).length < 2 ^ (prefixWord ++ tailWord_2167553).sum := by decide
  have hdescent : baseEnd_2167553 < baseStart_2167553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167560 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 5]
def baseStart_2167560 : Nat := 118140960795 + 2167560 * 2 ^ 59
def prefixEnd_2167560 : Nat := 4983230072969 + 3 ^ 40 * 2167560 * 2
def baseEnd_2167560 : Nat := 123666680828849405025731

theorem tailTrace_2167560 : CollatzResearch.WordTrace tailWord_2167560 prefixEnd_2167560 123666680828849405025731 := by
  unfold tailWord_2167560
  simp only [CollatzResearch.WordTrace]
  refine ⟨39528704013653892310398067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52704938684871856413864089 39528704013653892310398067)
  ·
    refine ⟨59293056020480838465597101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39528704013653892310398067 59293056020480838465597101)
    ·
      refine ⟨22234896007680314424598913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59293056020480838465597101 22234896007680314424598913)
      ·
        refine ⟨16676172005760235818449185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22234896007680314424598913 16676172005760235818449185)
        ·
          refine ⟨12507129004320176863836889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16676172005760235818449185 12507129004320176863836889)
          ·
            refine ⟨9380346753240132647877667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12507129004320176863836889 9380346753240132647877667)
            ·
              refine ⟨14070520129860198971816501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9380346753240132647877667 14070520129860198971816501)
              ·
                refine ⟨1319111262174393653607797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14070520129860198971816501 1319111262174393653607797)
                ·
                  refine ⟨123666680828849405025731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319111262174393653607797 123666680828849405025731)
                  ·
                    rfl

theorem cell23_2167560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 5].length) (baseStart_2167560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167560 prefixEnd_2167560 := by exact prefixLift 2167560
  have htrace : WordTrace (prefixWord ++ tailWord_2167560) baseStart_2167560 baseEnd_2167560 := by
    simpa [prefixWord, tailWord_2167560, baseEnd_2167560] using wordTrace_append hprefix tailTrace_2167560
  have hstable : (prefixWord ++ tailWord_2167560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167560).length < 2 ^ (prefixWord ++ tailWord_2167560).sum := by decide
  have hdescent : baseEnd_2167560 < baseStart_2167560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167573 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_2167573 : Nat := 118140960795 + 2167573 * 2 ^ 59
def prefixEnd_2167573 : Nat := 4983230072969 + 3 ^ 40 * 2167573 * 2
def baseEnd_2167573 : Nat := 371002267569384364789673

theorem tailTrace_2167573 : CollatzResearch.WordTrace tailWord_2167573 prefixEnd_2167573 371002267569384364789673 := by
  unfold tailWord_2167573
  simp only [CollatzResearch.WordTrace]
  refine ⟨79057882176260687841019373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52705254784173791894012915 79057882176260687841019373)
  ·
    refine ⟨29646705816097757940382265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79057882176260687841019373 29646705816097757940382265)
    ·
      refine ⟨22235029362073318455286699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29646705816097757940382265 22235029362073318455286699)
      ·
        refine ⟨33352544043109977682930049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22235029362073318455286699 33352544043109977682930049)
        ·
          refine ⟨25014408032332483262197537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33352544043109977682930049 25014408032332483262197537)
          ·
            refine ⟨18760806024249362446648153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25014408032332483262197537 18760806024249362446648153)
            ·
              refine ⟨14070604518187021834986115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18760806024249362446648153 14070604518187021834986115)
              ·
                refine ⟨21105906777280532752479173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14070604518187021834986115 21105906777280532752479173)
                ·
                  refine ⟨3957357520740099891089845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21105906777280532752479173 3957357520740099891089845)
                  ·
                    refine ⟨371002267569384364789673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3957357520740099891089845 371002267569384364789673)
                    ·
                      rfl

theorem cell23_2167573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_2167573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167573 prefixEnd_2167573 := by exact prefixLift 2167573
  have htrace : WordTrace (prefixWord ++ tailWord_2167573) baseStart_2167573 baseEnd_2167573 := by
    simpa [prefixWord, tailWord_2167573, baseEnd_2167573] using wordTrace_append hprefix tailTrace_2167573
  have hstable : (prefixWord ++ tailWord_2167573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167573).length < 2 ^ (prefixWord ++ tailWord_2167573).sum := by decide
  have hdescent : baseEnd_2167573 < baseStart_2167573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167593 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_2167593 : Nat := 118140960795 + 2167593 * 2 ^ 59
def prefixEnd_2167593 : Nat := 4983230072969 + 3 ^ 40 * 2167593 * 2
def baseEnd_2167593 : Nat := 1113017072321243016118927

theorem tailTrace_2167593 : CollatzResearch.WordTrace tailWord_2167593 prefixEnd_2167593 1113017072321243016118927 := by
  unfold tailWord_2167593
  simp only [CollatzResearch.WordTrace]
  refine ⟨79058611636188231256747433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52705741090792154171164955 79058611636188231256747433)
  ·
    refine ⟨59293958727141173442560575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79058611636188231256747433 59293958727141173442560575)
    ·
      refine ⟨88940938090711760163840863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59293958727141173442560575 88940938090711760163840863)
      ·
        refine ⟨133411407136067640245761295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88940938090711760163840863 133411407136067640245761295)
        ·
          refine ⟨200117110704101460368641943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133411407136067640245761295 200117110704101460368641943)
          ·
            refine ⟨300175666056152190552962915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200117110704101460368641943 300175666056152190552962915)
            ·
              refine ⟨450263499084228285829444373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300175666056152190552962915 450263499084228285829444373)
              ·
                refine ⟨21106101519573200898255205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 450263499084228285829444373 21106101519573200898255205)
                ·
                  refine ⟨3957394034919975168422851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21106101519573200898255205 3957394034919975168422851)
                  ·
                    refine ⟨5936091052379962752634277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3957394034919975168422851 5936091052379962752634277)
                    ·
                      refine ⟨1113017072321243016118927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5936091052379962752634277 1113017072321243016118927)
                      ·
                        rfl

theorem cell23_2167593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_2167593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167593 prefixEnd_2167593 := by exact prefixLift 2167593
  have htrace : WordTrace (prefixWord ++ tailWord_2167593) baseStart_2167593 baseEnd_2167593 := by
    simpa [prefixWord, tailWord_2167593, baseEnd_2167593] using wordTrace_append hprefix tailTrace_2167593
  have hstable : (prefixWord ++ tailWord_2167593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167593).length < 2 ^ (prefixWord ++ tailWord_2167593).sum := by decide
  have hdescent : baseEnd_2167593 < baseStart_2167593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167643 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 3]
def baseStart_2167643 : Nat := 118140960795 + 2167643 * 2 ^ 59
def prefixEnd_2167643 : Nat := 4983230072969 + 3 ^ 40 * 2167643 * 2
def baseEnd_2167643 : Nat := 1113042746353967820493697

theorem tailTrace_2167643 : CollatzResearch.WordTrace tailWord_2167643 prefixEnd_2167643 1113042746353967820493697 := by
  unfold tailWord_2167643
  simp only [CollatzResearch.WordTrace]
  refine ⟨79060435286007089796067583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52706956857338059864045055 79060435286007089796067583)
  ·
    refine ⟨118590652929010634694101375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79060435286007089796067583 118590652929010634694101375)
    ·
      refine ⟨177885979393515952041152063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118590652929010634694101375 177885979393515952041152063)
      ·
        refine ⟨266828969090273928061728095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177885979393515952041152063 266828969090273928061728095)
        ·
          refine ⟨400243453635410892092592143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266828969090273928061728095 400243453635410892092592143)
          ·
            refine ⟨600365180453116338138888215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400243453635410892092592143 600365180453116338138888215)
            ·
              refine ⟨900547770679674507208332323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600365180453116338138888215 900547770679674507208332323)
              ·
                refine ⟨1350821656019511760812498485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900547770679674507208332323 1350821656019511760812498485)
                ·
                  refine ⟨126639530251829227576171733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350821656019511760812498485 126639530251829227576171733)
                  ·
                    refine ⟨2968113990277247521316525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 126639530251829227576171733 2968113990277247521316525)
                    ·
                      refine ⟨1113042746353967820493697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2968113990277247521316525 1113042746353967820493697)
                      ·
                        rfl

theorem cell23_2167643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 3].length) (baseStart_2167643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167643 prefixEnd_2167643 := by exact prefixLift 2167643
  have htrace : WordTrace (prefixWord ++ tailWord_2167643) baseStart_2167643 baseEnd_2167643 := by
    simpa [prefixWord, tailWord_2167643, baseEnd_2167643] using wordTrace_append hprefix tailTrace_2167643
  have hstable : (prefixWord ++ tailWord_2167643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167643).length < 2 ^ (prefixWord ++ tailWord_2167643).sum := by decide
  have hdescent : baseEnd_2167643 < baseStart_2167643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167653 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2167653 : Nat := 118140960795 + 2167653 * 2 ^ 59
def prefixEnd_2167653 : Nat := 4983230072969 + 3 ^ 40 * 2167653 * 2
def baseEnd_2167653 : Nat := 1113047881160512781368651

theorem tailTrace_2167653 : CollatzResearch.WordTrace tailWord_2167653 prefixEnd_2167653 1113047881160512781368651 := by
  unfold tailWord_2167653
  simp only [CollatzResearch.WordTrace]
  refine ⟨79060800015970861503931613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52707200010647241002621075 79060800015970861503931613)
  ·
    refine ⟨29647800005989073063974355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79060800015970861503931613 29647800005989073063974355)
    ·
      refine ⟨44471700008983609595961533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29647800005989073063974355 44471700008983609595961533)
      ·
        refine ⟨16676887503368853598485575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44471700008983609595961533 16676887503368853598485575)
        ·
          refine ⟨25015331255053280397728363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16676887503368853598485575 25015331255053280397728363)
          ·
            refine ⟨37522996882579920596592545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25015331255053280397728363 37522996882579920596592545)
            ·
              refine ⟨28142247661934940447444409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37522996882579920596592545 28142247661934940447444409)
              ·
                refine ⟨21106685746451205335583307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28142247661934940447444409 21106685746451205335583307)
                ·
                  refine ⟨31660028619676808003374961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21106685746451205335583307 31660028619676808003374961)
                  ·
                    refine ⟨23745021464757606002531221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31660028619676808003374961 23745021464757606002531221)
                    ·
                      refine ⟨1113047881160512781368651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23745021464757606002531221 1113047881160512781368651)
                      ·
                        rfl

theorem cell23_2167653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2167653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167653 prefixEnd_2167653 := by exact prefixLift 2167653
  have htrace : WordTrace (prefixWord ++ tailWord_2167653) baseStart_2167653 baseEnd_2167653 := by
    simpa [prefixWord, tailWord_2167653, baseEnd_2167653] using wordTrace_append hprefix tailTrace_2167653
  have hstable : (prefixWord ++ tailWord_2167653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167653).length < 2 ^ (prefixWord ++ tailWord_2167653).sum := by decide
  have hdescent : baseEnd_2167653 < baseStart_2167653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167744 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 2, 4]
def baseStart_2167744 : Nat := 118140960795 + 2167744 * 2 ^ 59
def prefixEnd_2167744 : Nat := 4983230072969 + 3 ^ 40 * 2167744 * 2
def baseEnd_2167744 : Nat := 371031535966690641776911

theorem tailTrace_2167744 : CollatzResearch.WordTrace tailWord_2167744 prefixEnd_2167744 371031535966690641776911 := by
  unfold tailWord_2167744
  simp only [CollatzResearch.WordTrace]
  refine ⟨39532059529320592022747143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52709412705760789363662857 39532059529320592022747143)
  ·
    refine ⟨59298089293980888034120715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39532059529320592022747143 59298089293980888034120715)
    ·
      refine ⟨88947133940971332051181073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59298089293980888034120715 88947133940971332051181073)
      ·
        refine ⟨66710350455728499038385805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88947133940971332051181073 66710350455728499038385805)
        ·
          refine ⟨25016381420898187139394677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66710350455728499038385805 25016381420898187139394677)
          ·
            refine ⟨2345285758209205044318251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25016381420898187139394677 2345285758209205044318251)
            ·
              refine ⟨3517928637313807566477377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345285758209205044318251 3517928637313807566477377)
              ·
                refine ⟨2638446477985355674858033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517928637313807566477377 2638446477985355674858033)
                ·
                  refine ⟨1978834858489016756143525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638446477985355674858033 1978834858489016756143525)
                  ·
                    refine ⟨371031535966690641776911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1978834858489016756143525 371031535966690641776911)
                    ·
                      rfl

theorem cell23_2167744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_2167744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167744 prefixEnd_2167744 := by exact prefixLift 2167744
  have htrace : WordTrace (prefixWord ++ tailWord_2167744) baseStart_2167744 baseEnd_2167744 := by
    simpa [prefixWord, tailWord_2167744, baseEnd_2167744] using wordTrace_append hprefix tailTrace_2167744
  have hstable : (prefixWord ++ tailWord_2167744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167744).length < 2 ^ (prefixWord ++ tailWord_2167744).sum := by decide
  have hdescent : baseEnd_2167744 < baseStart_2167744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167751 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_2167751 : Nat := 118140960795 + 2167751 * 2 ^ 59
def prefixEnd_2167751 : Nat := 4983230072969 + 3 ^ 40 * 2167751 * 2
def baseEnd_2167751 : Nat := 1113098202264653397943201

theorem tailTrace_2167751 : CollatzResearch.WordTrace tailWord_2167751 prefixEnd_2167751 1113098202264653397943201 := by
  unfold tailWord_2167751
  simp only [CollatzResearch.WordTrace]
  refine ⟨79064374369615824240999107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52709582913077216160666071 79064374369615824240999107)
  ·
    refine ⟨118596561554423736361498661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79064374369615824240999107 118596561554423736361498661)
    ·
      refine ⟨22236855291454450567780999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118596561554423736361498661 22236855291454450567780999)
      ·
        refine ⟨33355282937181675851671499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22236855291454450567780999 33355282937181675851671499)
        ·
          refine ⟨50032924405772513777507249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33355282937181675851671499 50032924405772513777507249)
          ·
            refine ⟨37524693304329385333130437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50032924405772513777507249 37524693304329385333130437)
            ·
              refine ⟨7035879994561759749961957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37524693304329385333130437 7035879994561759749961957)
              ·
                refine ⟨1319227498980329953117867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7035879994561759749961957 1319227498980329953117867)
                ·
                  refine ⟨1978841248470494929676801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319227498980329953117867 1978841248470494929676801)
                  ·
                    refine ⟨1484130936352871197257601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1978841248470494929676801 1484130936352871197257601)
                    ·
                      refine ⟨1113098202264653397943201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484130936352871197257601 1113098202264653397943201)
                      ·
                        rfl

theorem cell23_2167751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_2167751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167751 prefixEnd_2167751 := by exact prefixLift 2167751
  have htrace : WordTrace (prefixWord ++ tailWord_2167751) baseStart_2167751 baseEnd_2167751 := by
    simpa [prefixWord, tailWord_2167751, baseEnd_2167751] using wordTrace_append hprefix tailTrace_2167751
  have hstable : (prefixWord ++ tailWord_2167751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167751).length < 2 ^ (prefixWord ++ tailWord_2167751).sum := by decide
  have hdescent : baseEnd_2167751 < baseStart_2167751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167764 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2167764 : Nat := 118140960795 + 2167764 * 2 ^ 59
def prefixEnd_2167764 : Nat := 4983230072969 + 3 ^ 40 * 2167764 * 2
def baseEnd_2167764 : Nat := 1113104877513161847080641

theorem tailTrace_2167764 : CollatzResearch.WordTrace tailWord_2167764 prefixEnd_2167764 1113104877513161847080641 := by
  unfold tailWord_2167764
  simp only [CollatzResearch.WordTrace]
  refine ⟨39532424259284363730611173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52709899012379151640814897 39532424259284363730611173)
  ·
    refine ⟨7412329548615818199489595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39532424259284363730611173 7412329548615818199489595)
    ·
      refine ⟨11118494322923727299234393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412329548615818199489595 11118494322923727299234393)
      ·
        refine ⟨8338870742192795474425795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11118494322923727299234393 8338870742192795474425795)
        ·
          refine ⟨12508306113289193211638693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8338870742192795474425795 12508306113289193211638693)
          ·
            refine ⟨2345307396241723727182255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12508306113289193211638693 2345307396241723727182255)
            ·
              refine ⟨3517961094362585590773383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345307396241723727182255 3517961094362585590773383)
              ·
                refine ⟨5276941641543878386160075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3517961094362585590773383 5276941641543878386160075)
                ·
                  refine ⟨7915412462315817579240113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5276941641543878386160075 7915412462315817579240113)
                  ·
                    refine ⟨5936559346736863184430085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7915412462315817579240113 5936559346736863184430085)
                    ·
                      refine ⟨1113104877513161847080641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5936559346736863184430085 1113104877513161847080641)
                      ·
                        rfl

theorem cell23_2167764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2167764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167764 prefixEnd_2167764 := by exact prefixLift 2167764
  have htrace : WordTrace (prefixWord ++ tailWord_2167764) baseStart_2167764 baseEnd_2167764 := by
    simpa [prefixWord, tailWord_2167764, baseEnd_2167764] using wordTrace_append hprefix tailTrace_2167764
  have hstable : (prefixWord ++ tailWord_2167764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167764).length < 2 ^ (prefixWord ++ tailWord_2167764).sum := by decide
  have hdescent : baseEnd_2167764 < baseStart_2167764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167818 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_2167818 : Nat := 118140960795 + 2167818 * 2 ^ 59
def prefixEnd_2167818 : Nat := 4983230072969 + 3 ^ 40 * 2167818 * 2
def baseEnd_2167818 : Nat := 1113132605468504635805393

theorem tailTrace_2167818 : CollatzResearch.WordTrace tailWord_2167818 prefixEnd_2167818 1113132605468504635805393 := by
  unfold tailWord_2167818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19766704515093273670922027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52711212040248729789125405 19766704515093273670922027)
  ·
    refine ⟨29650056772639910506383041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19766704515093273670922027 29650056772639910506383041)
    ·
      refine ⟨22237542579479932879787281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29650056772639910506383041 22237542579479932879787281)
      ·
        refine ⟨16678156934609949659840461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22237542579479932879787281 16678156934609949659840461)
        ·
          refine ⟨6254308850478731122440173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16678156934609949659840461 6254308850478731122440173)
          ·
            refine ⟨2345365818929524170915065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6254308850478731122440173 2345365818929524170915065)
            ·
              refine ⟨1759024364197143128186299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345365818929524170915065 1759024364197143128186299)
              ·
                refine ⟨2638536546295714692279449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759024364197143128186299 2638536546295714692279449)
                ·
                  refine ⟨1978902409721786019209587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638536546295714692279449 1978902409721786019209587)
                  ·
                    refine ⟨2968353614582679028814381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1978902409721786019209587 2968353614582679028814381)
                    ·
                      refine ⟨1113132605468504635805393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2968353614582679028814381 1113132605468504635805393)
                      ·
                        rfl

theorem cell23_2167818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_2167818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167818 prefixEnd_2167818 := by exact prefixLift 2167818
  have htrace : WordTrace (prefixWord ++ tailWord_2167818) baseStart_2167818 baseEnd_2167818 := by
    simpa [prefixWord, tailWord_2167818, baseEnd_2167818] using wordTrace_append hprefix tailTrace_2167818
  have hstable : (prefixWord ++ tailWord_2167818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167818).length < 2 ^ (prefixWord ++ tailWord_2167818).sum := by decide
  have hdescent : baseEnd_2167818 < baseStart_2167818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167857 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_2167857 : Nat := 118140960795 + 2167857 * 2 ^ 59
def prefixEnd_2167857 : Nat := 4983230072969 + 3 ^ 40 * 2167857 * 2
def baseEnd_2167857 : Nat := 1113152631214029983217713

theorem tailTrace_2167857 : CollatzResearch.WordTrace tailWord_2167857 prefixEnd_2167857 1113152631214029983217713 := by
  unfold tailWord_2167857
  simp only [CollatzResearch.WordTrace]
  refine ⟨79068240507231804344357825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52712160338154536229571883 79068240507231804344357825)
  ·
    refine ⟨59301180380423853258268369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79068240507231804344357825 59301180380423853258268369)
    ·
      refine ⟨44475885285317889943701277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59301180380423853258268369 44475885285317889943701277)
      ·
        refine ⟨16678456981994208728887979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44475885285317889943701277 16678456981994208728887979)
        ·
          refine ⟨25017685472991313093331969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16678456981994208728887979 25017685472991313093331969)
          ·
            refine ⟨18763264104743484819998977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25017685472991313093331969 18763264104743484819998977)
            ·
              refine ⟨14072448078557613614999233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18763264104743484819998977 14072448078557613614999233)
              ·
                refine ⟨10554336058918210211249425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14072448078557613614999233 10554336058918210211249425)
                ·
                  refine ⟨7915752044188657658437069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10554336058918210211249425 7915752044188657658437069)
                  ·
                    refine ⟨2968407016570746621913901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7915752044188657658437069 2968407016570746621913901)
                    ·
                      refine ⟨1113152631214029983217713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2968407016570746621913901 1113152631214029983217713)
                      ·
                        rfl

theorem cell23_2167857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_2167857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167857 prefixEnd_2167857 := by exact prefixLift 2167857
  have htrace : WordTrace (prefixWord ++ tailWord_2167857) baseStart_2167857 baseEnd_2167857 := by
    simpa [prefixWord, tailWord_2167857, baseEnd_2167857] using wordTrace_append hprefix tailTrace_2167857
  have hstable : (prefixWord ++ tailWord_2167857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167857).length < 2 ^ (prefixWord ++ tailWord_2167857).sum := by decide
  have hdescent : baseEnd_2167857 < baseStart_2167857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167864 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 5]
def baseStart_2167864 : Nat := 118140960795 + 2167864 * 2 ^ 59
def prefixEnd_2167864 : Nat := 4983230072969 + 3 ^ 40 * 2167864 * 2
def baseEnd_2167864 : Nat := 123684025064290161758909

theorem tailTrace_2167864 : CollatzResearch.WordTrace tailWord_2167864 prefixEnd_2167864 123684025064290161758909 := by
  unfold tailWord_2167864
  simp only [CollatzResearch.WordTrace]
  refine ⟨39534247909103222269931323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52712330545470963026575097 39534247909103222269931323)
  ·
    refine ⟨59301371863654833404896985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39534247909103222269931323 59301371863654833404896985)
    ·
      refine ⟨44476028897741125053672739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59301371863654833404896985 44476028897741125053672739)
      ·
        refine ⟨66714043346611687580509109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44476028897741125053672739 66714043346611687580509109)
        ·
          refine ⟨6254441563744845710672729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66714043346611687580509109 6254441563744845710672729)
          ·
            refine ⟨4690831172808634283004547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6254441563744845710672729 4690831172808634283004547)
            ·
              refine ⟨7036246759212951424506821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4690831172808634283004547 7036246759212951424506821)
              ·
                refine ⟨1319296267352428392095029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7036246759212951424506821 1319296267352428392095029)
                ·
                  refine ⟨123684025064290161758909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319296267352428392095029 123684025064290161758909)
                  ·
                    rfl

theorem cell23_2167864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 5].length) (baseStart_2167864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167864 prefixEnd_2167864 := by exact prefixLift 2167864
  have htrace : WordTrace (prefixWord ++ tailWord_2167864) baseStart_2167864 baseEnd_2167864 := by
    simpa [prefixWord, tailWord_2167864, baseEnd_2167864] using wordTrace_append hprefix tailTrace_2167864
  have hstable : (prefixWord ++ tailWord_2167864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167864).length < 2 ^ (prefixWord ++ tailWord_2167864).sum := by decide
  have hdescent : baseEnd_2167864 < baseStart_2167864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167897 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_2167897 : Nat := 118140960795 + 2167897 * 2 ^ 59
def prefixEnd_2167897 : Nat := 4983230072969 + 3 ^ 40 * 2167897 * 2
def baseEnd_2167897 : Nat := 1113173170440209826717529

theorem tailTrace_2167897 : CollatzResearch.WordTrace tailWord_2167897 prefixEnd_2167897 1113173170440209826717529 := by
  unfold tailWord_2167897
  simp only [CollatzResearch.WordTrace]
  refine ⟨79069699427086891175813945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52713132951391260783875963 79069699427086891175813945)
  ·
    refine ⟨59302274570315168381860459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79069699427086891175813945 59302274570315168381860459)
    ·
      refine ⟨88953411855472752572790689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59302274570315168381860459 88953411855472752572790689)
      ·
        refine ⟨66715058891604564429593017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88953411855472752572790689 66715058891604564429593017)
        ·
          refine ⟨50036294168703423322194763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66715058891604564429593017 50036294168703423322194763)
          ·
            refine ⟨75054441253055134983292145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50036294168703423322194763 75054441253055134983292145)
            ·
              refine ⟨56290830939791351237469109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75054441253055134983292145 56290830939791351237469109)
              ·
                refine ⟨5277265400605439178512729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56290830939791351237469109 5277265400605439178512729)
                ·
                  refine ⟨3957949050454079383884547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5277265400605439178512729 3957949050454079383884547)
                  ·
                    refine ⟨5936923575681119075826821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3957949050454079383884547 5936923575681119075826821)
                    ·
                      refine ⟨1113173170440209826717529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5936923575681119075826821 1113173170440209826717529)
                      ·
                        rfl

theorem cell23_2167897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_2167897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167897 prefixEnd_2167897 := by exact prefixLift 2167897
  have htrace : WordTrace (prefixWord ++ tailWord_2167897) baseStart_2167897 baseEnd_2167897 := by
    simpa [prefixWord, tailWord_2167897, baseEnd_2167897] using wordTrace_append hprefix tailTrace_2167897
  have hstable : (prefixWord ++ tailWord_2167897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167897).length < 2 ^ (prefixWord ++ tailWord_2167897).sum := by decide
  have hdescent : baseEnd_2167897 < baseStart_2167897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167907 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 7, 4]
def baseStart_2167907 : Nat := 118140960795 + 2167907 * 2 ^ 59
def prefixEnd_2167907 : Nat := 4983230072969 + 3 ^ 40 * 2167907 * 2
def baseEnd_2167907 : Nat := 371059435082251595864161

theorem tailTrace_2167907 : CollatzResearch.WordTrace tailWord_2167907 prefixEnd_2167907 371059435082251595864161 := by
  unfold tailWord_2167907
  simp only [CollatzResearch.WordTrace]
  refine ⟨79070064157050662883677975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52713376104700441922451983 79070064157050662883677975)
  ·
    refine ⟨118605096235575994325516963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79070064157050662883677975 118605096235575994325516963)
    ·
      refine ⟨177907644353363991488275445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118605096235575994325516963 177907644353363991488275445)
      ·
        refine ⟨16678841658127874202025823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177907644353363991488275445 16678841658127874202025823)
        ·
          refine ⟨25018262487191811303038735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16678841658127874202025823 25018262487191811303038735)
          ·
            refine ⟨37527393730787716954558103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25018262487191811303038735 37527393730787716954558103)
            ·
              refine ⟨56291090596181575431837155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37527393730787716954558103 56291090596181575431837155)
              ·
                refine ⟨84436635894272363147755733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56291090596181575431837155 84436635894272363147755733)
                ·
                  refine ⟨1978983653772008511275525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 84436635894272363147755733 1978983653772008511275525)
                  ·
                    refine ⟨371059435082251595864161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1978983653772008511275525 371059435082251595864161)
                    ·
                      rfl

theorem cell23_2167907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 4].length) (baseStart_2167907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167907 prefixEnd_2167907 := by exact prefixLift 2167907
  have htrace : WordTrace (prefixWord ++ tailWord_2167907) baseStart_2167907 baseEnd_2167907 := by
    simpa [prefixWord, tailWord_2167907, baseEnd_2167907] using wordTrace_append hprefix tailTrace_2167907
  have hstable : (prefixWord ++ tailWord_2167907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167907).length < 2 ^ (prefixWord ++ tailWord_2167907).sum := by decide
  have hdescent : baseEnd_2167907 < baseStart_2167907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167975 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2167975 : Nat := 118140960795 + 2167975 * 2 ^ 59
def prefixEnd_2167975 : Nat := 4983230072969 + 3 ^ 40 * 2167975 * 2
def baseEnd_2167975 : Nat := 371071073977086840514057

theorem tailTrace_2167975 : CollatzResearch.WordTrace tailWord_2167975 prefixEnd_2167975 371071073977086840514057 := by
  unfold tailWord_2167975
  simp only [CollatzResearch.WordTrace]
  refine ⟨79072544320804310497153379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52715029547202873664768919 79072544320804310497153379)
  ·
    refine ⟨118608816481206465745730069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79072544320804310497153379 118608816481206465745730069)
    ·
      refine ⟨5559788272556553081831097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118608816481206465745730069 5559788272556553081831097)
      ·
        refine ⟨4169841204417414811373323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5559788272556553081831097 4169841204417414811373323)
        ·
          refine ⟨6254761806626122217059985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169841204417414811373323 6254761806626122217059985)
          ·
            refine ⟨4691071354969591662794989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6254761806626122217059985 4691071354969591662794989)
            ·
              refine ⟨1759151758113596873548121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4691071354969591662794989 1759151758113596873548121)
              ·
                refine ⟨1319363818585197655161091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1759151758113596873548121 1319363818585197655161091)
                ·
                  refine ⟨1979045727877796482741637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319363818585197655161091 1979045727877796482741637)
                  ·
                    refine ⟨371071073977086840514057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1979045727877796482741637 371071073977086840514057)
                    ·
                      rfl

theorem cell23_2167975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2167975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2167975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2167975 prefixEnd_2167975 := by exact prefixLift 2167975
  have htrace : WordTrace (prefixWord ++ tailWord_2167975) baseStart_2167975 baseEnd_2167975 := by
    simpa [prefixWord, tailWord_2167975, baseEnd_2167975] using wordTrace_append hprefix tailTrace_2167975
  have hstable : (prefixWord ++ tailWord_2167975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167975).length < 2 ^ (prefixWord ++ tailWord_2167975).sum := by decide
  have hdescent : baseEnd_2167975 < baseStart_2167975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168001 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2168001 : Nat := 118140960795 + 2168001 * 2 ^ 59
def prefixEnd_2168001 : Nat := 4983230072969 + 3 ^ 40 * 2168001 * 2
def baseEnd_2168001 : Nat := 371075524142759139939017

theorem tailTrace_2168001 : CollatzResearch.WordTrace tailWord_2168001 prefixEnd_2168001 371075524142759139939017 := by
  unfold tailWord_2168001
  simp only [CollatzResearch.WordTrace]
  refine ⟨79073492618710116937599857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52715661745806744625066571 79073492618710116937599857)
  ·
    refine ⟨59305119464032587703199893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79073492618710116937599857 59305119464032587703199893)
    ·
      refine ⟨2779927474876527548587495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59305119464032587703199893 2779927474876527548587495)
      ·
        refine ⟨4169891212314791322881243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779927474876527548587495 4169891212314791322881243)
        ·
          refine ⟨6254836818472186984321865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169891212314791322881243 6254836818472186984321865)
          ·
            refine ⟨4691127613854140238241399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6254836818472186984321865 4691127613854140238241399)
            ·
              refine ⟨7036691420781210357362099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691127613854140238241399 7036691420781210357362099)
              ·
                refine ⟨10555037131171815536043149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7036691420781210357362099 10555037131171815536043149)
                ·
                  refine ⟨3958138924189430826016181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10555037131171815536043149 3958138924189430826016181)
                  ·
                    refine ⟨371075524142759139939017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3958138924189430826016181 371075524142759139939017)
                    ·
                      rfl

theorem cell23_2168001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2168001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168001 prefixEnd_2168001 := by exact prefixLift 2168001
  have htrace : WordTrace (prefixWord ++ tailWord_2168001) baseStart_2168001 baseEnd_2168001 := by
    simpa [prefixWord, tailWord_2168001, baseEnd_2168001] using wordTrace_append hprefix tailTrace_2168001
  have hstable : (prefixWord ++ tailWord_2168001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168001).length < 2 ^ (prefixWord ++ tailWord_2168001).sum := by decide
  have hdescent : baseEnd_2168001 < baseStart_2168001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168007 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_2168007 : Nat := 118140960795 + 2168007 * 2 ^ 59
def prefixEnd_2168007 : Nat := 4983230072969 + 3 ^ 40 * 2168007 * 2
def baseEnd_2168007 : Nat := 1113229653312204396342023

theorem tailTrace_2168007 : CollatzResearch.WordTrace tailWord_2168007 prefixEnd_2168007 1113229653312204396342023 := by
  unfold tailWord_2168007
  simp only [CollatzResearch.WordTrace]
  refine ⟨79073711456688379962318275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52715807637792253308212183 79073711456688379962318275)
  ·
    refine ⟨118610567185032569943477413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79073711456688379962318275 118610567185032569943477413)
    ·
      refine ⟨22239481347193606864402015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118610567185032569943477413 22239481347193606864402015)
      ·
        refine ⟨33359222020790410296603023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22239481347193606864402015 33359222020790410296603023)
        ·
          refine ⟨50038833031185615444904535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33359222020790410296603023 50038833031185615444904535)
          ·
            refine ⟨75058249546778423167356803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50038833031185615444904535 75058249546778423167356803)
            ·
              refine ⟨112587374320167634751035205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75058249546778423167356803 112587374320167634751035205)
              ·
                refine ⟨21110132685031431515819101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112587374320167634751035205 21110132685031431515819101)
                ·
                  refine ⟨7916299756886786818432163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21110132685031431515819101 7916299756886786818432163)
                  ·
                    refine ⟨11874449635330180227648245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7916299756886786818432163 11874449635330180227648245)
                    ·
                      refine ⟨1113229653312204396342023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11874449635330180227648245 1113229653312204396342023)
                      ·
                        rfl

theorem cell23_2168007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_2168007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168007 prefixEnd_2168007 := by exact prefixLift 2168007
  have htrace : WordTrace (prefixWord ++ tailWord_2168007) baseStart_2168007 baseEnd_2168007 := by
    simpa [prefixWord, tailWord_2168007, baseEnd_2168007] using wordTrace_append hprefix tailTrace_2168007
  have hstable : (prefixWord ++ tailWord_2168007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168007).length < 2 ^ (prefixWord ++ tailWord_2168007).sum := by decide
  have hdescent : baseEnd_2168007 < baseStart_2168007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168044 : List Nat := [2, 2, 1, 1, 2, 6, 1, 8]
def baseStart_2168044 : Nat := 118140960795 + 2168044 * 2 ^ 59
def prefixEnd_2168044 : Nat := 4983230072969 + 3 ^ 40 * 2168044 * 2
def baseEnd_2168044 : Nat := 41231431559126694502939

theorem tailTrace_2168044 : CollatzResearch.WordTrace tailWord_2168044 prefixEnd_2168044 41231431559126694502939 := by
  unfold tailWord_2168044
  simp only [CollatzResearch.WordTrace]
  refine ⟨39537530478777167640707593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52716707305036223520943457 39537530478777167640707593)
  ·
    refine ⟨29653147859082875730530695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39537530478777167640707593 29653147859082875730530695)
    ·
      refine ⟨44479721788624313595796043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29653147859082875730530695 44479721788624313595796043)
      ·
        refine ⟨66719582682936470393694065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44479721788624313595796043 66719582682936470393694065)
        ·
          refine ⟨50039687012202352795270549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66719582682936470393694065 50039687012202352795270549)
          ·
            refine ⟨2345610328696985287278307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50039687012202352795270549 2345610328696985287278307)
            ·
              refine ⟨3518415493045477930917461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345610328696985287278307 3518415493045477930917461)
              ·
                refine ⟨41231431559126694502939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3518415493045477930917461 41231431559126694502939)
                ·
                  rfl

theorem cell23_2168044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 8].length) (baseStart_2168044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168044 prefixEnd_2168044 := by exact prefixLift 2168044
  have htrace : WordTrace (prefixWord ++ tailWord_2168044) baseStart_2168044 baseEnd_2168044 := by
    simpa [prefixWord, tailWord_2168044, baseEnd_2168044] using wordTrace_append hprefix tailTrace_2168044
  have hstable : (prefixWord ++ tailWord_2168044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168044).length < 2 ^ (prefixWord ++ tailWord_2168044).sum := by decide
  have hdescent : baseEnd_2168044 < baseStart_2168044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168057 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_2168057 : Nat := 118140960795 + 2168057 * 2 ^ 59
def prefixEnd_2168057 : Nat := 4983230072969 + 3 ^ 40 * 2168057 * 2
def baseEnd_2168057 : Nat := 371085109114976400238931

theorem tailTrace_2168057 : CollatzResearch.WordTrace tailWord_2168057 prefixEnd_2168057 371085109114976400238931 := by
  unfold tailWord_2168057
  simp only [CollatzResearch.WordTrace]
  refine ⟨79075535106507238501638425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52717023404338159001092283 79075535106507238501638425)
  ·
    refine ⟨59306651329880428876228819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79075535106507238501638425 59306651329880428876228819)
    ·
      refine ⟨88959976994820643314343229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59306651329880428876228819 88959976994820643314343229)
      ·
        refine ⟨33359991373057741242878711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88959976994820643314343229 33359991373057741242878711)
        ·
          refine ⟨50039987059586611864318067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33359991373057741242878711 50039987059586611864318067)
          ·
            refine ⟨75059980589379917796477101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50039987059586611864318067 75059980589379917796477101)
            ·
              refine ⟨28147492721017469173678913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75059980589379917796477101 28147492721017469173678913)
              ·
                refine ⟨21110619540763101880259185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28147492721017469173678913 21110619540763101880259185)
                ·
                  refine ⟨15832964655572326410194389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21110619540763101880259185 15832964655572326410194389)
                  ·
                    refine ⟨371085109114976400238931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15832964655572326410194389 371085109114976400238931)
                    ·
                      rfl

theorem cell23_2168057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_2168057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168057 prefixEnd_2168057 := by exact prefixLift 2168057
  have htrace : WordTrace (prefixWord ++ tailWord_2168057) baseStart_2168057 baseEnd_2168057 := by
    simpa [prefixWord, tailWord_2168057, baseEnd_2168057] using wordTrace_append hprefix tailTrace_2168057
  have hstable : (prefixWord ++ tailWord_2168057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168057).length < 2 ^ (prefixWord ++ tailWord_2168057).sum := by decide
  have hdescent : baseEnd_2168057 < baseStart_2168057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168072 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_2168072 : Nat := 118140960795 + 2168072 * 2 ^ 59
def prefixEnd_2168072 : Nat := 4983230072969 + 3 ^ 40 * 2168072 * 2
def baseEnd_2168072 : Nat := 1113263029554746642029225

theorem tailTrace_2168072 : CollatzResearch.WordTrace tailWord_2168072 prefixEnd_2168072 1113263029554746642029225 := by
  unfold tailWord_2168072
  simp only [CollatzResearch.WordTrace]
  refine ⟨39538041100726448031717235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52717388134301930708956313 39538041100726448031717235)
  ·
    refine ⟨59307061651089672047575853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39538041100726448031717235 59307061651089672047575853)
    ·
      refine ⟨22240148119158627017840945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59307061651089672047575853 22240148119158627017840945)
      ·
        refine ⟨16680111089368970263380709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22240148119158627017840945 16680111089368970263380709)
        ·
          refine ⟨3127520829256681924383883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16680111089368970263380709 3127520829256681924383883)
          ·
            refine ⟨4691281243885022886575825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127520829256681924383883 4691281243885022886575825)
            ·
              refine ⟨3518460932913767164931869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4691281243885022886575825 3518460932913767164931869)
              ·
                refine ⟨1319422849842662686849451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3518460932913767164931869 1319422849842662686849451)
                ·
                  refine ⟨1979134274763994030274177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319422849842662686849451 1979134274763994030274177)
                  ·
                    refine ⟨1484350706072995522705633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979134274763994030274177 1484350706072995522705633)
                    ·
                      refine ⟨1113263029554746642029225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484350706072995522705633 1113263029554746642029225)
                      ·
                        rfl

theorem cell23_2168072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_2168072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168072 prefixEnd_2168072 := by exact prefixLift 2168072
  have htrace : WordTrace (prefixWord ++ tailWord_2168072) baseStart_2168072 baseEnd_2168072 := by
    simpa [prefixWord, tailWord_2168072, baseEnd_2168072] using wordTrace_append hprefix tailTrace_2168072
  have hstable : (prefixWord ++ tailWord_2168072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168072).length < 2 ^ (prefixWord ++ tailWord_2168072).sum := by decide
  have hdescent : baseEnd_2168072 < baseStart_2168072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168082 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2168082 : Nat := 118140960795 + 2168082 * 2 ^ 59
def prefixEnd_2168082 : Nat := 4983230072969 + 3 ^ 40 * 2168082 * 2
def baseEnd_2168082 : Nat := 371089388120430534301393

theorem tailTrace_2168082 : CollatzResearch.WordTrace tailWord_2168082 prefixEnd_2168082 371089388120430534301393 := by
  unfold tailWord_2168082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19769111732854166942824625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52717631287611111847532333 19769111732854166942824625)
  ·
    refine ⟨14826833799640625207118469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19769111732854166942824625 14826833799640625207118469)
    ·
      refine ⟨2780031337432617226334713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14826833799640625207118469 2780031337432617226334713)
      ·
        refine ⟨2085023503074462919751035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2780031337432617226334713 2085023503074462919751035)
        ·
          refine ⟨3127535254611694379626553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2085023503074462919751035 3127535254611694379626553)
          ·
            refine ⟨2345651440958770784719915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127535254611694379626553 2345651440958770784719915)
            ·
              refine ⟨3518477161438156177079873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345651440958770784719915 3518477161438156177079873)
              ·
                refine ⟨2638857871078617132809905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3518477161438156177079873 2638857871078617132809905)
                ·
                  refine ⟨1979143403308962849607429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638857871078617132809905 1979143403308962849607429)
                  ·
                    refine ⟨371089388120430534301393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1979143403308962849607429 371089388120430534301393)
                    ·
                      rfl

theorem cell23_2168082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2168082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168082 prefixEnd_2168082 := by exact prefixLift 2168082
  have htrace : WordTrace (prefixWord ++ tailWord_2168082) baseStart_2168082 baseEnd_2168082 := by
    simpa [prefixWord, tailWord_2168082, baseEnd_2168082] using wordTrace_append hprefix tailTrace_2168082
  have hstable : (prefixWord ++ tailWord_2168082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168082).length < 2 ^ (prefixWord ++ tailWord_2168082).sum := by decide
  have hdescent : baseEnd_2168082 < baseStart_2168082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168088 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2168088 : Nat := 118140960795 + 2168088 * 2 ^ 59
def prefixEnd_2168088 : Nat := 4983230072969 + 3 ^ 40 * 2168088 * 2
def baseEnd_2168088 : Nat := 1113271245245218579429151

theorem tailTrace_2168088 : CollatzResearch.WordTrace tailWord_2168088 prefixEnd_2168088 1113271245245218579429151 := by
  unfold tailWord_2168088
  simp only [CollatzResearch.WordTrace]
  refine ⟨39538332884697465398008459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52717777179596620530677945 39538332884697465398008459)
  ·
    refine ⟨59307499327046198097012689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39538332884697465398008459 59307499327046198097012689)
    ·
      refine ⟨44480624495284648572759517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59307499327046198097012689 44480624495284648572759517)
      ·
        refine ⟨16680234185731743214784819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44480624495284648572759517 16680234185731743214784819)
        ·
          refine ⟨25020351278597614822177229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16680234185731743214784819 25020351278597614822177229)
          ·
            refine ⟨9382631729474105558316461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25020351278597614822177229 9382631729474105558316461)
            ·
              refine ⟨3518486898552789584368673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9382631729474105558316461 3518486898552789584368673)
              ·
                refine ⟨2638865173914592188276505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3518486898552789584368673 2638865173914592188276505)
                ·
                  refine ⟨1979148880435944141207379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638865173914592188276505 1979148880435944141207379)
                  ·
                    refine ⟨2968723320653916211811069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979148880435944141207379 2968723320653916211811069)
                    ·
                      refine ⟨1113271245245218579429151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2968723320653916211811069 1113271245245218579429151)
                      ·
                        rfl

theorem cell23_2168088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2168088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168088 prefixEnd_2168088 := by exact prefixLift 2168088
  have htrace : WordTrace (prefixWord ++ tailWord_2168088) baseStart_2168088 baseEnd_2168088 := by
    simpa [prefixWord, tailWord_2168088, baseEnd_2168088] using wordTrace_append hprefix tailTrace_2168088
  have hstable : (prefixWord ++ tailWord_2168088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168088).length < 2 ^ (prefixWord ++ tailWord_2168088).sum := by decide
  have hdescent : baseEnd_2168088 < baseStart_2168088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168107 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_2168107 : Nat := 118140960795 + 2168107 * 2 ^ 59
def prefixEnd_2168107 : Nat := 4983230072969 + 3 ^ 40 * 2168107 * 2
def baseEnd_2168107 : Nat := 1113281001377654005091563

theorem tailTrace_2168107 : CollatzResearch.WordTrace tailWord_2168107 prefixEnd_2168107 1113281001377654005091563 := by
  unfold tailWord_2168107
  simp only [CollatzResearch.WordTrace]
  refine ⟨79077358756326097040958575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52718239170884064693972383 79077358756326097040958575)
  ·
    refine ⟨118616038134489145561437863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79077358756326097040958575 118616038134489145561437863)
    ·
      refine ⟨177924057201733718342156795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118616038134489145561437863 177924057201733718342156795)
      ·
        refine ⟨266886085802600577513235193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177924057201733718342156795 266886085802600577513235193)
        ·
          refine ⟨200164564351950433134926395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266886085802600577513235193 200164564351950433134926395)
          ·
            refine ⟨300246846527925649702389593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200164564351950433134926395 300246846527925649702389593)
            ·
              refine ⟨225185134895944237276792195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300246846527925649702389593 225185134895944237276792195)
              ·
                refine ⟨337777702343916355915188293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225185134895944237276792195 337777702343916355915188293)
                ·
                  refine ⟨63333319189484316734097805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337777702343916355915188293 63333319189484316734097805)
                  ·
                    refine ⟨23749994696056618775286677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63333319189484316734097805 23749994696056618775286677)
                    ·
                      refine ⟨1113281001377654005091563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23749994696056618775286677 1113281001377654005091563)
                      ·
                        rfl

theorem cell23_2168107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_2168107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168107 prefixEnd_2168107 := by exact prefixLift 2168107
  have htrace : WordTrace (prefixWord ++ tailWord_2168107) baseStart_2168107 baseEnd_2168107 := by
    simpa [prefixWord, tailWord_2168107, baseEnd_2168107] using wordTrace_append hprefix tailTrace_2168107
  have hstable : (prefixWord ++ tailWord_2168107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168107).length < 2 ^ (prefixWord ++ tailWord_2168107).sum := by decide
  have hdescent : baseEnd_2168107 < baseStart_2168107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168151 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 7]
def baseStart_2168151 : Nat := 118140960795 + 2168151 * 2 ^ 59
def prefixEnd_2168151 : Nat := 4983230072969 + 3 ^ 40 * 2168151 * 2
def baseEnd_2168151 : Nat := 123700399391827981437929

theorem tailTrace_2168151 : CollatzResearch.WordTrace tailWord_2168151 prefixEnd_2168151 123700399391827981437929 := by
  unfold tailWord_2168151
  simp only [CollatzResearch.WordTrace]
  refine ⟨79078963568166692555560307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52719309045444461703706871 79078963568166692555560307)
  ·
    refine ⟨118618445352250038833340461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79078963568166692555560307 118618445352250038833340461)
    ·
      refine ⟨44481917007093764562502673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118618445352250038833340461 44481917007093764562502673)
      ·
        refine ⟨33361437755320323421877005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44481917007093764562502673 33361437755320323421877005)
        ·
          refine ⟨12510539158245121283203877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33361437755320323421877005 12510539158245121283203877)
          ·
            refine ⟨2345726092170960240600727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12510539158245121283203877 2345726092170960240600727)
            ·
              refine ⟨3518589138256440360901091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345726092170960240600727 3518589138256440360901091)
              ·
                refine ⟨5277883707384660541351637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518589138256440360901091 5277883707384660541351637)
                ·
                  refine ⟨123700399391827981437929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5277883707384660541351637 123700399391827981437929)
                  ·
                    rfl

theorem cell23_2168151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 7].length) (baseStart_2168151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168151 prefixEnd_2168151 := by exact prefixLift 2168151
  have htrace : WordTrace (prefixWord ++ tailWord_2168151) baseStart_2168151 baseEnd_2168151 := by
    simpa [prefixWord, tailWord_2168151, baseEnd_2168151] using wordTrace_append hprefix tailTrace_2168151
  have hstable : (prefixWord ++ tailWord_2168151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168151).length < 2 ^ (prefixWord ++ tailWord_2168151).sum := by decide
  have hdescent : baseEnd_2168151 < baseStart_2168151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168204 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2168204 : Nat := 118140960795 + 2168204 * 2 ^ 59
def prefixEnd_2168204 : Nat := 4983230072969 + 3 ^ 40 * 2168204 * 2
def baseEnd_2168204 : Nat := 1113330809001140125578617

theorem tailTrace_2168204 : CollatzResearch.WordTrace tailWord_2168204 prefixEnd_2168204 1113330809001140125578617 := by
  unfold tailWord_2168204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39540448318487341303619833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52720597757983121738159777 39540448318487341303619833)
  ·
    refine ⟨29655336238865505977714875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39540448318487341303619833 29655336238865505977714875)
    ·
      refine ⟨44483004358298258966572313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29655336238865505977714875 44483004358298258966572313)
      ·
        refine ⟨33362253268723694224929235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44483004358298258966572313 33362253268723694224929235)
        ·
          refine ⟨50043379903085541337393853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33362253268723694224929235 50043379903085541337393853)
          ·
            refine ⟨18766267463657078001522695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50043379903085541337393853 18766267463657078001522695)
            ·
              refine ⟨28149401195485617002284043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18766267463657078001522695 28149401195485617002284043)
              ·
                refine ⟨42224101793228425503426065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28149401195485617002284043 42224101793228425503426065)
                ·
                  refine ⟨31668076344921319127569549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42224101793228425503426065 31668076344921319127569549)
                  ·
                    refine ⟨11875528629345494672838581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31668076344921319127569549 11875528629345494672838581)
                    ·
                      refine ⟨1113330809001140125578617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11875528629345494672838581 1113330809001140125578617)
                      ·
                        rfl

theorem cell23_2168204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2168204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168204 prefixEnd_2168204 := by exact prefixLift 2168204
  have htrace : WordTrace (prefixWord ++ tailWord_2168204) baseStart_2168204 baseEnd_2168204 := by
    simpa [prefixWord, tailWord_2168204, baseEnd_2168204] using wordTrace_append hprefix tailTrace_2168204
  have hstable : (prefixWord ++ tailWord_2168204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168204).length < 2 ^ (prefixWord ++ tailWord_2168204).sum := by decide
  have hdescent : baseEnd_2168204 < baseStart_2168204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168218 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2]
def baseStart_2168218 : Nat := 118140960795 + 2168218 * 2 ^ 59
def prefixEnd_2168218 : Nat := 4983230072969 + 3 ^ 40 * 2168218 * 2
def baseEnd_2168218 : Nat := 1113337997730303070803553

theorem tailTrace_2168218 : CollatzResearch.WordTrace tailWord_2168218 prefixEnd_2168218 1113337997730303070803553 := by
  unfold tailWord_2168218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19770351814730990749562327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52720938172615975332166205 19770351814730990749562327)
  ·
    refine ⟨29655527722096486124343491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19770351814730990749562327 29655527722096486124343491)
    ·
      refine ⟨44483291583144729186515237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29655527722096486124343491 44483291583144729186515237)
      ·
        refine ⟨8340617171839636722471607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44483291583144729186515237 8340617171839636722471607)
        ·
          refine ⟨12510925757759455083707411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8340617171839636722471607 12510925757759455083707411)
          ·
            refine ⟨18766388636639182625561117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12510925757759455083707411 18766388636639182625561117)
            ·
              refine ⟨7037395738739693484585419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18766388636639182625561117 7037395738739693484585419)
              ·
                refine ⟨10556093608109540226878129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037395738739693484585419 10556093608109540226878129)
                ·
                  refine ⟨7917070206082155170158597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10556093608109540226878129 7917070206082155170158597)
                  ·
                    refine ⟨1484450663640404094404737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7917070206082155170158597 1484450663640404094404737)
                    ·
                      refine ⟨1113337997730303070803553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484450663640404094404737 1113337997730303070803553)
                      ·
                        rfl

theorem cell23_2168218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_2168218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168218 prefixEnd_2168218 := by exact prefixLift 2168218
  have htrace : WordTrace (prefixWord ++ tailWord_2168218) baseStart_2168218 baseEnd_2168218 := by
    simpa [prefixWord, tailWord_2168218, baseEnd_2168218] using wordTrace_append hprefix tailTrace_2168218
  have hstable : (prefixWord ++ tailWord_2168218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168218).length < 2 ^ (prefixWord ++ tailWord_2168218).sum := by decide
  have hdescent : baseEnd_2168218 < baseStart_2168218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168232 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2168232 : Nat := 118140960795 + 2168232 * 2 ^ 59
def prefixEnd_2168232 : Nat := 4983230072969 + 3 ^ 40 * 2168232 * 2
def baseEnd_2168232 : Nat := 371115062153155338676163

theorem tailTrace_2168232 : CollatzResearch.WordTrace tailWord_2168232 prefixEnd_2168232 371115062153155338676163 := by
  unfold tailWord_2168232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39540958940436621694629475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52721278587248828926172633 39540958940436621694629475)
  ·
    refine ⟨59311438410654932541944213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39540958940436621694629475 59311438410654932541944213)
    ·
      refine ⟨2780223675499449962903635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59311438410654932541944213 2780223675499449962903635)
      ·
        refine ⟨4170335513249174944355453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780223675499449962903635 4170335513249174944355453)
        ·
          refine ⟨1563875817468440604133295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4170335513249174944355453 1563875817468440604133295)
          ·
            refine ⟨2345813726202660906199943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563875817468440604133295 2345813726202660906199943)
            ·
              refine ⟨3518720589303991359299915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345813726202660906199943 3518720589303991359299915)
              ·
                refine ⟨5278080883955987038949873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518720589303991359299915 5278080883955987038949873)
                ·
                  refine ⟨3958560662966990279212405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5278080883955987038949873 3958560662966990279212405)
                  ·
                    refine ⟨371115062153155338676163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3958560662966990279212405 371115062153155338676163)
                    ·
                      rfl

theorem cell23_2168232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2168232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168232 prefixEnd_2168232 := by exact prefixLift 2168232
  have htrace : WordTrace (prefixWord ++ tailWord_2168232) baseStart_2168232 baseEnd_2168232 := by
    simpa [prefixWord, tailWord_2168232, baseEnd_2168232] using wordTrace_append hprefix tailTrace_2168232
  have hstable : (prefixWord ++ tailWord_2168232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168232).length < 2 ^ (prefixWord ++ tailWord_2168232).sum := by decide
  have hdescent : baseEnd_2168232 < baseStart_2168232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168245 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2168245 : Nat := 118140960795 + 2168245 * 2 ^ 59
def prefixEnd_2168245 : Nat := 4983230072969 + 3 ^ 40 * 2168245 * 2
def baseEnd_2168245 : Nat := 371117287235991488388643

theorem tailTrace_2168245 : CollatzResearch.WordTrace tailWord_2168245 prefixEnd_2168245 371117287235991488388643 := by
  unfold tailWord_2168245
  simp only [CollatzResearch.WordTrace]
  refine ⟨79082392029826146609482189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52721594686550764406321459 79082392029826146609482189)
  ·
    refine ⟨29655897011184804978555821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79082392029826146609482189 29655897011184804978555821)
    ·
      refine ⟨11120961379194301866958433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29655897011184804978555821 11120961379194301866958433)
      ·
        refine ⟨8340721034395726400218825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11120961379194301866958433 8340721034395726400218825)
        ·
          refine ⟨6255540775796794800164119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8340721034395726400218825 6255540775796794800164119)
          ·
            refine ⟨9383311163695192200246179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6255540775796794800164119 9383311163695192200246179)
            ·
              refine ⟨14074966745542788300369269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9383311163695192200246179 14074966745542788300369269)
              ·
                refine ⟨1319528132394636403159619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14074966745542788300369269 1319528132394636403159619)
                ·
                  refine ⟨1979292198591954604739429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319528132394636403159619 1979292198591954604739429)
                  ·
                    refine ⟨371117287235991488388643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1979292198591954604739429 371117287235991488388643)
                    ·
                      rfl

theorem cell23_2168245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2168245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168245 prefixEnd_2168245 := by exact prefixLift 2168245
  have htrace : WordTrace (prefixWord ++ tailWord_2168245) baseStart_2168245 baseEnd_2168245 := by
    simpa [prefixWord, tailWord_2168245, baseEnd_2168245] using wordTrace_append hprefix tailTrace_2168245
  have hstable : (prefixWord ++ tailWord_2168245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168245).length < 2 ^ (prefixWord ++ tailWord_2168245).sum := by decide
  have hdescent : baseEnd_2168245 < baseStart_2168245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168285 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2168285 : Nat := 118140960795 + 2168285 * 2 ^ 59
def prefixEnd_2168285 : Nat := 4983230072969 + 3 ^ 40 * 2168285 * 2
def baseEnd_2168285 : Nat := 1113372400934154308665745

theorem tailTrace_2168285 : CollatzResearch.WordTrace tailWord_2168285 prefixEnd_2168285 1113372400934154308665745 := by
  unfold tailWord_2168285
  simp only [CollatzResearch.WordTrace]
  refine ⟨79083850949681233440938309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52722567299787488960625539 79083850949681233440938309)
  ·
    refine ⟨14828222053065231270175933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79083850949681233440938309 14828222053065231270175933)
    ·
      refine ⟨5560583269899461726315975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14828222053065231270175933 5560583269899461726315975)
      ·
        refine ⟨8340874904849192589473963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560583269899461726315975 8340874904849192589473963)
        ·
          refine ⟨12511312357273788884210945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8340874904849192589473963 12511312357273788884210945)
          ·
            refine ⟨9383484267955341663158209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12511312357273788884210945 9383484267955341663158209)
            ·
              refine ⟨7037613200966506247368657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9383484267955341663158209 7037613200966506247368657)
              ·
                refine ⟨5278209900724879685526493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7037613200966506247368657 5278209900724879685526493)
                ·
                  refine ⟨1979328712771829882072435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5278209900724879685526493 1979328712771829882072435)
                  ·
                    refine ⟨2968993069157744823108653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979328712771829882072435 2968993069157744823108653)
                    ·
                      refine ⟨1113372400934154308665745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2968993069157744823108653 1113372400934154308665745)
                      ·
                        rfl

theorem cell23_2168285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2168285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168285 prefixEnd_2168285 := by exact prefixLift 2168285
  have htrace : WordTrace (prefixWord ++ tailWord_2168285) baseStart_2168285 baseEnd_2168285 := by
    simpa [prefixWord, tailWord_2168285, baseEnd_2168285] using wordTrace_append hprefix tailTrace_2168285
  have hstable : (prefixWord ++ tailWord_2168285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168285).length < 2 ^ (prefixWord ++ tailWord_2168285).sum := by decide
  have hdescent : baseEnd_2168285 < baseStart_2168285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168326 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2168326 : Nat := 118140960795 + 2168326 * 2 ^ 59
def prefixEnd_2168326 : Nat := 4983230072969 + 3 ^ 40 * 2168326 * 2
def baseEnd_2168326 : Nat := 123710383737887627583673

theorem tailTrace_2168326 : CollatzResearch.WordTrace tailWord_2168326 prefixEnd_2168326 123710383737887627583673 := by
  unfold tailWord_2168326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471417073204146795099401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52723564228355131628787221 2471417073204146795099401)
  ·
    refine ⟨1853562804903110096324551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2471417073204146795099401 1853562804903110096324551)
    ·
      refine ⟨2780344207354665144486827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853562804903110096324551 2780344207354665144486827)
      ·
        refine ⟨4170516311031997716730241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780344207354665144486827 4170516311031997716730241)
        ·
          refine ⟨3127887233273998287547681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4170516311031997716730241 3127887233273998287547681)
          ·
            refine ⟨2345915424955498715660761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127887233273998287547681 2345915424955498715660761)
            ·
              refine ⟨1759436568716624036745571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345915424955498715660761 1759436568716624036745571)
              ·
                refine ⟨2639154853074936055118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759436568716624036745571 2639154853074936055118357)
                ·
                  refine ⟨123710383737887627583673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2639154853074936055118357 123710383737887627583673)
                  ·
                    rfl

theorem cell23_2168326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2168326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168326 prefixEnd_2168326 := by exact prefixLift 2168326
  have htrace : WordTrace (prefixWord ++ tailWord_2168326) baseStart_2168326 baseEnd_2168326 := by
    simpa [prefixWord, tailWord_2168326, baseEnd_2168326] using wordTrace_append hprefix tailTrace_2168326
  have hstable : (prefixWord ++ tailWord_2168326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168326).length < 2 ^ (prefixWord ++ tailWord_2168326).sum := by decide
  have hdescent : baseEnd_2168326 < baseStart_2168326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168362 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2168362 : Nat := 118140960795 + 2168362 * 2 ^ 59
def prefixEnd_2168362 : Nat := 4983230072969 + 3 ^ 40 * 2168362 * 2
def baseEnd_2168362 : Nat := 1113411938944550507402891

theorem tailTrace_2168362 : CollatzResearch.WordTrace tailWord_2168362 prefixEnd_2168362 1113411938944550507402891 := by
  unfold tailWord_2168362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19771664842600568897872835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52724439580268183727660893 19771664842600568897872835)
  ·
    refine ⟨29657497263900853346809253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19771664842600568897872835 29657497263900853346809253)
    ·
      refine ⟨5560780736981410002526735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29657497263900853346809253 5560780736981410002526735)
      ·
        refine ⟨8341171105472115003790103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560780736981410002526735 8341171105472115003790103)
        ·
          refine ⟨12511756658208172505685155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8341171105472115003790103 12511756658208172505685155)
          ·
            refine ⟨18767634987312258758527733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12511756658208172505685155 18767634987312258758527733)
            ·
              refine ⟨1759465780060524258611975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18767634987312258758527733 1759465780060524258611975)
              ·
                refine ⟨2639198670090786387917963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759465780060524258611975 2639198670090786387917963)
                ·
                  refine ⟨3958798005136179581876945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639198670090786387917963 3958798005136179581876945)
                  ·
                    refine ⟨2969098503852134686407709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3958798005136179581876945 2969098503852134686407709)
                    ·
                      refine ⟨1113411938944550507402891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969098503852134686407709 1113411938944550507402891)
                      ·
                        rfl

theorem cell23_2168362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2168362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168362 prefixEnd_2168362 := by exact prefixLift 2168362
  have htrace : WordTrace (prefixWord ++ tailWord_2168362) baseStart_2168362 baseEnd_2168362 := by
    simpa [prefixWord, tailWord_2168362, baseEnd_2168362] using wordTrace_append hprefix tailTrace_2168362
  have hstable : (prefixWord ++ tailWord_2168362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168362).length < 2 ^ (prefixWord ++ tailWord_2168362).sum := by decide
  have hdescent : baseEnd_2168362 < baseStart_2168362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168375 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_2168375 : Nat := 118140960795 + 2168375 * 2 ^ 59
def prefixEnd_2168375 : Nat := 4983230072969 + 3 ^ 40 * 2168375 * 2
def baseEnd_2168375 : Nat := 1113418614193058956540331

theorem tailTrace_2168375 : CollatzResearch.WordTrace tailWord_2168375 prefixEnd_2168375 1113418614193058956540331 := by
  unfold tailWord_2168375
  simp only [CollatzResearch.WordTrace]
  refine ⟨79087133519355178811714579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52724755679570119207809719 79087133519355178811714579)
  ·
    refine ⟨118630700279032768217571869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79087133519355178811714579 118630700279032768217571869)
    ·
      refine ⟨44486512604637288081589451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118630700279032768217571869 44486512604637288081589451)
      ·
        refine ⟨66729768906955932122384177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44486512604637288081589451 66729768906955932122384177)
        ·
          refine ⟨50047326680216949091788133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66729768906955932122384177 50047326680216949091788133)
          ·
            refine ⟨9383873752540677954710275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50047326680216949091788133 9383873752540677954710275)
            ·
              refine ⟨14075810628811016932065413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9383873752540677954710275 14075810628811016932065413)
              ·
                refine ⟨2639214492902065674762265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14075810628811016932065413 2639214492902065674762265)
                ·
                  refine ⟨1979410869676549256071699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2639214492902065674762265 1979410869676549256071699)
                  ·
                    refine ⟨2969116304514823884107549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979410869676549256071699 2969116304514823884107549)
                    ·
                      refine ⟨1113418614193058956540331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969116304514823884107549 1113418614193058956540331)
                      ·
                        rfl

theorem cell23_2168375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_2168375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168375 prefixEnd_2168375 := by exact prefixLift 2168375
  have htrace : WordTrace (prefixWord ++ tailWord_2168375) baseStart_2168375 baseEnd_2168375 := by
    simpa [prefixWord, tailWord_2168375, baseEnd_2168375] using wordTrace_append hprefix tailTrace_2168375
  have hstable : (prefixWord ++ tailWord_2168375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168375).length < 2 ^ (prefixWord ++ tailWord_2168375).sum := by decide
  have hdescent : baseEnd_2168375 < baseStart_2168375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168376 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 1, 2, 2]
def baseStart_2168376 : Nat := 118140960795 + 2168376 * 2 ^ 59
def prefixEnd_2168376 : Nat := 4983230072969 + 3 ^ 40 * 2168376 * 2
def baseEnd_2168376 : Nat := 1113419127673713452627827

theorem tailTrace_2168376 : CollatzResearch.WordTrace tailWord_2168376 prefixEnd_2168376 1113419127673713452627827 := by
  unfold tailWord_2168376
  simp only [CollatzResearch.WordTrace]
  refine ⟨39543584996175777991250491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52724779994901037321667321 39543584996175777991250491)
  ·
    refine ⟨59315377494263666986875737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39543584996175777991250491 59315377494263666986875737)
    ·
      refine ⟨44486533120697750240156803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59315377494263666986875737 44486533120697750240156803)
      ·
        refine ⟨66729799681046625360235205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44486533120697750240156803 66729799681046625360235205)
        ·
          refine ⟨12511837440196242255044101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66729799681046625360235205 12511837440196242255044101)
          ·
            refine ⟨2345969520036795422820769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12511837440196242255044101 2345969520036795422820769)
            ·
              refine ⟨1759477140027596567115577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345969520036795422820769 1759477140027596567115577)
              ·
                refine ⟨1319607855020697425336683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1759477140027596567115577 1319607855020697425336683)
                ·
                  refine ⟨1979411782531046138005025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319607855020697425336683 1979411782531046138005025)
                  ·
                    refine ⟨1484558836898284603503769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979411782531046138005025 1484558836898284603503769)
                    ·
                      refine ⟨1113419127673713452627827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484558836898284603503769 1113419127673713452627827)
                      ·
                        rfl

theorem cell23_2168376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_2168376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168376 prefixEnd_2168376 := by exact prefixLift 2168376
  have htrace : WordTrace (prefixWord ++ tailWord_2168376) baseStart_2168376 baseEnd_2168376 := by
    simpa [prefixWord, tailWord_2168376, baseEnd_2168376] using wordTrace_append hprefix tailTrace_2168376
  have hstable : (prefixWord ++ tailWord_2168376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168376).length < 2 ^ (prefixWord ++ tailWord_2168376).sum := by decide
  have hdescent : baseEnd_2168376 < baseStart_2168376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168385 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2168385 : Nat := 118140960795 + 2168385 * 2 ^ 59
def prefixEnd_2168385 : Nat := 4983230072969 + 3 ^ 40 * 2168385 * 2
def baseEnd_2168385 : Nat := 1113423748999603917415285

theorem tailTrace_2168385 : CollatzResearch.WordTrace tailWord_2168385 prefixEnd_2168385 1113423748999603917415285 := by
  unfold tailWord_2168385
  simp only [CollatzResearch.WordTrace]
  refine ⟨79087498249318950519578609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52724998832879300346385739 79087498249318950519578609)
  ·
    refine ⟨59315623686989212889683957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79087498249318950519578609 59315623686989212889683957)
    ·
      refine ⟨5560839720655238708407871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59315623686989212889683957 5560839720655238708407871)
      ·
        refine ⟨8341259580982858062611807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560839720655238708407871 8341259580982858062611807)
        ·
          refine ⟨12511889371474287093917711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8341259580982858062611807 12511889371474287093917711)
          ·
            refine ⟨18767834057211430640876567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12511889371474287093917711 18767834057211430640876567)
            ·
              refine ⟨28151751085817145961314851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18767834057211430640876567 28151751085817145961314851)
              ·
                refine ⟨42227626628725718941972277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28151751085817145961314851 42227626628725718941972277)
                ·
                  refine ⟨3958839996443036150809901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42227626628725718941972277 3958839996443036150809901)
                  ·
                    refine ⟨1484564998666138556553713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3958839996443036150809901 1484564998666138556553713)
                    ·
                      refine ⟨1113423748999603917415285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484564998666138556553713 1113423748999603917415285)
                      ·
                        rfl

theorem cell23_2168385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2168385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168385 prefixEnd_2168385 := by exact prefixLift 2168385
  have htrace : WordTrace (prefixWord ++ tailWord_2168385) baseStart_2168385 baseEnd_2168385 := by
    simpa [prefixWord, tailWord_2168385, baseEnd_2168385] using wordTrace_append hprefix tailTrace_2168385
  have hstable : (prefixWord ++ tailWord_2168385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168385).length < 2 ^ (prefixWord ++ tailWord_2168385).sum := by decide
  have hdescent : baseEnd_2168385 < baseStart_2168385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168413 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2168413 : Nat := 118140960795 + 2168413 * 2 ^ 59
def prefixEnd_2168413 : Nat := 4983230072969 + 3 ^ 40 * 2168413 * 2
def baseEnd_2168413 : Nat := 1113438126457929807865157

theorem tailTrace_2168413 : CollatzResearch.WordTrace tailWord_2168413 prefixEnd_2168413 1113438126457929807865157 := by
  unfold tailWord_2168413
  simp only [CollatzResearch.WordTrace]
  refine ⟨79088519493217511301597893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52725679662145007534398595 79088519493217511301597893)
  ·
    refine ⟨14829097404978283369049605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79088519493217511301597893 14829097404978283369049605)
    ·
      refine ⟨2780455763433428131696801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14829097404978283369049605 2780455763433428131696801)
      ·
        refine ⟨2085341822575071098772601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2780455763433428131696801 2085341822575071098772601)
        ·
          refine ⟨1564006366931303324079451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2085341822575071098772601 1564006366931303324079451)
          ·
            refine ⟨2346009550396954986119177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564006366931303324079451 2346009550396954986119177)
            ·
              refine ⟨1759507162797716239589383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346009550396954986119177 1759507162797716239589383)
              ·
                refine ⟨2639260744196574359384075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759507162797716239589383 2639260744196574359384075)
                ·
                  refine ⟨3958891116294861539076113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639260744196574359384075 3958891116294861539076113)
                  ·
                    refine ⟨2969168337221146154307085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3958891116294861539076113 2969168337221146154307085)
                    ·
                      refine ⟨1113438126457929807865157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969168337221146154307085 1113438126457929807865157)
                      ·
                        rfl

theorem cell23_2168413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2168413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168413 prefixEnd_2168413 := by exact prefixLift 2168413
  have htrace : WordTrace (prefixWord ++ tailWord_2168413) baseStart_2168413 baseEnd_2168413 := by
    simpa [prefixWord, tailWord_2168413, baseEnd_2168413] using wordTrace_append hprefix tailTrace_2168413
  have hstable : (prefixWord ++ tailWord_2168413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168413).length < 2 ^ (prefixWord ++ tailWord_2168413).sum := by decide
  have hdescent : baseEnd_2168413 < baseStart_2168413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168419 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 1, 3, 2]
def baseStart_2168419 : Nat := 118140960795 + 2168419 * 2 ^ 59
def prefixEnd_2168419 : Nat := 4983230072969 + 3 ^ 40 * 2168419 * 2
def baseEnd_2168419 : Nat := 1113441207341856784390129

theorem tailTrace_2168419 : CollatzResearch.WordTrace tailWord_2168419 prefixEnd_2168419 1113441207341856784390129 := by
  unfold tailWord_2168419
  simp only [CollatzResearch.WordTrace]
  refine ⟨79088738331195774326316311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52725825554130516217544207 79088738331195774326316311)
  ·
    refine ⟨118633107496793661489474467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79088738331195774326316311 118633107496793661489474467)
    ·
      refine ⟨177949661245190492234211701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118633107496793661489474467 177949661245190492234211701)
      ·
        refine ⟨16682780741736608646957347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177949661245190492234211701 16682780741736608646957347)
        ·
          refine ⟨25024171112604912970436021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16682780741736608646957347 25024171112604912970436021)
          ·
            refine ⟨2346016041806710590978377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25024171112604912970436021 2346016041806710590978377)
            ·
              refine ⟨1759512031355032943233783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346016041806710590978377 1759512031355032943233783)
              ·
                refine ⟨2639268047032549414850675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759512031355032943233783 2639268047032549414850675)
                ·
                  refine ⟨3958902070548824122276013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639268047032549414850675 3958902070548824122276013)
                  ·
                    refine ⟨1484588276455809045853505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3958902070548824122276013 1484588276455809045853505)
                    ·
                      refine ⟨1113441207341856784390129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484588276455809045853505 1113441207341856784390129)
                      ·
                        rfl

theorem cell23_2168419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_2168419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168419 prefixEnd_2168419 := by exact prefixLift 2168419
  have htrace : WordTrace (prefixWord ++ tailWord_2168419) baseStart_2168419 baseEnd_2168419 := by
    simpa [prefixWord, tailWord_2168419, baseEnd_2168419] using wordTrace_append hprefix tailTrace_2168419
  have hstable : (prefixWord ++ tailWord_2168419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168419).length < 2 ^ (prefixWord ++ tailWord_2168419).sum := by decide
  have hdescent : baseEnd_2168419 < baseStart_2168419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168432 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 4, 2, 2]
def baseStart_2168432 : Nat := 118140960795 + 2168432 * 2 ^ 59
def prefixEnd_2168432 : Nat := 4983230072969 + 3 ^ 40 * 2168432 * 2
def baseEnd_2168432 : Nat := 1113447882590365233527569

theorem tailTrace_2168432 : CollatzResearch.WordTrace tailWord_2168432 prefixEnd_2168432 1113447882590365233527569 := by
  unfold tailWord_2168432
  simp only [CollatzResearch.WordTrace]
  refine ⟨39544606240074338773269775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52726141653432451697693033 39544606240074338773269775)
  ·
    refine ⟨59316909360111508159904663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39544606240074338773269775 59316909360111508159904663)
    ·
      refine ⟨88975364040167262239856995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59316909360111508159904663 88975364040167262239856995)
      ·
        refine ⟨133463046060250893359785493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88975364040167262239856995 133463046060250893359785493)
        ·
          refine ⟨6256080284074260626239945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133463046060250893359785493 6256080284074260626239945)
          ·
            refine ⟨4692060213055695469679959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6256080284074260626239945 4692060213055695469679959)
            ·
              refine ⟨7038090319583543204519939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4692060213055695469679959 7038090319583543204519939)
              ·
                refine ⟨10557135479375314806779909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7038090319583543204519939 10557135479375314806779909)
                ·
                  refine ⟨1979462902382871526271233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10557135479375314806779909 1979462902382871526271233)
                  ·
                    refine ⟨1484597176787153644703425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979462902382871526271233 1484597176787153644703425)
                    ·
                      refine ⟨1113447882590365233527569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484597176787153644703425 1113447882590365233527569)
                      ·
                        rfl

theorem cell23_2168432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 2, 2].length) (baseStart_2168432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168432 prefixEnd_2168432 := by exact prefixLift 2168432
  have htrace : WordTrace (prefixWord ++ tailWord_2168432) baseStart_2168432 baseEnd_2168432 := by
    simpa [prefixWord, tailWord_2168432, baseEnd_2168432] using wordTrace_append hprefix tailTrace_2168432
  have hstable : (prefixWord ++ tailWord_2168432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168432).length < 2 ^ (prefixWord ++ tailWord_2168432).sum := by decide
  have hdescent : baseEnd_2168432 < baseStart_2168432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168448 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_2168448 : Nat := 118140960795 + 2168448 * 2 ^ 59
def prefixEnd_2168448 : Nat := 4983230072969 + 3 ^ 40 * 2168448 * 2
def baseEnd_2168448 : Nat := 1113456098280837170927495

theorem tailTrace_2168448 : CollatzResearch.WordTrace tailWord_2168448 prefixEnd_2168448 1113456098280837170927495 := by
  unfold tailWord_2168448
  simp only [CollatzResearch.WordTrace]
  refine ⟨39544898024045356139560999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52726530698727141519414665 39544898024045356139560999)
  ·
    refine ⟨59317347036068034209341499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39544898024045356139560999 59317347036068034209341499)
    ·
      refine ⟨88976020554102051314012249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59317347036068034209341499 88976020554102051314012249)
      ·
        refine ⟨66732015415576538485509187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88976020554102051314012249 66732015415576538485509187)
        ·
          refine ⟨100098023123364807728263781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66732015415576538485509187 100098023123364807728263781)
          ·
            refine ⟨18768379335630901449049459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100098023123364807728263781 18768379335630901449049459)
            ·
              refine ⟨28152569003446352173574189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18768379335630901449049459 28152569003446352173574189)
              ·
                refine ⟨10557213376292382065090321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28152569003446352173574189 10557213376292382065090321)
                ·
                  refine ⟨7917910032219286548817741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10557213376292382065090321 7917910032219286548817741)
                  ·
                    refine ⟨2969216262082232455806653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7917910032219286548817741 2969216262082232455806653)
                    ·
                      refine ⟨1113456098280837170927495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969216262082232455806653 1113456098280837170927495)
                      ·
                        rfl

theorem cell23_2168448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_2168448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168448 prefixEnd_2168448 := by exact prefixLift 2168448
  have htrace : WordTrace (prefixWord ++ tailWord_2168448) baseStart_2168448 baseEnd_2168448 := by
    simpa [prefixWord, tailWord_2168448, baseEnd_2168448] using wordTrace_append hprefix tailTrace_2168448
  have hstable : (prefixWord ++ tailWord_2168448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168448).length < 2 ^ (prefixWord ++ tailWord_2168448).sum := by decide
  have hdescent : baseEnd_2168448 < baseStart_2168448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168472 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 5]
def baseStart_2168472 : Nat := 118140960795 + 2168472 * 2 ^ 59
def prefixEnd_2168472 : Nat := 4983230072969 + 3 ^ 40 * 2168472 * 2
def baseEnd_2168472 : Nat := 123718713535171675225265

theorem tailTrace_2168472 : CollatzResearch.WordTrace tailWord_2168472 prefixEnd_2168472 123718713535171675225265 := by
  unfold tailWord_2168472
  simp only [CollatzResearch.WordTrace]
  refine ⟨39545335700001882188997835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52727114266669176251997113 39545335700001882188997835)
  ·
    refine ⟨59318003550002823283496753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39545335700001882188997835 59318003550002823283496753)
    ·
      refine ⟨44488502662502117462622565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59318003550002823283496753 44488502662502117462622565)
      ·
        refine ⟨8341594249219147024241731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44488502662502117462622565 8341594249219147024241731)
        ·
          refine ⟨12512391373828720536362597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8341594249219147024241731 12512391373828720536362597)
          ·
            refine ⟨2346073382592885100567987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12512391373828720536362597 2346073382592885100567987)
            ·
              refine ⟨3519110073889327650851981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346073382592885100567987 3519110073889327650851981)
              ·
                refine ⟨1319666277708497869069493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3519110073889327650851981 1319666277708497869069493)
                ·
                  refine ⟨123718713535171675225265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1319666277708497869069493 123718713535171675225265)
                  ·
                    rfl

theorem cell23_2168472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 5].length) (baseStart_2168472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168472 prefixEnd_2168472 := by exact prefixLift 2168472
  have htrace : WordTrace (prefixWord ++ tailWord_2168472) baseStart_2168472 baseEnd_2168472 := by
    simpa [prefixWord, tailWord_2168472, baseEnd_2168472] using wordTrace_append hprefix tailTrace_2168472
  have hstable : (prefixWord ++ tailWord_2168472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168472).length < 2 ^ (prefixWord ++ tailWord_2168472).sum := by decide
  have hdescent : baseEnd_2168472 < baseStart_2168472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168505 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 2, 4, 2]
def baseStart_2168505 : Nat := 118140960795 + 2168505 * 2 ^ 59
def prefixEnd_2168505 : Nat := 4983230072969 + 3 ^ 40 * 2168505 * 2
def baseEnd_2168505 : Nat := 1113485366678143447914733

theorem tailTrace_2168505 : CollatzResearch.WordTrace tailWord_2168505 prefixEnd_2168505 1113485366678143447914733 := by
  unfold tailWord_2168505
  simp only [CollatzResearch.WordTrace]
  refine ⟨79091875008884211013946969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52727916672589474009297979 79091875008884211013946969)
  ·
    refine ⟨59318906256663158260460227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79091875008884211013946969 59318906256663158260460227)
    ·
      refine ⟨88978359384994737390690341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59318906256663158260460227 88978359384994737390690341)
      ·
        refine ⟨16683442384686513260754439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88978359384994737390690341 16683442384686513260754439)
        ·
          refine ⟨25025163577029769891131659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16683442384686513260754439 25025163577029769891131659)
          ·
            refine ⟨37537745365544654836697489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25025163577029769891131659 37537745365544654836697489)
            ·
              refine ⟨28153309024158491127523117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37537745365544654836697489 28153309024158491127523117)
              ·
                refine ⟨10557490884059434172821169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28153309024158491127523117 10557490884059434172821169)
                ·
                  refine ⟨7918118163044575629615877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10557490884059434172821169 7918118163044575629615877)
                  ·
                    refine ⟨1484647155570857930552977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7918118163044575629615877 1484647155570857930552977)
                    ·
                      refine ⟨1113485366678143447914733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484647155570857930552977 1113485366678143447914733)
                      ·
                        rfl

theorem cell23_2168505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_2168505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168505 prefixEnd_2168505 := by exact prefixLift 2168505
  have htrace : WordTrace (prefixWord ++ tailWord_2168505) baseStart_2168505 baseEnd_2168505 := by
    simpa [prefixWord, tailWord_2168505, baseEnd_2168505] using wordTrace_append hprefix tailTrace_2168505
  have hstable : (prefixWord ++ tailWord_2168505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168505).length < 2 ^ (prefixWord ++ tailWord_2168505).sum := by decide
  have hdescent : baseEnd_2168505 < baseStart_2168505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168522 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_2168522 : Nat := 118140960795 + 2168522 * 2 ^ 59
def prefixEnd_2168522 : Nat := 4983230072969 + 3 ^ 40 * 2168522 * 2
def baseEnd_2168522 : Nat := 1113494095849269881402155

theorem tailTrace_2168522 : CollatzResearch.WordTrace tailWord_2168522 prefixEnd_2168522 1113494095849269881402155 := by
  unfold tailWord_2168522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19773123762455655729328955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52728330033215081944877213 19773123762455655729328955)
  ·
    refine ⟨29659685643683483593993433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19773123762455655729328955 29659685643683483593993433)
    ·
      refine ⟨22244764232762612695495075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29659685643683483593993433 22244764232762612695495075)
      ·
        refine ⟨33367146349143919043242613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22244764232762612695495075 33367146349143919043242613)
        ·
          refine ⟨3128169970232242410303995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33367146349143919043242613 3128169970232242410303995)
          ·
            refine ⟨4692254955348363615455993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128169970232242410303995 4692254955348363615455993)
            ·
              refine ⟨3519191216511272711591995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4692254955348363615455993 3519191216511272711591995)
              ·
                refine ⟨5278786824766909067387993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519191216511272711591995 5278786824766909067387993)
                ·
                  refine ⟨3959090118575181800540995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5278786824766909067387993 3959090118575181800540995)
                  ·
                    refine ⟨5938635177862772700811493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3959090118575181800540995 5938635177862772700811493)
                    ·
                      refine ⟨1113494095849269881402155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5938635177862772700811493 1113494095849269881402155)
                      ·
                        rfl

theorem cell23_2168522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_2168522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168522 prefixEnd_2168522 := by exact prefixLift 2168522
  have htrace : WordTrace (prefixWord ++ tailWord_2168522) baseStart_2168522 baseEnd_2168522 := by
    simpa [prefixWord, tailWord_2168522, baseEnd_2168522] using wordTrace_append hprefix tailTrace_2168522
  have hstable : (prefixWord ++ tailWord_2168522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168522).length < 2 ^ (prefixWord ++ tailWord_2168522).sum := by decide
  have hdescent : baseEnd_2168522 < baseStart_2168522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168548 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_2168548 : Nat := 118140960795 + 2168548 * 2 ^ 59
def prefixEnd_2168548 : Nat := 4983230072969 + 3 ^ 40 * 2168548 * 2
def baseEnd_2168548 : Nat := 1113507446346286779677035

theorem tailTrace_2168548 : CollatzResearch.WordTrace tailWord_2168548 prefixEnd_2168548 1113507446346286779677035 := by
  unfold tailWord_2168548
  simp only [CollatzResearch.WordTrace]
  refine ⟨39546721673864214678881149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52728962231818952905174865 39546721673864214678881149)
  ·
    refine ⟨14830020627699080504580431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39546721673864214678881149 14830020627699080504580431)
    ·
      refine ⟨22245030941548620756870647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14830020627699080504580431 22245030941548620756870647)
      ·
        refine ⟨33367546412322931135305971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22245030941548620756870647 33367546412322931135305971)
        ·
          refine ⟨50051319618484396702958957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33367546412322931135305971 50051319618484396702958957)
          ·
            refine ⟨18769244856931648763609609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50051319618484396702958957 18769244856931648763609609)
            ·
              refine ⟨14076933642698736572707207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18769244856931648763609609 14076933642698736572707207)
              ·
                refine ⟨21115400464048104859060811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14076933642698736572707207 21115400464048104859060811)
                ·
                  refine ⟨31673100696072157288591217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21115400464048104859060811 31673100696072157288591217)
                  ·
                    refine ⟨23754825522054117966443413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31673100696072157288591217 23754825522054117966443413)
                    ·
                      refine ⟨1113507446346286779677035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23754825522054117966443413 1113507446346286779677035)
                      ·
                        rfl

theorem cell23_2168548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_2168548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168548 prefixEnd_2168548 := by exact prefixLift 2168548
  have htrace : WordTrace (prefixWord ++ tailWord_2168548) baseStart_2168548 baseEnd_2168548 := by
    simpa [prefixWord, tailWord_2168548, baseEnd_2168548] using wordTrace_append hprefix tailTrace_2168548
  have hstable : (prefixWord ++ tailWord_2168548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168548).length < 2 ^ (prefixWord ++ tailWord_2168548).sum := by decide
  have hdescent : baseEnd_2168548 < baseStart_2168548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168572 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_2168572 : Nat := 118140960795 + 2168572 * 2 ^ 59
def prefixEnd_2168572 : Nat := 4983230072969 + 3 ^ 40 * 2168572 * 2
def baseEnd_2168572 : Nat := 1113519769881994685776925

theorem tailTrace_2168572 : CollatzResearch.WordTrace tailWord_2168572 prefixEnd_2168572 1113519769881994685776925 := by
  unfold tailWord_2168572
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547159349820740728317985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52729545799760987637757313 39547159349820740728317985)
  ·
    refine ⟨29660369512365555546238489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39547159349820740728317985 29660369512365555546238489)
    ·
      refine ⟨22245277134274166659678867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29660369512365555546238489 22245277134274166659678867)
      ·
        refine ⟨33367915701411249989518301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22245277134274166659678867 33367915701411249989518301)
        ·
          refine ⟨12512968388029218746069363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33367915701411249989518301 12512968388029218746069363)
          ·
            refine ⟨18769452582043828119104045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12512968388029218746069363 18769452582043828119104045)
            ·
              refine ⟨7038544718266435544664017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18769452582043828119104045 7038544718266435544664017)
              ·
                refine ⟨5278908538699826658498013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7038544718266435544664017 5278908538699826658498013)
                ·
                  refine ⟨1979590702012434996936755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5278908538699826658498013 1979590702012434996936755)
                  ·
                    refine ⟨2969386053018652495405133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979590702012434996936755 2969386053018652495405133)
                    ·
                      refine ⟨1113519769881994685776925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969386053018652495405133 1113519769881994685776925)
                      ·
                        rfl

theorem cell23_2168572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_2168572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168572 prefixEnd_2168572 := by exact prefixLift 2168572
  have htrace : WordTrace (prefixWord ++ tailWord_2168572) baseStart_2168572 baseEnd_2168572 := by
    simpa [prefixWord, tailWord_2168572, baseEnd_2168572] using wordTrace_append hprefix tailTrace_2168572
  have hstable : (prefixWord ++ tailWord_2168572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168572).length < 2 ^ (prefixWord ++ tailWord_2168572).sum := by decide
  have hdescent : baseEnd_2168572 < baseStart_2168572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168625 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2168625 : Nat := 118140960795 + 2168625 * 2 ^ 59
def prefixEnd_2168625 : Nat := 4983230072969 + 3 ^ 40 * 2168625 * 2
def baseEnd_2168625 : Nat := 1113546984356682978414181

theorem tailTrace_2168625 : CollatzResearch.WordTrace tailWord_2168625 prefixEnd_2168625 1113546984356682978414181 := by
  unfold tailWord_2168625
  simp only [CollatzResearch.WordTrace]
  refine ⟨79096251768449471508315329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52730834512299647672210219 79096251768449471508315329)
  ·
    refine ⟨59322188826337103631236497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79096251768449471508315329 59322188826337103631236497)
    ·
      refine ⟨44491641619752827723427373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59322188826337103631236497 44491641619752827723427373)
      ·
        refine ⟨16684365607407310396285265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44491641619752827723427373 16684365607407310396285265)
        ·
          refine ⟨12513274205555482797213949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16684365607407310396285265 12513274205555482797213949)
          ·
            refine ⟨4692477827083306048955231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12513274205555482797213949 4692477827083306048955231)
            ·
              refine ⟨7038716740624959073432847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4692477827083306048955231 7038716740624959073432847)
              ·
                refine ⟨10558075110937438610149271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7038716740624959073432847 10558075110937438610149271)
                ·
                  refine ⟨15837112666406157915223907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10558075110937438610149271 15837112666406157915223907)
                  ·
                    refine ⟨23755668999609236872835861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15837112666406157915223907 23755668999609236872835861)
                    ·
                      refine ⟨1113546984356682978414181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23755668999609236872835861 1113546984356682978414181)
                      ·
                        rfl

theorem cell23_2168625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2168625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168625 prefixEnd_2168625 := by exact prefixLift 2168625
  have htrace : WordTrace (prefixWord ++ tailWord_2168625) baseStart_2168625 baseEnd_2168625 := by
    simpa [prefixWord, tailWord_2168625, baseEnd_2168625] using wordTrace_append hprefix tailTrace_2168625
  have hstable : (prefixWord ++ tailWord_2168625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168625).length < 2 ^ (prefixWord ++ tailWord_2168625).sum := by decide
  have hdescent : baseEnd_2168625 < baseStart_2168625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168629 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2168629 : Nat := 118140960795 + 2168629 * 2 ^ 59
def prefixEnd_2168629 : Nat := 4983230072969 + 3 ^ 40 * 2168629 * 2
def baseEnd_2168629 : Nat := 1113549038279300962764163

theorem tailTrace_2168629 : CollatzResearch.WordTrace tailWord_2168629 prefixEnd_2168629 1113549038279300962764163 := by
  unfold tailWord_2168629
  simp only [CollatzResearch.WordTrace]
  refine ⟨79096397660434980191460941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52730931773623320127640627 79096397660434980191460941)
  ·
    refine ⟨29661149122663117571797853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79096397660434980191460941 29661149122663117571797853)
    ·
      refine ⟨11122930920998669089424195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29661149122663117571797853 11122930920998669089424195)
      ·
        refine ⟨16684396381498003634136293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11122930920998669089424195 16684396381498003634136293)
        ·
          refine ⟨3128324321530875681400555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16684396381498003634136293 3128324321530875681400555)
          ·
            refine ⟨4692486482296313522100833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128324321530875681400555 4692486482296313522100833)
            ·
              refine ⟨3519364861722235141575625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4692486482296313522100833 3519364861722235141575625)
              ·
                refine ⟨2639523646291676356181719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519364861722235141575625 2639523646291676356181719)
                ·
                  refine ⟨3959285469437514534272579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639523646291676356181719 3959285469437514534272579)
                  ·
                    refine ⟨5938928204156271801408869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3959285469437514534272579 5938928204156271801408869)
                    ·
                      refine ⟨1113549038279300962764163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5938928204156271801408869 1113549038279300962764163)
                      ·
                        rfl

theorem cell23_2168629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2168629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168629 prefixEnd_2168629 := by exact prefixLift 2168629
  have htrace : WordTrace (prefixWord ++ tailWord_2168629) baseStart_2168629 baseEnd_2168629 := by
    simpa [prefixWord, tailWord_2168629, baseEnd_2168629] using wordTrace_append hprefix tailTrace_2168629
  have hstable : (prefixWord ++ tailWord_2168629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168629).length < 2 ^ (prefixWord ++ tailWord_2168629).sum := by decide
  have hdescent : baseEnd_2168629 < baseStart_2168629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168632 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_2168632 : Nat := 118140960795 + 2168632 * 2 ^ 59
def prefixEnd_2168632 : Nat := 4983230072969 + 3 ^ 40 * 2168632 * 2
def baseEnd_2168632 : Nat := 1113550578721264451026649

theorem tailTrace_2168632 : CollatzResearch.WordTrace tailWord_2168632 prefixEnd_2168632 1113550578721264451026649 := by
  unfold tailWord_2168632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39548253539712055851910075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52731004719616074469213433 39548253539712055851910075)
  ·
    refine ⟨59322380309568083777865113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39548253539712055851910075 59322380309568083777865113)
    ·
      refine ⟨44491785232176062833398835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59322380309568083777865113 44491785232176062833398835)
      ·
        refine ⟨66737677848264094250098253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44491785232176062833398835 66737677848264094250098253)
        ·
          refine ⟨25026629193099035343786845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66737677848264094250098253 25026629193099035343786845)
          ·
            refine ⟨9384985947412138253920067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25026629193099035343786845 9384985947412138253920067)
            ·
              refine ⟨14077478921118207380880101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9384985947412138253920067 14077478921118207380880101)
              ·
                refine ⟨2639527297709663883915019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14077478921118207380880101 2639527297709663883915019)
                ·
                  refine ⟨3959290946564495825872529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639527297709663883915019 3959290946564495825872529)
                  ·
                    refine ⟨2969468209923371869404397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3959290946564495825872529 2969468209923371869404397)
                    ·
                      refine ⟨1113550578721264451026649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969468209923371869404397 1113550578721264451026649)
                      ·
                        rfl

theorem cell23_2168632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_2168632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168632 prefixEnd_2168632 := by exact prefixLift 2168632
  have htrace : WordTrace (prefixWord ++ tailWord_2168632) baseStart_2168632 baseEnd_2168632 := by
    simpa [prefixWord, tailWord_2168632, baseEnd_2168632] using wordTrace_append hprefix tailTrace_2168632
  have hstable : (prefixWord ++ tailWord_2168632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168632).length < 2 ^ (prefixWord ++ tailWord_2168632).sum := by decide
  have hdescent : baseEnd_2168632 < baseStart_2168632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168645 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_2168645 : Nat := 118140960795 + 2168645 * 2 ^ 59
def prefixEnd_2168645 : Nat := 4983230072969 + 3 ^ 40 * 2168645 * 2
def baseEnd_2168645 : Nat := 1113557253969772900164089

theorem tailTrace_2168645 : CollatzResearch.WordTrace tailWord_2168645 prefixEnd_2168645 1113557253969772900164089 := by
  unfold tailWord_2168645
  simp only [CollatzResearch.WordTrace]
  refine ⟨79096981228377014924043389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52731320818918009949362259 79096981228377014924043389)
  ·
    refine ⟨29661367960641380596516271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79096981228377014924043389 29661367960641380596516271)
    ·
      refine ⟨44492051940962070894774407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29661367960641380596516271 44492051940962070894774407)
      ·
        refine ⟨66738077911443106342161611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44492051940962070894774407 66738077911443106342161611)
        ·
          refine ⟨100107116867164659513242417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66738077911443106342161611 100107116867164659513242417)
          ·
            refine ⟨75080337650373494634931813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100107116867164659513242417 75080337650373494634931813)
            ·
              refine ⟨14077563309445030244049715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75080337650373494634931813 14077563309445030244049715)
              ·
                refine ⟨21116344964167545366074573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14077563309445030244049715 21116344964167545366074573)
                ·
                  refine ⟨7918629361562829512277965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21116344964167545366074573 7918629361562829512277965)
                  ·
                    refine ⟨2969486010586061067104237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7918629361562829512277965 2969486010586061067104237)
                    ·
                      refine ⟨1113557253969772900164089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969486010586061067104237 1113557253969772900164089)
                      ·
                        rfl

theorem cell23_2168645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_2168645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168645 prefixEnd_2168645 := by exact prefixLift 2168645
  have htrace : WordTrace (prefixWord ++ tailWord_2168645) baseStart_2168645 baseEnd_2168645 := by
    simpa [prefixWord, tailWord_2168645, baseEnd_2168645] using wordTrace_append hprefix tailTrace_2168645
  have hstable : (prefixWord ++ tailWord_2168645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168645).length < 2 ^ (prefixWord ++ tailWord_2168645).sum := by decide
  have hdescent : baseEnd_2168645 < baseStart_2168645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168646 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2168646 : Nat := 118140960795 + 2168646 * 2 ^ 59
def prefixEnd_2168646 : Nat := 4983230072969 + 3 ^ 40 * 2168646 * 2
def baseEnd_2168646 : Nat := 1113557767450427396251585

theorem tailTrace_2168646 : CollatzResearch.WordTrace tailWord_2168646 prefixEnd_2168646 1113557767450427396251585 := by
  unfold tailWord_2168646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471781803167918502963431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52731345134248928063219861 2471781803167918502963431)
  ·
    refine ⟨3707672704751877754445147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2471781803167918502963431 3707672704751877754445147)
    ·
      refine ⟨5561509057127816631667721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3707672704751877754445147 5561509057127816631667721)
      ·
        refine ⟨4171131792845862473750791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5561509057127816631667721 4171131792845862473750791)
        ·
          refine ⟨6256697689268793710626187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171131792845862473750791 6256697689268793710626187)
          ·
            refine ⟨9385046533903190565939281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6256697689268793710626187 9385046533903190565939281)
            ·
              refine ⟨7038784900427392924454461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9385046533903190565939281 7038784900427392924454461)
              ·
                refine ⟨2639544337660272346670423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7038784900427392924454461 2639544337660272346670423)
                ·
                  refine ⟨3959316506490408520005635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639544337660272346670423 3959316506490408520005635)
                  ·
                    refine ⟨5938974759735612780008453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3959316506490408520005635 5938974759735612780008453)
                    ·
                      refine ⟨1113557767450427396251585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5938974759735612780008453 1113557767450427396251585)
                      ·
                        rfl

theorem cell23_2168646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2168646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168646 prefixEnd_2168646 := by exact prefixLift 2168646
  have htrace : WordTrace (prefixWord ++ tailWord_2168646) baseStart_2168646 baseEnd_2168646 := by
    simpa [prefixWord, tailWord_2168646, baseEnd_2168646] using wordTrace_append hprefix tailTrace_2168646
  have hstable : (prefixWord ++ tailWord_2168646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168646).length < 2 ^ (prefixWord ++ tailWord_2168646).sum := by decide
  have hdescent : baseEnd_2168646 < baseStart_2168646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168652 : List Nat := [2, 2, 1, 3, 5, 1, 9]
def baseStart_2168652 : Nat := 118140960795 + 2168652 * 2 ^ 59
def prefixEnd_2168652 : Nat := 4983230072969 + 3 ^ 40 * 2168652 * 2
def baseEnd_2168652 : Nat := 13747664794251288552797

theorem tailTrace_2168652 : CollatzResearch.WordTrace tailWord_2168652 prefixEnd_2168652 13747664794251288552797 := by
  unfold tailWord_2168652
  simp only [CollatzResearch.WordTrace]
  refine ⟨39548618269675827559774105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52731491026234436746365473 39548618269675827559774105)
  ·
    refine ⟨29661463702256870669830579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39548618269675827559774105 29661463702256870669830579)
    ·
      refine ⟨44492195553385306004745869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29661463702256870669830579 44492195553385306004745869)
      ·
        refine ⟨16684573332519489751779701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44492195553385306004745869 16684573332519489751779701)
        ·
          refine ⟨1564178749923702164229347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16684573332519489751779701 1564178749923702164229347)
          ·
            refine ⟨2346268124885553246344021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564178749923702164229347 2346268124885553246344021)
            ·
              refine ⟨13747664794251288552797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2346268124885553246344021 13747664794251288552797)
              ·
                rfl

theorem cell23_2168652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 9].length) (baseStart_2168652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168652 prefixEnd_2168652 := by exact prefixLift 2168652
  have htrace : WordTrace (prefixWord ++ tailWord_2168652) baseStart_2168652 baseEnd_2168652 := by
    simpa [prefixWord, tailWord_2168652, baseEnd_2168652] using wordTrace_append hprefix tailTrace_2168652
  have hstable : (prefixWord ++ tailWord_2168652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168652).length < 2 ^ (prefixWord ++ tailWord_2168652).sum := by decide
  have hdescent : baseEnd_2168652 < baseStart_2168652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168663 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 3, 2, 2]
def baseStart_2168663 : Nat := 118140960795 + 2168663 * 2 ^ 59
def prefixEnd_2168663 : Nat := 4983230072969 + 3 ^ 40 * 2168663 * 2
def baseEnd_2168663 : Nat := 1113566496621553829739007

theorem tailTrace_2168663 : CollatzResearch.WordTrace tailWord_2168663 prefixEnd_2168663 1113566496621553829739007 := by
  unfold tailWord_2168663
  simp only [CollatzResearch.WordTrace]
  refine ⟨79097637742311803998198643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52731758494874535998799095 79097637742311803998198643)
  ·
    refine ⟨118646456613467705997297965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79097637742311803998198643 118646456613467705997297965)
    ·
      refine ⟨44492421230050389748986737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118646456613467705997297965 44492421230050389748986737)
      ·
        refine ⟨33369315922537792311740053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44492421230050389748986737 33369315922537792311740053)
        ·
          refine ⟨1564186683868959014612815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33369315922537792311740053 1564186683868959014612815)
          ·
            refine ⟨2346280025803438521919223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564186683868959014612815 2346280025803438521919223)
            ·
              refine ⟨3519420038705157782878835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346280025803438521919223 3519420038705157782878835)
              ·
                refine ⟨5279130058057736674318253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519420038705157782878835 5279130058057736674318253)
                ·
                  refine ⟨1979673771771651252869345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5279130058057736674318253 1979673771771651252869345)
                  ·
                    refine ⟨1484755328828738439652009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979673771771651252869345 1484755328828738439652009)
                    ·
                      refine ⟨1113566496621553829739007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484755328828738439652009 1113566496621553829739007)
                      ·
                        rfl

theorem cell23_2168663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_2168663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168663 prefixEnd_2168663 := by exact prefixLift 2168663
  have htrace : WordTrace (prefixWord ++ tailWord_2168663) baseStart_2168663 baseEnd_2168663 := by
    simpa [prefixWord, tailWord_2168663, baseEnd_2168663] using wordTrace_append hprefix tailTrace_2168663
  have hstable : (prefixWord ++ tailWord_2168663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168663).length < 2 ^ (prefixWord ++ tailWord_2168663).sum := by decide
  have hdescent : baseEnd_2168663 < baseStart_2168663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168679 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2168679 : Nat := 118140960795 + 2168679 * 2 ^ 59
def prefixEnd_2168679 : Nat := 4983230072969 + 3 ^ 40 * 2168679 * 2
def baseEnd_2168679 : Nat := 1113574712312025767138933

theorem tailTrace_2168679 : CollatzResearch.WordTrace tailWord_2168679 prefixEnd_2168679 1113574712312025767138933 := by
  unfold tailWord_2168679
  simp only [CollatzResearch.WordTrace]
  refine ⟨79098221310253838730781091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52732147540169225820520727 79098221310253838730781091)
  ·
    refine ⟨118647331965380758096171637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79098221310253838730781091 118647331965380758096171637)
    ·
      refine ⟨11123187371754446071516091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118647331965380758096171637 11123187371754446071516091)
      ·
        refine ⟨16684781057631669107274137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11123187371754446071516091 16684781057631669107274137)
        ·
          refine ⟨12513585793223751830455603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16684781057631669107274137 12513585793223751830455603)
          ·
            refine ⟨18770378689835627745683405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12513585793223751830455603 18770378689835627745683405)
            ·
              refine ⟨7038892008688360404631277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18770378689835627745683405 7038892008688360404631277)
              ·
                refine ⟨2639584503258135151736729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7038892008688360404631277 2639584503258135151736729)
                ·
                  refine ⟨1979688377443601363802547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2639584503258135151736729 1979688377443601363802547)
                  ·
                    refine ⟨2969532566165402045703821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979688377443601363802547 2969532566165402045703821)
                    ·
                      refine ⟨1113574712312025767138933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969532566165402045703821 1113574712312025767138933)
                      ·
                        rfl

theorem cell23_2168679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2168679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168679 prefixEnd_2168679 := by exact prefixLift 2168679
  have htrace : WordTrace (prefixWord ++ tailWord_2168679) baseStart_2168679 baseEnd_2168679 := by
    simpa [prefixWord, tailWord_2168679, baseEnd_2168679] using wordTrace_append hprefix tailTrace_2168679
  have hstable : (prefixWord ++ tailWord_2168679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168679).length < 2 ^ (prefixWord ++ tailWord_2168679).sum := by decide
  have hdescent : baseEnd_2168679 < baseStart_2168679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168715 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4]
def baseStart_2168715 : Nat := 118140960795 + 2168715 * 2 ^ 59
def prefixEnd_2168715 : Nat := 4983230072969 + 3 ^ 40 * 2168715 * 2
def baseEnd_2168715 : Nat := 1113593197615587626288767

theorem tailTrace_2168715 : CollatzResearch.WordTrace tailWord_2168715 prefixEnd_2168715 1113593197615587626288767 := by
  unfold tailWord_2168715
  simp only [CollatzResearch.WordTrace]
  refine ⟨79099534338123416879091599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52733022892082277919394399 79099534338123416879091599)
  ·
    refine ⟨118649301507185125318637399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79099534338123416879091599 118649301507185125318637399)
    ·
      refine ⟨177973952260777687977956099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118649301507185125318637399 177973952260777687977956099)
      ·
        refine ⟨266960928391166531966934149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177973952260777687977956099 266960928391166531966934149)
        ·
          refine ⟨50055174073343724743800153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266960928391166531966934149 50055174073343724743800153)
          ·
            refine ⟨37541380555007793557850115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50055174073343724743800153 37541380555007793557850115)
            ·
              refine ⟨56312070832511690336775173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37541380555007793557850115 56312070832511690336775173)
              ·
                refine ⟨10558513281095941938145345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56312070832511690336775173 10558513281095941938145345)
                ·
                  refine ⟨7918884960821956453609009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10558513281095941938145345 7918884960821956453609009)
                  ·
                    refine ⟨5939163720616467340206757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7918884960821956453609009 5939163720616467340206757)
                    ·
                      refine ⟨1113593197615587626288767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5939163720616467340206757 1113593197615587626288767)
                      ·
                        rfl

theorem cell23_2168715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_2168715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168715 prefixEnd_2168715 := by exact prefixLift 2168715
  have htrace : WordTrace (prefixWord ++ tailWord_2168715) baseStart_2168715 baseEnd_2168715 := by
    simpa [prefixWord, tailWord_2168715, baseEnd_2168715] using wordTrace_append hprefix tailTrace_2168715
  have hstable : (prefixWord ++ tailWord_2168715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168715).length < 2 ^ (prefixWord ++ tailWord_2168715).sum := by decide
  have hdescent : baseEnd_2168715 < baseStart_2168715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168725 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 7]
def baseStart_2168725 : Nat := 118140960795 + 2168725 * 2 ^ 59
def prefixEnd_2168725 : Nat := 4983230072969 + 3 ^ 40 * 2168725 * 2
def baseEnd_2168725 : Nat := 123733148046903620795969

theorem tailTrace_2168725 : CollatzResearch.WordTrace tailWord_2168725 prefixEnd_2168725 123733148046903620795969 := by
  unfold tailWord_2168725
  simp only [CollatzResearch.WordTrace]
  refine ⟨79099899068087188586955629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52733266045391459057970419 79099899068087188586955629)
  ·
    refine ⟨29662462150532695720108361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79099899068087188586955629 29662462150532695720108361)
    ·
      refine ⟨22246846612899521790081271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29662462150532695720108361 22246846612899521790081271)
      ·
        refine ⟨33370269919349282685121907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22246846612899521790081271 33370269919349282685121907)
        ·
          refine ⟨50055404879023924027682861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33370269919349282685121907 50055404879023924027682861)
          ·
            refine ⟨18770776829633971510381073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50055404879023924027682861 18770776829633971510381073)
            ·
              refine ⟨14078082622225478632785805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18770776829633971510381073 14078082622225478632785805)
              ·
                refine ⟨5279280983334554487294677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14078082622225478632785805 5279280983334554487294677)
                ·
                  refine ⟨123733148046903620795969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5279280983334554487294677 123733148046903620795969)
                  ·
                    rfl

theorem cell23_2168725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_2168725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168725 prefixEnd_2168725 := by exact prefixLift 2168725
  have htrace : WordTrace (prefixWord ++ tailWord_2168725) baseStart_2168725 baseEnd_2168725 := by
    simpa [prefixWord, tailWord_2168725, baseEnd_2168725] using wordTrace_append hprefix tailTrace_2168725
  have hstable : (prefixWord ++ tailWord_2168725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168725).length < 2 ^ (prefixWord ++ tailWord_2168725).sum := by decide
  have hdescent : baseEnd_2168725 < baseStart_2168725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168732 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2168732 : Nat := 118140960795 + 2168732 * 2 ^ 59
def prefixEnd_2168732 : Nat := 4983230072969 + 3 ^ 40 * 2168732 * 2
def baseEnd_2168732 : Nat := 1113601926786714059776189

theorem tailTrace_2168732 : CollatzResearch.WordTrace tailWord_2168732 prefixEnd_2168732 1113601926786714059776189 := by
  unfold tailWord_2168732
  simp only [CollatzResearch.WordTrace]
  refine ⟨39550077189530914391230225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52733436252707885854973633 39550077189530914391230225)
  ·
    refine ⟨29662557892148185793422669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39550077189530914391230225 29662557892148185793422669)
    ·
      refine ⟨11123459209555569672533501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29662557892148185793422669 11123459209555569672533501)
      ·
        refine ⟨4171297203583338627200063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11123459209555569672533501 4171297203583338627200063)
        ·
          refine ⟨6256945805375007940800095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171297203583338627200063 6256945805375007940800095)
          ·
            refine ⟨9385418708062511911200143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6256945805375007940800095 9385418708062511911200143)
            ·
              refine ⟨14078128062093767866800215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9385418708062511911200143 14078128062093767866800215)
              ·
                refine ⟨21117192093140651800200323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14078128062093767866800215 21117192093140651800200323)
                ·
                  refine ⟨31675788139710977700300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21117192093140651800200323 31675788139710977700300485)
                  ·
                    refine ⟨5939210276195808318806341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31675788139710977700300485 5939210276195808318806341)
                    ·
                      refine ⟨1113601926786714059776189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5939210276195808318806341 1113601926786714059776189)
                      ·
                        rfl

theorem cell23_2168732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2168732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168732 prefixEnd_2168732 := by exact prefixLift 2168732
  have htrace : WordTrace (prefixWord ++ tailWord_2168732) baseStart_2168732 baseEnd_2168732 := by
    simpa [prefixWord, tailWord_2168732, baseEnd_2168732] using wordTrace_append hprefix tailTrace_2168732
  have hstable : (prefixWord ++ tailWord_2168732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168732).length < 2 ^ (prefixWord ++ tailWord_2168732).sum := by decide
  have hdescent : baseEnd_2168732 < baseStart_2168732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168755 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 1, 7]
def baseStart_2168755 : Nat := 118140960795 + 2168755 * 2 ^ 59
def prefixEnd_2168755 : Nat := 4983230072969 + 3 ^ 40 * 2168755 * 2
def baseEnd_2168755 : Nat := 371204578947255823262861

theorem tailTrace_2168755 : CollatzResearch.WordTrace tailWord_2168755 prefixEnd_2168755 371204578947255823262861 := by
  unfold tailWord_2168755
  simp only [CollatzResearch.WordTrace]
  refine ⟨79100993257978503710547719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52733995505319002473698479 79100993257978503710547719)
  ·
    refine ⟨118651489886967755565821579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79100993257978503710547719 118651489886967755565821579)
    ·
      refine ⟨177977234830451633348732369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118651489886967755565821579 177977234830451633348732369)
      ·
        refine ⟨133482926122838725011549277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177977234830451633348732369 133482926122838725011549277)
        ·
          refine ⟨50056097296064521879330979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133482926122838725011549277 50056097296064521879330979)
          ·
            refine ⟨75084145944096782818996469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50056097296064521879330979 75084145944096782818996469)
            ·
              refine ⟨7039138682259073389280919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75084145944096782818996469 7039138682259073389280919)
              ·
                refine ⟨10558708023388610083921379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7039138682259073389280919 10558708023388610083921379)
                ·
                  refine ⟨15838062035082915125882069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10558708023388610083921379 15838062035082915125882069)
                  ·
                    refine ⟨371204578947255823262861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15838062035082915125882069 371204578947255823262861)
                    ·
                      rfl

theorem cell23_2168755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 7].length) (baseStart_2168755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168755 prefixEnd_2168755 := by exact prefixLift 2168755
  have htrace : WordTrace (prefixWord ++ tailWord_2168755) baseStart_2168755 baseEnd_2168755 := by
    simpa [prefixWord, tailWord_2168755, baseEnd_2168755] using wordTrace_append hprefix tailTrace_2168755
  have hstable : (prefixWord ++ tailWord_2168755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168755).length < 2 ^ (prefixWord ++ tailWord_2168755).sum := by decide
  have hdescent : baseEnd_2168755 < baseStart_2168755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168762 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2]
def baseStart_2168762 : Nat := 118140960795 + 2168762 * 2 ^ 59
def prefixEnd_2168762 : Nat := 4983230072969 + 3 ^ 40 * 2168762 * 2
def baseEnd_2168762 : Nat := 1113617331206348942401051

theorem tailTrace_2168762 : CollatzResearch.WordTrace tailWord_2168762 prefixEnd_2168762 1113617331206348942401051 := by
  unfold tailWord_2168762
  simp only [CollatzResearch.WordTrace]
  refine ⟨19775312142238285976513135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52734165712635429270701693 19775312142238285976513135)
  ·
    refine ⟨29662968213357428964769703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19775312142238285976513135 29662968213357428964769703)
    ·
      refine ⟨44494452320036143447154555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29662968213357428964769703 44494452320036143447154555)
      ·
        refine ⟨66741678480054215170731833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44494452320036143447154555 66741678480054215170731833)
        ·
          refine ⟨50056258860040661378048875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66741678480054215170731833 50056258860040661378048875)
          ·
            refine ⟨75084388290060992067073313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50056258860040661378048875 75084388290060992067073313)
            ·
              refine ⟨56313291217545744050304985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75084388290060992067073313 56313291217545744050304985)
              ·
                refine ⟨42234968413159308037728739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56313291217545744050304985 42234968413159308037728739)
                ·
                  refine ⟨63352452619738962056593109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42234968413159308037728739 63352452619738962056593109)
                  ·
                    refine ⟨1484823108275131923201401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63352452619738962056593109 1484823108275131923201401)
                    ·
                      refine ⟨1113617331206348942401051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484823108275131923201401 1113617331206348942401051)
                      ·
                        rfl

theorem cell23_2168762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_2168762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168762 prefixEnd_2168762 := by exact prefixLift 2168762
  have htrace : WordTrace (prefixWord ++ tailWord_2168762) baseStart_2168762 baseEnd_2168762 := by
    simpa [prefixWord, tailWord_2168762, baseEnd_2168762] using wordTrace_append hprefix tailTrace_2168762
  have hstable : (prefixWord ++ tailWord_2168762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168762).length < 2 ^ (prefixWord ++ tailWord_2168762).sum := by decide
  have hdescent : baseEnd_2168762 < baseStart_2168762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168812 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_2168812 : Nat := 118140960795 + 2168812 * 2 ^ 59
def prefixEnd_2168812 : Nat := 4983230072969 + 3 ^ 40 * 2168812 * 2
def baseEnd_2168812 : Nat := 1113643005239073746775821

theorem tailTrace_2168812 : CollatzResearch.WordTrace tailWord_2168812 prefixEnd_2168812 1113643005239073746775821 := by
  unfold tailWord_2168812
  simp only [CollatzResearch.WordTrace]
  refine ⟨39551536109386001222686345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52735381479181334963581793 39551536109386001222686345)
  ·
    refine ⟨29663652082039500917014759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39551536109386001222686345 29663652082039500917014759)
    ·
      refine ⟨44495478123059251375522139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29663652082039500917014759 44495478123059251375522139)
      ·
        refine ⟨66743217184588877063283209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44495478123059251375522139 66743217184588877063283209)
        ·
          refine ⟨50057412888441657797462407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66743217184588877063283209 50057412888441657797462407)
          ·
            refine ⟨75086119332662486696193611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50057412888441657797462407 75086119332662486696193611)
            ·
              refine ⟨112629178998993730044290417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75086119332662486696193611 112629178998993730044290417)
              ·
                refine ⟨84471884249245297533217813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112629178998993730044290417 84471884249245297533217813)
                ·
                  refine ⟨3959619574183373321869585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84471884249245297533217813 3959619574183373321869585)
                  ·
                    refine ⟨2969714680637529991402189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3959619574183373321869585 2969714680637529991402189)
                    ·
                      refine ⟨1113643005239073746775821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969714680637529991402189 1113643005239073746775821)
                      ·
                        rfl

theorem cell23_2168812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_2168812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168812 prefixEnd_2168812 := by exact prefixLift 2168812
  have htrace : WordTrace (prefixWord ++ tailWord_2168812) baseStart_2168812 baseEnd_2168812 := by
    simpa [prefixWord, tailWord_2168812, baseEnd_2168812] using wordTrace_append hprefix tailTrace_2168812
  have hstable : (prefixWord ++ tailWord_2168812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168812).length < 2 ^ (prefixWord ++ tailWord_2168812).sum := by decide
  have hdescent : baseEnd_2168812 < baseStart_2168812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168815 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 10]
def baseStart_2168815 : Nat := 118140960795 + 2168815 * 2 ^ 59
def prefixEnd_2168815 : Nat := 4983230072969 + 3 ^ 40 * 2168815 * 2
def baseEnd_2168815 : Nat := 123738282853448581670923

theorem tailTrace_2168815 : CollatzResearch.WordTrace tailWord_2168815 prefixEnd_2168815 123738282853448581670923 := by
  unfold tailWord_2168815
  simp only [CollatzResearch.WordTrace]
  refine ⟨79103181637761133957731899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52735454425174089305154599 79103181637761133957731899)
  ·
    refine ⟨118654772456641700936597849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79103181637761133957731899 118654772456641700936597849)
    ·
      refine ⟨88991079342481275702448387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118654772456641700936597849 88991079342481275702448387)
      ·
        refine ⟨133486619013721913553672581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88991079342481275702448387 133486619013721913553672581)
        ·
          refine ⟨25028741065072858791313609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133486619013721913553672581 25028741065072858791313609)
          ·
            refine ⟨18771555798804644093485207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25028741065072858791313609 18771555798804644093485207)
            ·
              refine ⟨28157333698206966140227811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18771555798804644093485207 28157333698206966140227811)
              ·
                refine ⟨42236000547310449210341717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28157333698206966140227811 42236000547310449210341717)
                ·
                  refine ⟨123738282853448581670923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42236000547310449210341717 123738282853448581670923)
                  ·
                    rfl

theorem cell23_2168815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 10].length) (baseStart_2168815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168815 prefixEnd_2168815 := by exact prefixLift 2168815
  have htrace : WordTrace (prefixWord ++ tailWord_2168815) baseStart_2168815 baseEnd_2168815 := by
    simpa [prefixWord, tailWord_2168815, baseEnd_2168815] using wordTrace_append hprefix tailTrace_2168815
  have hstable : (prefixWord ++ tailWord_2168815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168815).length < 2 ^ (prefixWord ++ tailWord_2168815).sum := by decide
  have hdescent : baseEnd_2168815 < baseStart_2168815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168835 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_2168835 : Nat := 118140960795 + 2168835 * 2 ^ 59
def prefixEnd_2168835 : Nat := 4983230072969 + 3 ^ 40 * 2168835 * 2
def baseEnd_2168835 : Nat := 1113654815294127156788215

theorem tailTrace_2168835 : CollatzResearch.WordTrace tailWord_2168835 prefixEnd_2168835 1113654815294127156788215 := by
  unfold tailWord_2168835
  simp only [CollatzResearch.WordTrace]
  refine ⟨79103911097688677373459959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52735940731792451582306639 79103911097688677373459959)
  ·
    refine ⟨118655866646533016060189939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79103911097688677373459959 118655866646533016060189939)
    ·
      refine ⟨177983799969799524090284909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118655866646533016060189939 177983799969799524090284909)
      ·
        refine ⟨66743924988674821533856841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177983799969799524090284909 66743924988674821533856841)
        ·
          refine ⟨50057943741506116150392631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66743924988674821533856841 50057943741506116150392631)
          ·
            refine ⟨75086915612259174225588947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50057943741506116150392631 75086915612259174225588947)
            ·
              refine ⟨112630373418388761338383421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75086915612259174225588947 112630373418388761338383421)
              ·
                refine ⟨42236390031895785501893783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112630373418388761338383421 42236390031895785501893783)
                ·
                  refine ⟨63354585047843678252840675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42236390031895785501893783 63354585047843678252840675)
                  ·
                    refine ⟨95031877571765517379261013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63354585047843678252840675 95031877571765517379261013)
                    ·
                      refine ⟨1113654815294127156788215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 95031877571765517379261013 1113654815294127156788215)
                      ·
                        rfl

theorem cell23_2168835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_2168835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168835 prefixEnd_2168835 := by exact prefixLift 2168835
  have htrace : WordTrace (prefixWord ++ tailWord_2168835) baseStart_2168835 baseEnd_2168835 := by
    simpa [prefixWord, tailWord_2168835, baseEnd_2168835] using wordTrace_append hprefix tailTrace_2168835
  have hstable : (prefixWord ++ tailWord_2168835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168835).length < 2 ^ (prefixWord ++ tailWord_2168835).sum := by decide
  have hdescent : baseEnd_2168835 < baseStart_2168835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168838 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2168838 : Nat := 118140960795 + 2168838 * 2 ^ 59
def prefixEnd_2168838 : Nat := 4983230072969 + 3 ^ 40 * 2168838 * 2
def baseEnd_2168838 : Nat := 1113656355736090645050703

theorem tailTrace_2168838 : CollatzResearch.WordTrace tailWord_2168838 prefixEnd_2168838 1113656355736090645050703 := by
  unfold tailWord_2168838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472000641146181527681849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52736013677785205923879445 2472000641146181527681849)
  ·
    refine ⟨1854000480859636145761387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2472000641146181527681849 1854000480859636145761387)
    ·
      refine ⟨2781000721289454218642081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854000480859636145761387 2781000721289454218642081)
      ·
        refine ⟨2085750540967090663981561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2781000721289454218642081 2085750540967090663981561)
        ·
          refine ⟨1564312905725317997986171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2085750540967090663981561 1564312905725317997986171)
          ·
            refine ⟨2346469358587976996979257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564312905725317997986171 2346469358587976996979257)
            ·
              refine ⟨1759852018940982747734443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346469358587976996979257 1759852018940982747734443)
              ·
                refine ⟨2639778028411474121601665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759852018940982747734443 2639778028411474121601665)
                ·
                  refine ⟨1979833521308605591201249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2639778028411474121601665 1979833521308605591201249)
                  ·
                    refine ⟨1484875140981454193400937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979833521308605591201249 1484875140981454193400937)
                    ·
                      refine ⟨1113656355736090645050703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484875140981454193400937 1113656355736090645050703)
                      ·
                        rfl

theorem cell23_2168838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2168838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168838 prefixEnd_2168838 := by exact prefixLift 2168838
  have htrace : WordTrace (prefixWord ++ tailWord_2168838) baseStart_2168838 baseEnd_2168838 := by
    simpa [prefixWord, tailWord_2168838, baseEnd_2168838] using wordTrace_append hprefix tailTrace_2168838
  have hstable : (prefixWord ++ tailWord_2168838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168838).length < 2 ^ (prefixWord ++ tailWord_2168838).sum := by decide
  have hdescent : baseEnd_2168838 < baseStart_2168838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168892 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_2168892 : Nat := 118140960795 + 2168892 * 2 ^ 59
def prefixEnd_2168892 : Nat := 4983230072969 + 3 ^ 40 * 2168892 * 2
def baseEnd_2168892 : Nat := 371228027897144477925151

theorem tailTrace_2168892 : CollatzResearch.WordTrace tailWord_2168892 prefixEnd_2168892 371228027897144477925151 := by
  unfold tailWord_2168892
  simp only [CollatzResearch.WordTrace]
  refine ⟨39552995029241088054142465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52737326705654784072189953 39552995029241088054142465)
  ·
    refine ⟨29664746271930816040606849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39552995029241088054142465 29664746271930816040606849)
    ·
      refine ⟨22248559703948112030455137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29664746271930816040606849 22248559703948112030455137)
      ·
        refine ⟨16686419777961084022841353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22248559703948112030455137 16686419777961084022841353)
        ·
          refine ⟨12514814833470813017131015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16686419777961084022841353 12514814833470813017131015)
          ·
            refine ⟨18772222250206219525696523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514814833470813017131015 18772222250206219525696523)
            ·
              refine ⟨28158333375309329288544785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18772222250206219525696523 28158333375309329288544785)
              ·
                refine ⟨21118750031481996966408589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28158333375309329288544785 21118750031481996966408589)
                ·
                  refine ⟨7919531261805748862403221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21118750031481996966408589 7919531261805748862403221)
                  ·
                    refine ⟨371228027897144477925151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7919531261805748862403221 371228027897144477925151)
                    ·
                      rfl

theorem cell23_2168892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_2168892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168892 prefixEnd_2168892 := by exact prefixLift 2168892
  have htrace : WordTrace (prefixWord ++ tailWord_2168892) baseStart_2168892 baseEnd_2168892 := by
    simpa [prefixWord, tailWord_2168892, baseEnd_2168892] using wordTrace_append hprefix tailTrace_2168892
  have hstable : (prefixWord ++ tailWord_2168892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168892).length < 2 ^ (prefixWord ++ tailWord_2168892).sum := by decide
  have hdescent : baseEnd_2168892 < baseStart_2168892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168893 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_2168893 : Nat := 118140960795 + 2168893 * 2 ^ 59
def prefixEnd_2168893 : Nat := 4983230072969 + 3 ^ 40 * 2168893 * 2
def baseEnd_2168893 : Nat := 1113684597172087929862949

theorem tailTrace_2168893 : CollatzResearch.WordTrace tailWord_2168893 prefixEnd_2168893 1113684597172087929862949 := by
  unfold tailWord_2168893
  simp only [CollatzResearch.WordTrace]
  refine ⟨79106026531478553279071333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52737351020985702186047555 79106026531478553279071333)
  ·
    refine ⟨14832379974652228739825875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79106026531478553279071333 14832379974652228739825875)
    ·
      refine ⟨22248569961978343109738813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14832379974652228739825875 22248569961978343109738813)
      ·
        refine ⟨8343213735741878666152055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22248569961978343109738813 8343213735741878666152055)
        ·
          refine ⟨12514820603612817999228083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8343213735741878666152055 12514820603612817999228083)
          ·
            refine ⟨18772230905419226998842125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514820603612817999228083 18772230905419226998842125)
            ·
              refine ⟨7039586589532210124565797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18772230905419226998842125 7039586589532210124565797)
              ·
                refine ⟨1319922485537289398356087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7039586589532210124565797 1319922485537289398356087)
                ·
                  refine ⟨1979883728305934097534131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319922485537289398356087 1979883728305934097534131)
                  ·
                    refine ⟨2969825592458901146301197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979883728305934097534131 2969825592458901146301197)
                    ·
                      refine ⟨1113684597172087929862949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969825592458901146301197 1113684597172087929862949)
                      ·
                        rfl

theorem cell23_2168893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_2168893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168893 prefixEnd_2168893 := by exact prefixLift 2168893
  have htrace : WordTrace (prefixWord ++ tailWord_2168893) baseStart_2168893 baseEnd_2168893 := by
    simpa [prefixWord, tailWord_2168893, baseEnd_2168893] using wordTrace_append hprefix tailTrace_2168893
  have hstable : (prefixWord ++ tailWord_2168893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168893).length < 2 ^ (prefixWord ++ tailWord_2168893).sum := by decide
  have hdescent : baseEnd_2168893 < baseStart_2168893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168919 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_2168919 : Nat := 118140960795 + 2168919 * 2 ^ 59
def prefixEnd_2168919 : Nat := 4983230072969 + 3 ^ 40 * 2168919 * 2
def baseEnd_2168919 : Nat := 1113697947669104828137829

theorem tailTrace_2168919 : CollatzResearch.WordTrace tailWord_2168919 prefixEnd_2168919 1113697947669104828137829 := by
  unfold tailWord_2168919
  simp only [CollatzResearch.WordTrace]
  refine ⟨79106974829384359719517811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52737983219589573146345207 79106974829384359719517811)
  ·
    refine ⟨118660462244076539579276717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79106974829384359719517811 118660462244076539579276717)
    ·
      refine ⟨44497673341528702342228769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118660462244076539579276717 44497673341528702342228769)
      ·
        refine ⟨33373255006146526756671577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44497673341528702342228769 33373255006146526756671577)
        ·
          refine ⟨25029941254609895067503683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33373255006146526756671577 25029941254609895067503683)
          ·
            refine ⟨37544911881914842601255525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25029941254609895067503683 37544911881914842601255525)
            ·
              refine ⟨7039670977859032987735411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37544911881914842601255525 7039670977859032987735411)
              ·
                refine ⟨10559506466788549481603117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7039670977859032987735411 10559506466788549481603117)
                ·
                  refine ⟨3959814925045706055601169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10559506466788549481603117 3959814925045706055601169)
                  ·
                    refine ⟨2969861193784279541700877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3959814925045706055601169 2969861193784279541700877)
                    ·
                      refine ⟨1113697947669104828137829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2969861193784279541700877 1113697947669104828137829)
                      ·
                        rfl

theorem cell23_2168919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_2168919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168919 prefixEnd_2168919 := by exact prefixLift 2168919
  have htrace : WordTrace (prefixWord ++ tailWord_2168919) baseStart_2168919 baseEnd_2168919 := by
    simpa [prefixWord, tailWord_2168919, baseEnd_2168919] using wordTrace_append hprefix tailTrace_2168919
  have hstable : (prefixWord ++ tailWord_2168919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168919).length < 2 ^ (prefixWord ++ tailWord_2168919).sum := by decide
  have hdescent : baseEnd_2168919 < baseStart_2168919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168930 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2168930 : Nat := 118140960795 + 2168930 * 2 ^ 59
def prefixEnd_2168930 : Nat := 4983230072969 + 3 ^ 40 * 2168930 * 2
def baseEnd_2168930 : Nat := 371234531985434761700093

theorem tailTrace_2168930 : CollatzResearch.WordTrace tailWord_2168930 prefixEnd_2168930 371234531985434761700093 := by
  unfold tailWord_2168930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19776844008086127149542061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52738250688229672398778829 19776844008086127149542061)
  ·
    refine ⟨7416316503032297681078273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19776844008086127149542061 7416316503032297681078273)
    ·
      refine ⟨5562237377274223260808705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7416316503032297681078273 5562237377274223260808705)
      ·
        refine ⟨4171678032955667445606529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5562237377274223260808705 4171678032955667445606529)
        ·
          refine ⟨3128758524716750584204897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4171678032955667445606529 3128758524716750584204897)
          ·
            refine ⟨2346568893537562938153673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3128758524716750584204897 2346568893537562938153673)
            ·
              refine ⟨1759926670153172203615255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346568893537562938153673 1759926670153172203615255)
              ·
                refine ⟨2639890005229758305422883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759926670153172203615255 2639890005229758305422883)
                ·
                  refine ⟨3959835007844637458134325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639890005229758305422883 3959835007844637458134325)
                  ·
                    refine ⟨371234531985434761700093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3959835007844637458134325 371234531985434761700093)
                    ·
                      rfl

theorem cell23_2168930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2168930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168930 prefixEnd_2168930 := by exact prefixLift 2168930
  have htrace : WordTrace (prefixWord ++ tailWord_2168930) baseStart_2168930 baseEnd_2168930 := by
    simpa [prefixWord, tailWord_2168930, baseEnd_2168930] using wordTrace_append hprefix tailTrace_2168930
  have hstable : (prefixWord ++ tailWord_2168930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168930).length < 2 ^ (prefixWord ++ tailWord_2168930).sum := by decide
  have hdescent : baseEnd_2168930 < baseStart_2168930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168933 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 1, 1, 4]
def baseStart_2168933 : Nat := 118140960795 + 2168933 * 2 ^ 59
def prefixEnd_2168933 : Nat := 4983230072969 + 3 ^ 40 * 2168933 * 2
def baseEnd_2168933 : Nat := 1113705136398267773362765

theorem tailTrace_2168933 : CollatzResearch.WordTrace tailWord_2168933 prefixEnd_2168933 1113705136398267773362765 := by
  unfold tailWord_2168933
  simp only [CollatzResearch.WordTrace]
  refine ⟨79107485451333640110527453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52738323634222426740351635 79107485451333640110527453)
  ·
    refine ⟨29665307044250115041447795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79107485451333640110527453 29665307044250115041447795)
    ·
      refine ⟨44497960566375172562171693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29665307044250115041447795 44497960566375172562171693)
      ·
        refine ⟨16686735212390689710814385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44497960566375172562171693 16686735212390689710814385)
        ·
          refine ⟨12515051409293017283110789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16686735212390689710814385 12515051409293017283110789)
          ·
            refine ⟨2346572139242440740583273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12515051409293017283110789 2346572139242440740583273)
            ·
              refine ⟨1759929104431830555437455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346572139242440740583273 1759929104431830555437455)
              ·
                refine ⟨2639893656647745833156183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759929104431830555437455 2639893656647745833156183)
                ·
                  refine ⟨3959840484971618749734275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639893656647745833156183 3959840484971618749734275)
                  ·
                    refine ⟨5939760727457428124601413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3959840484971618749734275 5939760727457428124601413)
                    ·
                      refine ⟨1113705136398267773362765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5939760727457428124601413 1113705136398267773362765)
                      ·
                        rfl

theorem cell23_2168933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_2168933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168933 prefixEnd_2168933 := by exact prefixLift 2168933
  have htrace : WordTrace (prefixWord ++ tailWord_2168933) baseStart_2168933 baseEnd_2168933 := by
    simpa [prefixWord, tailWord_2168933, baseEnd_2168933] using wordTrace_append hprefix tailTrace_2168933
  have hstable : (prefixWord ++ tailWord_2168933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168933).length < 2 ^ (prefixWord ++ tailWord_2168933).sum := by decide
  have hdescent : baseEnd_2168933 < baseStart_2168933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168950 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2168950 : Nat := 118140960795 + 2168950 * 2 ^ 59
def prefixEnd_2168950 : Nat := 4983230072969 + 3 ^ 40 * 2168950 * 2
def baseEnd_2168950 : Nat := 1113713865569394206850187

theorem tailTrace_2168950 : CollatzResearch.WordTrace tailWord_2168950 prefixEnd_2168950 1113713865569394206850187 := by
  unfold tailWord_2168950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4944256593267003250868519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52738736994848034675930869 4944256593267003250868519)
  ·
    refine ⟨7416384889900504876302779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4944256593267003250868519 7416384889900504876302779)
    ·
      refine ⟨11124577334850757314454169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7416384889900504876302779 11124577334850757314454169)
      ·
        refine ⟨8343433001138067985840627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11124577334850757314454169 8343433001138067985840627)
        ·
          refine ⟨12515149501707101978760941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8343433001138067985840627 12515149501707101978760941)
          ·
            refine ⟨4693181063140163242035353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12515149501707101978760941 4693181063140163242035353)
            ·
              refine ⟨3519885797355122431526515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693181063140163242035353 3519885797355122431526515)
              ·
                refine ⟨5279828696032683647289773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519885797355122431526515 5279828696032683647289773)
                ·
                  refine ⟨1979935761012256367733665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5279828696032683647289773 1979935761012256367733665)
                  ·
                    refine ⟨1484951820759192275800249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979935761012256367733665 1484951820759192275800249)
                    ·
                      refine ⟨1113713865569394206850187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484951820759192275800249 1113713865569394206850187)
                      ·
                        rfl

theorem cell23_2168950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2168950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168950 prefixEnd_2168950 := by exact prefixLift 2168950
  have htrace : WordTrace (prefixWord ++ tailWord_2168950) baseStart_2168950 baseEnd_2168950 := by
    simpa [prefixWord, tailWord_2168950, baseEnd_2168950] using wordTrace_append hprefix tailTrace_2168950
  have hstable : (prefixWord ++ tailWord_2168950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168950).length < 2 ^ (prefixWord ++ tailWord_2168950).sum := by decide
  have hdescent : baseEnd_2168950 < baseStart_2168950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168984 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2168984 : Nat := 118140960795 + 2168984 * 2 ^ 59
def prefixEnd_2168984 : Nat := 4983230072969 + 3 ^ 40 * 2168984 * 2
def baseEnd_2168984 : Nat := 1113731323911647073825031

theorem tailTrace_2168984 : CollatzResearch.WordTrace tailWord_2168984 prefixEnd_2168984 1113731323911647073825031 := by
  unfold tailWord_2168984
  simp only [CollatzResearch.WordTrace]
  refine ⟨39554672787074437910317003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52739563716099250547089337 39554672787074437910317003)
  ·
    refine ⟨59332009180611656865475505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39554672787074437910317003 59332009180611656865475505)
    ·
      refine ⟨44499006885458742649106629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59332009180611656865475505 44499006885458742649106629)
      ·
        refine ⟨8343563791023514246707493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44499006885458742649106629 8343563791023514246707493)
        ·
          refine ⟨1564418210816908921257655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8343563791023514246707493 1564418210816908921257655)
          ·
            refine ⟨2346627316225363381886483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564418210816908921257655 2346627316225363381886483)
            ·
              refine ⟨3519940974338045072829725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346627316225363381886483 3519940974338045072829725)
              ·
                refine ⟨1319977865376766902311147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3519940974338045072829725 1319977865376766902311147)
                ·
                  refine ⟨1979966798065150353466721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319977865376766902311147 1979966798065150353466721)
                  ·
                    refine ⟨1484975098548862765100041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979966798065150353466721 1484975098548862765100041)
                    ·
                      refine ⟨1113731323911647073825031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484975098548862765100041 1113731323911647073825031)
                      ·
                        rfl

theorem cell23_2168984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2168984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168984 prefixEnd_2168984 := by exact prefixLift 2168984
  have htrace : WordTrace (prefixWord ++ tailWord_2168984) baseStart_2168984 baseEnd_2168984 := by
    simpa [prefixWord, tailWord_2168984, baseEnd_2168984] using wordTrace_append hprefix tailTrace_2168984
  have hstable : (prefixWord ++ tailWord_2168984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168984).length < 2 ^ (prefixWord ++ tailWord_2168984).sum := by decide
  have hdescent : baseEnd_2168984 < baseStart_2168984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168993 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2168993 : Nat := 118140960795 + 2168993 * 2 ^ 59
def prefixEnd_2168993 : Nat := 4983230072969 + 3 ^ 40 * 2168993 * 2
def baseEnd_2168993 : Nat := 1113735945237537538612489

theorem tailTrace_2168993 : CollatzResearch.WordTrace tailWord_2168993 prefixEnd_2168993 1113735945237537538612489 := by
  unfold tailWord_2168993
  simp only [CollatzResearch.WordTrace]
  refine ⟨79109673831116270357711633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52739782554077513571807755 79109673831116270357711633)
  ·
    refine ⟨59332255373337202768283725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79109673831116270357711633 59332255373337202768283725)
    ·
      refine ⟨22249595765001451038106397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59332255373337202768283725 22249595765001451038106397)
      ·
        refine ⟨8343598411875544139289899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22249595765001451038106397 8343598411875544139289899)
        ·
          refine ⟨12515397617813316208934849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8343598411875544139289899 12515397617813316208934849)
          ·
            refine ⟨9386548213359987156701137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12515397617813316208934849 9386548213359987156701137)
            ·
              refine ⟨7039911160019990367525853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9386548213359987156701137 7039911160019990367525853)
              ·
                refine ⟨2639966685007496387822195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7039911160019990367525853 2639966685007496387822195)
                ·
                  refine ⟨3959950027511244581733293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639966685007496387822195 3959950027511244581733293)
                  ·
                    refine ⟨1484981260316716718149985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3959950027511244581733293 1484981260316716718149985)
                    ·
                      refine ⟨1113735945237537538612489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1484981260316716718149985 1113735945237537538612489)
                      ·
                        rfl

theorem cell23_2168993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2168993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2168993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2168993 prefixEnd_2168993 := by exact prefixLift 2168993
  have htrace : WordTrace (prefixWord ++ tailWord_2168993) baseStart_2168993 baseEnd_2168993 := by
    simpa [prefixWord, tailWord_2168993, baseEnd_2168993] using wordTrace_append hprefix tailTrace_2168993
  have hstable : (prefixWord ++ tailWord_2168993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168993).length < 2 ^ (prefixWord ++ tailWord_2168993).sum := by decide
  have hdescent : baseEnd_2168993 < baseStart_2168993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169063 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 5]
def baseStart_2169063 : Nat := 118140960795 + 2169063 * 2 ^ 59
def prefixEnd_2169063 : Nat := 4983230072969 + 3 ^ 40 * 2169063 * 2
def baseEnd_2169063 : Nat := 123752432098150251637463

theorem tailTrace_2169063 : CollatzResearch.WordTrace tailWord_2169063 prefixEnd_2169063 123752432098150251637463 := by
  unfold tailWord_2169063
  simp only [CollatzResearch.WordTrace]
  refine ⟨79112226940862672312759843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52741484627241781541839895 79112226940862672312759843)
  ·
    refine ⟨118668340411294008469139765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79112226940862672312759843 118668340411294008469139765)
    ·
      refine ⟨11125156913558813293981853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118668340411294008469139765 11125156913558813293981853)
      ·
        refine ⟨4171933842584554985243195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11125156913558813293981853 4171933842584554985243195)
        ·
          refine ⟨6257900763876832477864793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171933842584554985243195 6257900763876832477864793)
          ·
            refine ⟨4693425572907624358398595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257900763876832477864793 4693425572907624358398595)
            ·
              refine ⟨7040138359361436537597893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693425572907624358398595 7040138359361436537597893)
              ·
                refine ⟨1320025942380269350799605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7040138359361436537597893 1320025942380269350799605)
                ·
                  refine ⟨123752432098150251637463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1320025942380269350799605 123752432098150251637463)
                  ·
                    rfl

theorem cell23_2169063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 5].length) (baseStart_2169063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169063 prefixEnd_2169063 := by exact prefixLift 2169063
  have htrace : WordTrace (prefixWord ++ tailWord_2169063) baseStart_2169063 baseEnd_2169063 := by
    simpa [prefixWord, tailWord_2169063, baseEnd_2169063] using wordTrace_append hprefix tailTrace_2169063
  have hstable : (prefixWord ++ tailWord_2169063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169063).length < 2 ^ (prefixWord ++ tailWord_2169063).sum := by decide
  have hdescent : baseEnd_2169063 < baseStart_2169063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169066 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_2169066 : Nat := 118140960795 + 2169066 * 2 ^ 59
def prefixEnd_2169066 : Nat := 4983230072969 + 3 ^ 40 * 2169066 * 2
def baseEnd_2169066 : Nat := 1113773429325315752999653

theorem tailTrace_2169066 : CollatzResearch.WordTrace tailWord_2169066 prefixEnd_2169066 1113773429325315752999653 := by
  unfold tailWord_2169066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19778084089962950956279763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52741557573234535883412701 19778084089962950956279763)
  ·
    refine ⟨29667126134944426434419645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19778084089962950956279763 29667126134944426434419645)
    ·
      refine ⟨11125172300604159912907367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29667126134944426434419645 11125172300604159912907367)
      ·
        refine ⟨16687758450906239869361051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125172300604159912907367 16687758450906239869361051)
        ·
          refine ⟨25031637676359359804041577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16687758450906239869361051 25031637676359359804041577)
          ·
            refine ⟨18773728257269519853031183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25031637676359359804041577 18773728257269519853031183)
            ·
              refine ⟨28160592385904279779546775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18773728257269519853031183 28160592385904279779546775)
              ·
                refine ⟨42240888578856419669320163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28160592385904279779546775 42240888578856419669320163)
                ·
                  refine ⟨63361332868284629503980245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42240888578856419669320163 63361332868284629503980245)
                  ·
                    refine ⟨1485031239100421003999537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63361332868284629503980245 1485031239100421003999537)
                    ·
                      refine ⟨1113773429325315752999653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485031239100421003999537 1113773429325315752999653)
                      ·
                        rfl

theorem cell23_2169066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_2169066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169066 prefixEnd_2169066 := by exact prefixLift 2169066
  have htrace : WordTrace (prefixWord ++ tailWord_2169066) baseStart_2169066 baseEnd_2169066 := by
    simpa [prefixWord, tailWord_2169066, baseEnd_2169066] using wordTrace_append hprefix tailTrace_2169066
  have hstable : (prefixWord ++ tailWord_2169066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169066).length < 2 ^ (prefixWord ++ tailWord_2169066).sum := by decide
  have hdescent : baseEnd_2169066 < baseStart_2169066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169096 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2169096 : Nat := 118140960795 + 2169096 * 2 ^ 59
def prefixEnd_2169096 : Nat := 4983230072969 + 3 ^ 40 * 2169096 * 2
def baseEnd_2169096 : Nat := 1113788833744950635624515

theorem tailTrace_2169096 : CollatzResearch.WordTrace tailWord_2169096 prefixEnd_2169096 1113788833744950635624515 := by
  unfold tailWord_2169096
  simp only [CollatzResearch.WordTrace]
  refine ⟨39556715274871559474355571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52742287033162079299140761 39556715274871559474355571)
  ·
    refine ⟨59335072912307339211533357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39556715274871559474355571 59335072912307339211533357)
    ·
      refine ⟨22250652342115252204325009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59335072912307339211533357 22250652342115252204325009)
      ·
        refine ⟨16687989256586439153243757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22250652342115252204325009 16687989256586439153243757)
        ·
          refine ⟨6257995971219914682466409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16687989256586439153243757 6257995971219914682466409)
          ·
            refine ⟨4693496978414936011849807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257995971219914682466409 4693496978414936011849807)
            ·
              refine ⟨7040245467622404017774711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693496978414936011849807 7040245467622404017774711)
              ·
                refine ⟨10560368201433606026662067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7040245467622404017774711 10560368201433606026662067)
                ·
                  refine ⟨15840552302150409039993101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10560368201433606026662067 15840552302150409039993101)
                  ·
                    refine ⟨5940207113306403389997413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15840552302150409039993101 5940207113306403389997413)
                    ·
                      refine ⟨1113788833744950635624515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5940207113306403389997413 1113788833744950635624515)
                      ·
                        rfl

theorem cell23_2169096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2169096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169096 prefixEnd_2169096 := by exact prefixLift 2169096
  have htrace : WordTrace (prefixWord ++ tailWord_2169096) baseStart_2169096 baseEnd_2169096 := by
    simpa [prefixWord, tailWord_2169096, baseEnd_2169096] using wordTrace_append hprefix tailTrace_2169096
  have hstable : (prefixWord ++ tailWord_2169096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169096).length < 2 ^ (prefixWord ++ tailWord_2169096).sum := by decide
  have hdescent : baseEnd_2169096 < baseStart_2169096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169109 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2169109 : Nat := 118140960795 + 2169109 * 2 ^ 59
def prefixEnd_2169109 : Nat := 4983230072969 + 3 ^ 40 * 2169109 * 2
def baseEnd_2169109 : Nat := 1113795508993459084761955

theorem tailTrace_2169109 : CollatzResearch.WordTrace tailWord_2169109 prefixEnd_2169109 1113795508993459084761955 := by
  unfold tailWord_2169109
  simp only [CollatzResearch.WordTrace]
  refine ⟨79113904698696022168934381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52742603132464014779289587 79113904698696022168934381)
  ·
    refine ⟨29667714262011008313350393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79113904698696022168934381 29667714262011008313350393)
    ·
      refine ⟨22250785696508256235012795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29667714262011008313350393 22250785696508256235012795)
      ·
        refine ⟨33376178544762384352519193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22250785696508256235012795 33376178544762384352519193)
        ·
          refine ⟨25032133908571788264389395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33376178544762384352519193 25032133908571788264389395)
          ·
            refine ⟨37548200862857682396584093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25032133908571788264389395 37548200862857682396584093)
            ·
              refine ⟨14080575323571630898719035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37548200862857682396584093 14080575323571630898719035)
              ·
                refine ⟨21120862985357446348078553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14080575323571630898719035 21120862985357446348078553)
                ·
                  refine ⟨15840647239018084761058915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21120862985357446348078553 15840647239018084761058915)
                  ·
                    refine ⟨23760970858527127141588373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15840647239018084761058915 23760970858527127141588373)
                    ·
                      refine ⟨1113795508993459084761955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23760970858527127141588373 1113795508993459084761955)
                      ·
                        rfl

theorem cell23_2169109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2169109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169109 prefixEnd_2169109 := by exact prefixLift 2169109
  have htrace : WordTrace (prefixWord ++ tailWord_2169109) baseStart_2169109 baseEnd_2169109 := by
    simpa [prefixWord, tailWord_2169109, baseEnd_2169109] using wordTrace_append hprefix tailTrace_2169109
  have hstable : (prefixWord ++ tailWord_2169109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169109).length < 2 ^ (prefixWord ++ tailWord_2169109).sum := by decide
  have hdescent : baseEnd_2169109 < baseStart_2169109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169116 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2169116 : Nat := 118140960795 + 2169116 * 2 ^ 59
def prefixEnd_2169116 : Nat := 4983230072969 + 3 ^ 40 * 2169116 * 2
def baseEnd_2169116 : Nat := 1113799103358040557374423

theorem tailTrace_2169116 : CollatzResearch.WordTrace tailWord_2169116 prefixEnd_2169116 1113799103358040557374423 := by
  unfold tailWord_2169116
  simp only [CollatzResearch.WordTrace]
  refine ⟨39557080004835331182219601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52742773339780441576292801 39557080004835331182219601)
  ·
    refine ⟨29667810003626498386664701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39557080004835331182219601 29667810003626498386664701)
    ·
      refine ⟨11125428751359936894999263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29667810003626498386664701 11125428751359936894999263)
      ·
        refine ⟨16688143127039905342498895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125428751359936894999263 16688143127039905342498895)
        ·
          refine ⟨25032214690559858013748343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16688143127039905342498895 25032214690559858013748343)
          ·
            refine ⟨37548322035839787020622515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25032214690559858013748343 37548322035839787020622515)
            ·
              refine ⟨56322483053759680530933773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37548322035839787020622515 56322483053759680530933773)
              ·
                refine ⟨21120931145159880199100165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56322483053759680530933773 21120931145159880199100165)
                ·
                  refine ⟨3960174589717477537331281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21120931145159880199100165 3960174589717477537331281)
                  ·
                    refine ⟨2970130942288108152998461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3960174589717477537331281 2970130942288108152998461)
                    ·
                      refine ⟨1113799103358040557374423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2970130942288108152998461 1113799103358040557374423)
                      ·
                        rfl

theorem cell23_2169116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2169116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169116 prefixEnd_2169116 := by exact prefixLift 2169116
  have htrace : WordTrace (prefixWord ++ tailWord_2169116) baseStart_2169116 baseEnd_2169116 := by
    simpa [prefixWord, tailWord_2169116, baseEnd_2169116] using wordTrace_append hprefix tailTrace_2169116
  have hstable : (prefixWord ++ tailWord_2169116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169116).length < 2 ^ (prefixWord ++ tailWord_2169116).sum := by decide
  have hdescent : baseEnd_2169116 < baseStart_2169116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169123 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 1, 4]
def baseStart_2169123 : Nat := 118140960795 + 2169123 * 2 ^ 59
def prefixEnd_2169123 : Nat := 4983230072969 + 3 ^ 40 * 2169123 * 2
def baseEnd_2169123 : Nat := 371267565907540676662297

theorem tailTrace_2169123 : CollatzResearch.WordTrace tailWord_2169123 prefixEnd_2169123 371267565907540676662297 := by
  unfold tailWord_2169123
  simp only [CollatzResearch.WordTrace]
  refine ⟨79114415320645302559944023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52742943547096868373296015 79114415320645302559944023)
  ·
    refine ⟨118671622980967953839916035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79114415320645302559944023 118671622980967953839916035)
    ·
      refine ⟨178007434471451930759874053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118671622980967953839916035 178007434471451930759874053)
      ·
        refine ⟨33376393963397237017476385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178007434471451930759874053 33376393963397237017476385)
        ·
          refine ⟨25032295472547927763107289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33376393963397237017476385 25032295472547927763107289)
          ·
            refine ⟨18774221604410945822330467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25032295472547927763107289 18774221604410945822330467)
            ·
              refine ⟨28161332406616418733495701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18774221604410945822330467 28161332406616418733495701)
              ·
                refine ⟨1320062456560144628132611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28161332406616418733495701 1320062456560144628132611)
                ·
                  refine ⟨1980093684840216942198917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320062456560144628132611 1980093684840216942198917)
                  ·
                    refine ⟨371267565907540676662297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980093684840216942198917 371267565907540676662297)
                    ·
                      rfl

theorem cell23_2169123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 4].length) (baseStart_2169123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169123 prefixEnd_2169123 := by exact prefixLift 2169123
  have htrace : WordTrace (prefixWord ++ tailWord_2169123) baseStart_2169123 baseEnd_2169123 := by
    simpa [prefixWord, tailWord_2169123, baseEnd_2169123] using wordTrace_append hprefix tailTrace_2169123
  have hstable : (prefixWord ++ tailWord_2169123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169123).length < 2 ^ (prefixWord ++ tailWord_2169123).sum := by decide
  have hdescent : baseEnd_2169123 < baseStart_2169123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169139 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_2169139 : Nat := 118140960795 + 2169139 * 2 ^ 59
def prefixEnd_2169139 : Nat := 4983230072969 + 3 ^ 40 * 2169139 * 2
def baseEnd_2169139 : Nat := 1113810913413093967386817

theorem tailTrace_2169139 : CollatzResearch.WordTrace tailWord_2169139 prefixEnd_2169139 1113810913413093967386817 := by
  unfold tailWord_2169139
  simp only [CollatzResearch.WordTrace]
  refine ⟨79114998888587337292526471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52743332592391558195017647 79114998888587337292526471)
  ·
    refine ⟨118672498332881005938789707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79114998888587337292526471 118672498332881005938789707)
    ·
      refine ⟨178008747499321508908184561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118672498332881005938789707 178008747499321508908184561)
      ·
        refine ⟨133506560624491131681138421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178008747499321508908184561 133506560624491131681138421)
        ·
          refine ⟨12516240058546043595106727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133506560624491131681138421 12516240058546043595106727)
          ·
            refine ⟨18774360087819065392660091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12516240058546043595106727 18774360087819065392660091)
            ·
              refine ⟨28161540131728598088990137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18774360087819065392660091 28161540131728598088990137)
              ·
                refine ⟨21121155098796448566742603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28161540131728598088990137 21121155098796448566742603)
                ·
                  refine ⟨31681732648194672850113905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21121155098796448566742603 31681732648194672850113905)
                  ·
                    refine ⟨23761299486146004637585429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31681732648194672850113905 23761299486146004637585429)
                    ·
                      refine ⟨1113810913413093967386817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23761299486146004637585429 1113810913413093967386817)
                      ·
                        rfl

theorem cell23_2169139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_2169139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169139 prefixEnd_2169139 := by exact prefixLift 2169139
  have htrace : WordTrace (prefixWord ++ tailWord_2169139) baseStart_2169139 baseEnd_2169139 := by
    simpa [prefixWord, tailWord_2169139, baseEnd_2169139] using wordTrace_append hprefix tailTrace_2169139
  have hstable : (prefixWord ++ tailWord_2169139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169139).length < 2 ^ (prefixWord ++ tailWord_2169139).sum := by decide
  have hdescent : baseEnd_2169139 < baseStart_2169139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169220 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_2169220 : Nat := 118140960795 + 2169220 * 2 ^ 59
def prefixEnd_2169220 : Nat := 4983230072969 + 3 ^ 40 * 2169220 * 2
def baseEnd_2169220 : Nat := 1113852505346108150473945

theorem tailTrace_2169220 : CollatzResearch.WordTrace tailWord_2169220 prefixEnd_2169220 1113852505346108150473945 := by
  unfold tailWord_2169220
  simp only [CollatzResearch.WordTrace]
  refine ⟨39558976600646944063112557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52745302134195925417483409 39558976600646944063112557)
  ·
    refine ⟨14834616225242604023667209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39558976600646944063112557 14834616225242604023667209)
    ·
      refine ⟨11125962168931953017750407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14834616225242604023667209 11125962168931953017750407)
      ·
        refine ⟨16688943253397929526625611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125962168931953017750407 16688943253397929526625611)
        ·
          refine ⟨25033414880096894289938417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16688943253397929526625611 25033414880096894289938417)
          ·
            refine ⟨18775061160072670717453813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25033414880096894289938417 18775061160072670717453813)
            ·
              refine ⟨1760161983756812879761295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18775061160072670717453813 1760161983756812879761295)
              ·
                refine ⟨2640242975635219319641943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760161983756812879761295 2640242975635219319641943)
                ·
                  refine ⟨3960364463452828979462915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640242975635219319641943 3960364463452828979462915)
                  ·
                    refine ⟨5940546695179243469194373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960364463452828979462915 5940546695179243469194373)
                    ·
                      refine ⟨1113852505346108150473945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5940546695179243469194373 1113852505346108150473945)
                      ·
                        rfl

theorem cell23_2169220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_2169220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169220 prefixEnd_2169220 := by exact prefixLift 2169220
  have htrace : WordTrace (prefixWord ++ tailWord_2169220) baseStart_2169220 baseEnd_2169220 := by
    simpa [prefixWord, tailWord_2169220, baseEnd_2169220] using wordTrace_append hprefix tailTrace_2169220
  have hstable : (prefixWord ++ tailWord_2169220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169220).length < 2 ^ (prefixWord ++ tailWord_2169220).sum := by decide
  have hdescent : baseEnd_2169220 < baseStart_2169220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169226 : List Nat := [3, 1, 2, 5, 12]
def baseStart_2169226 : Nat := 118140960795 + 2169226 * 2 ^ 59
def prefixEnd_2169226 : Nat := 4983230072969 + 3 ^ 40 * 2169226 * 2
def baseEnd_2169226 : Nat := 1527922614856015263373

theorem tailTrace_2169226 : CollatzResearch.WordTrace tailWord_2169226 prefixEnd_2169226 1527922614856015263373 := by
  unfold tailWord_2169226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19779543009818037787735883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52745448026181434100629021 19779543009818037787735883)
  ·
    refine ⟨29669314514727056681603825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19779543009818037787735883 29669314514727056681603825)
    ·
      refine ⟨22251985886045292511202869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29669314514727056681603825 22251985886045292511202869)
      ·
        refine ⟨2086123676816746172925269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22251985886045292511202869 2086123676816746172925269)
        ·
          refine ⟨1527922614856015263373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2086123676816746172925269 1527922614856015263373)
          ·
            rfl

theorem cell23_2169226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 12].length) (baseStart_2169226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169226 prefixEnd_2169226 := by exact prefixLift 2169226
  have htrace : WordTrace (prefixWord ++ tailWord_2169226) baseStart_2169226 baseEnd_2169226 := by
    simpa [prefixWord, tailWord_2169226, baseEnd_2169226] using wordTrace_append hprefix tailTrace_2169226
  have hstable : (prefixWord ++ tailWord_2169226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169226).length < 2 ^ (prefixWord ++ tailWord_2169226).sum := by decide
  have hdescent : baseEnd_2169226 < baseStart_2169226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169230 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2169230 : Nat := 118140960795 + 2169230 * 2 ^ 59
def prefixEnd_2169230 : Nat := 4983230072969 + 3 ^ 40 * 2169230 * 2
def baseEnd_2169230 : Nat := 371285880050884370449633

theorem tailTrace_2169230 : CollatzResearch.WordTrace tailWord_2169230 prefixEnd_2169230 371285880050884370449633 := by
  unfold tailWord_2169230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9889789741407207479261143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52745545287505106556059429 9889789741407207479261143)
  ·
    refine ⟨14834684612110811218891715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9889789741407207479261143 14834684612110811218891715)
    ·
      refine ⟨22252026918166216828337573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14834684612110811218891715 22252026918166216828337573)
      ·
        refine ⟨4172255047156165655313295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22252026918166216828337573 4172255047156165655313295)
        ·
          refine ⟨6258382570734248482969943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172255047156165655313295 6258382570734248482969943)
          ·
            refine ⟨9387573856101372724454915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6258382570734248482969943 9387573856101372724454915)
            ·
              refine ⟨14081360784152059086682373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9387573856101372724454915 14081360784152059086682373)
              ·
                refine ⟨2640255147028511078752945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14081360784152059086682373 2640255147028511078752945)
                ·
                  refine ⟨1980191360271383309064709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640255147028511078752945 1980191360271383309064709)
                  ·
                    refine ⟨371285880050884370449633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980191360271383309064709 371285880050884370449633)
                    ·
                      rfl

theorem cell23_2169230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2169230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169230 prefixEnd_2169230 := by exact prefixLift 2169230
  have htrace : WordTrace (prefixWord ++ tailWord_2169230) baseStart_2169230 baseEnd_2169230 := by
    simpa [prefixWord, tailWord_2169230, baseEnd_2169230] using wordTrace_append hprefix tailTrace_2169230
  have hstable : (prefixWord ++ tailWord_2169230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169230).length < 2 ^ (prefixWord ++ tailWord_2169230).sum := by decide
  have hdescent : baseEnd_2169230 < baseStart_2169230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169253 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_2169253 : Nat := 118140960795 + 2169253 * 2 ^ 59
def prefixEnd_2169253 : Nat := 4983230072969 + 3 ^ 40 * 2169253 * 2
def baseEnd_2169253 : Nat := 1113869450207706521361293

theorem tailTrace_2169253 : CollatzResearch.WordTrace tailWord_2169253 prefixEnd_2169253 1113869450207706521361293 := by
  unfold tailWord_2169253
  simp only [CollatzResearch.WordTrace]
  refine ⟨79119156810174334762176413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52746104540116223174784275 79119156810174334762176413)
  ·
    refine ⟨29669683803815375535816155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79119156810174334762176413 29669683803815375535816155)
    ·
      refine ⟨44504525705723063303724233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29669683803815375535816155 44504525705723063303724233)
      ·
        refine ⟨33378394279292297477793175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44504525705723063303724233 33378394279292297477793175)
        ·
          refine ⟨50067591418938446216689763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33378394279292297477793175 50067591418938446216689763)
          ·
            refine ⟨75101387128407669325034645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50067591418938446216689763 75101387128407669325034645)
            ·
              refine ⟨3520377521644109499610999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75101387128407669325034645 3520377521644109499610999)
              ·
                refine ⟨5280566282466164249416499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520377521644109499610999 5280566282466164249416499)
                ·
                  refine ⟨7920849423699246374124749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5280566282466164249416499 7920849423699246374124749)
                  ·
                    refine ⟨2970318533887217390296781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7920849423699246374124749 2970318533887217390296781)
                    ·
                      refine ⟨1113869450207706521361293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2970318533887217390296781 1113869450207706521361293)
                      ·
                        rfl

theorem cell23_2169253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_2169253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169253 prefixEnd_2169253 := by exact prefixLift 2169253
  have htrace : WordTrace (prefixWord ++ tailWord_2169253) baseStart_2169253 baseEnd_2169253 := by
    simpa [prefixWord, tailWord_2169253, baseEnd_2169253] using wordTrace_append hprefix tailTrace_2169253
  have hstable : (prefixWord ++ tailWord_2169253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169253).length < 2 ^ (prefixWord ++ tailWord_2169253).sum := by decide
  have hdescent : baseEnd_2169253 < baseStart_2169253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169258 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2169258 : Nat := 118140960795 + 2169258 * 2 ^ 59
def prefixEnd_2169258 : Nat := 4983230072969 + 3 ^ 40 * 2169258 * 2
def baseEnd_2169258 : Nat := 1113872017610979001798771

theorem tailTrace_2169258 : CollatzResearch.WordTrace tailWord_2169258 prefixEnd_2169258 1113872017610979001798771 := by
  unfold tailWord_2169258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19779834793789055154027107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52746226116770813744072285 19779834793789055154027107)
  ·
    refine ⟨29669752190683582731040661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19779834793789055154027107 29669752190683582731040661)
    ·
      refine ⟨1390769633938292940517531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29669752190683582731040661 1390769633938292940517531)
      ·
        refine ⟨2086154450907439410776297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390769633938292940517531 2086154450907439410776297)
        ·
          refine ⟨1564615838180579558082223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2086154450907439410776297 1564615838180579558082223)
          ·
            refine ⟨2346923757270869337123335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564615838180579558082223 2346923757270869337123335)
            ·
              refine ⟨3520385635906304005685003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346923757270869337123335 3520385635906304005685003)
              ·
                refine ⟨5280578453859456008527505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520385635906304005685003 5280578453859456008527505)
                ·
                  refine ⟨3960433840394592006395629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5280578453859456008527505 3960433840394592006395629)
                  ·
                    refine ⟨1485162690147972002398361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3960433840394592006395629 1485162690147972002398361)
                    ·
                      refine ⟨1113872017610979001798771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485162690147972002398361 1113872017610979001798771)
                      ·
                        rfl

theorem cell23_2169258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2169258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169258 prefixEnd_2169258 := by exact prefixLift 2169258
  have htrace : WordTrace (prefixWord ++ tailWord_2169258) baseStart_2169258 baseEnd_2169258 := by
    simpa [prefixWord, tailWord_2169258, baseEnd_2169258] using wordTrace_append hprefix tailTrace_2169258
  have hstable : (prefixWord ++ tailWord_2169258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169258).length < 2 ^ (prefixWord ++ tailWord_2169258).sum := by decide
  have hdescent : baseEnd_2169258 < baseStart_2169258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169266 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2169266 : Nat := 118140960795 + 2169266 * 2 ^ 59
def prefixEnd_2169266 : Nat := 4983230072969 + 3 ^ 40 * 2169266 * 2
def baseEnd_2169266 : Nat := 1113876125456214970498733

theorem tailTrace_2169266 : CollatzResearch.WordTrace tailWord_2169266 prefixEnd_2169266 1113876125456214970498733 := by
  unfold tailWord_2169266
  simp only [CollatzResearch.WordTrace]
  refine ⟨19779907739781809495599913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52746420639418158654933101 19779907739781809495599913)
  ·
    refine ⟨14834930804836357121699935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19779907739781809495599913 14834930804836357121699935)
    ·
      refine ⟨22252396207254535682549903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14834930804836357121699935 22252396207254535682549903)
      ·
        refine ⟨33378594310881803523824855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22252396207254535682549903 33378594310881803523824855)
        ·
          refine ⟨50067891466322705285737283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33378594310881803523824855 50067891466322705285737283)
          ·
            refine ⟨75101837199484057928605925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50067891466322705285737283 75101837199484057928605925)
            ·
              refine ⟨14081594474903260861613611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75101837199484057928605925 14081594474903260861613611)
              ·
                refine ⟨21122391712354891292420417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14081594474903260861613611 21122391712354891292420417)
                ·
                  refine ⟨15841793784266168469315313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21122391712354891292420417 15841793784266168469315313)
                  ·
                    refine ⟨11881345338199626351986485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15841793784266168469315313 11881345338199626351986485)
                    ·
                      refine ⟨1113876125456214970498733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11881345338199626351986485 1113876125456214970498733)
                      ·
                        rfl

theorem cell23_2169266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2169266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169266 prefixEnd_2169266 := by exact prefixLift 2169266
  have htrace : WordTrace (prefixWord ++ tailWord_2169266) baseStart_2169266 baseEnd_2169266 := by
    simpa [prefixWord, tailWord_2169266, baseEnd_2169266] using wordTrace_append hprefix tailTrace_2169266
  have hstable : (prefixWord ++ tailWord_2169266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169266).length < 2 ^ (prefixWord ++ tailWord_2169266).sum := by decide
  have hdescent : baseEnd_2169266 < baseStart_2169266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169281 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2169281 : Nat := 118140960795 + 2169281 * 2 ^ 59
def prefixEnd_2169281 : Nat := 4983230072969 + 3 ^ 40 * 2169281 * 2
def baseEnd_2169281 : Nat := 371294609222010803937055

theorem tailTrace_2169281 : CollatzResearch.WordTrace tailWord_2169281 prefixEnd_2169281 371294609222010803937055 := by
  unfold tailWord_2169281
  simp only [CollatzResearch.WordTrace]
  refine ⟨79120178054072895544195697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52746785369381930362797131 79120178054072895544195697)
  ·
    refine ⟨59340133540554671658146773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79120178054072895544195697 59340133540554671658146773)
    ·
      refine ⟨1390784379856750116987815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 59340133540554671658146773 1390784379856750116987815)
      ·
        refine ⟨2086176569785125175481723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390784379856750116987815 2086176569785125175481723)
        ·
          refine ⟨3129264854677687763222585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086176569785125175481723 3129264854677687763222585)
          ·
            refine ⟨2346948641008265822416939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3129264854677687763222585 2346948641008265822416939)
            ·
              refine ⟨3520422961512398733625409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346948641008265822416939 3520422961512398733625409)
              ·
                refine ⟨2640317221134299050219057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520422961512398733625409 2640317221134299050219057)
                ·
                  refine ⟨1980237915850724287664293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640317221134299050219057 1980237915850724287664293)
                  ·
                    refine ⟨371294609222010803937055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980237915850724287664293 371294609222010803937055)
                    ·
                      rfl

theorem cell23_2169281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2169281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169281 prefixEnd_2169281 := by exact prefixLift 2169281
  have htrace : WordTrace (prefixWord ++ tailWord_2169281) baseStart_2169281 baseEnd_2169281 := by
    simpa [prefixWord, tailWord_2169281, baseEnd_2169281] using wordTrace_append hprefix tailTrace_2169281
  have hstable : (prefixWord ++ tailWord_2169281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169281).length < 2 ^ (prefixWord ++ tailWord_2169281).sum := by decide
  have hdescent : baseEnd_2169281 < baseStart_2169281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169287 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_2169287 : Nat := 118140960795 + 2169287 * 2 ^ 59
def prefixEnd_2169287 : Nat := 4983230072969 + 3 ^ 40 * 2169287 * 2
def baseEnd_2169287 : Nat := 1113886908549959388336137

theorem tailTrace_2169287 : CollatzResearch.WordTrace tailWord_2169287 prefixEnd_2169287 1113886908549959388336137 := by
  unfold tailWord_2169287
  simp only [CollatzResearch.WordTrace]
  refine ⟨79120396892051158568914115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52746931261367439045942743 79120396892051158568914115)
  ·
    refine ⟨118680595338076737853371173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79120396892051158568914115 118680595338076737853371173)
    ·
      refine ⟨22252611625889388347507095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118680595338076737853371173 22252611625889388347507095)
      ·
        refine ⟨33378917438834082521260643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22252611625889388347507095 33378917438834082521260643)
        ·
          refine ⟨50068376158251123781890965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33378917438834082521260643 50068376158251123781890965)
          ·
            refine ⟨2346955132418021427276139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50068376158251123781890965 2346955132418021427276139)
            ·
              refine ⟨3520432698627032140914209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346955132418021427276139 3520432698627032140914209)
              ·
                refine ⟨2640324523970274105685657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520432698627032140914209 2640324523970274105685657)
                ·
                  refine ⟨1980243392977705579264243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640324523970274105685657 1980243392977705579264243)
                  ·
                    refine ⟨2970365089466558368896365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1980243392977705579264243 2970365089466558368896365)
                    ·
                      refine ⟨1113886908549959388336137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2970365089466558368896365 1113886908549959388336137)
                      ·
                        rfl

theorem cell23_2169287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_2169287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169287 prefixEnd_2169287 := by exact prefixLift 2169287
  have htrace : WordTrace (prefixWord ++ tailWord_2169287) baseStart_2169287 baseEnd_2169287 := by
    simpa [prefixWord, tailWord_2169287, baseEnd_2169287] using wordTrace_append hprefix tailTrace_2169287
  have hstable : (prefixWord ++ tailWord_2169287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169287).length < 2 ^ (prefixWord ++ tailWord_2169287).sum := by decide
  have hdescent : baseEnd_2169287 < baseStart_2169287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169330 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2169330 : Nat := 118140960795 + 2169330 * 2 ^ 59
def prefixEnd_2169330 : Nat := 4983230072969 + 3 ^ 40 * 2169330 * 2
def baseEnd_2169330 : Nat := 1113908988218102720098439

theorem tailTrace_2169330 : CollatzResearch.WordTrace tailWord_2169330 prefixEnd_2169330 1113908988218102720098439 := by
  unfold tailWord_2169330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19780491307723844228182361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52747976820596917941819629 19780491307723844228182361)
  ·
    refine ⟨14835368480792883171136771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19780491307723844228182361 14835368480792883171136771)
    ·
      refine ⟨22253052721189324756705157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14835368480792883171136771 22253052721189324756705157)
      ·
        refine ⟨4172447385222998391882217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22253052721189324756705157 4172447385222998391882217)
        ·
          refine ⟨3129335538917248793911663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4172447385222998391882217 3129335538917248793911663)
          ·
            refine ⟨4694003308375873190867495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129335538917248793911663 4694003308375873190867495)
            ·
              refine ⟨7041004962563809786301243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694003308375873190867495 7041004962563809786301243)
              ·
                refine ⟨10561507443845714679451865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7041004962563809786301243 10561507443845714679451865)
                ·
                  refine ⟨7921130582884286009588899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10561507443845714679451865 7921130582884286009588899)
                  ·
                    refine ⟨11881695874326429014383349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7921130582884286009588899 11881695874326429014383349)
                    ·
                      refine ⟨1113908988218102720098439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11881695874326429014383349 1113908988218102720098439)
                      ·
                        rfl

theorem cell23_2169330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2169330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169330 prefixEnd_2169330 := by exact prefixLift 2169330
  have htrace : WordTrace (prefixWord ++ tailWord_2169330) baseStart_2169330 baseEnd_2169330 := by
    simpa [prefixWord, tailWord_2169330, baseEnd_2169330] using wordTrace_append hprefix tailTrace_2169330
  have hstable : (prefixWord ++ tailWord_2169330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169330).length < 2 ^ (prefixWord ++ tailWord_2169330).sum := by decide
  have hdescent : baseEnd_2169330 < baseStart_2169330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169400 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 2, 4, 2]
def baseStart_2169400 : Nat := 118140960795 + 2169400 * 2 ^ 59
def prefixEnd_2169400 : Nat := 4983230072969 + 3 ^ 40 * 2169400 * 2
def baseEnd_2169400 : Nat := 1113944931863917446223117

theorem tailTrace_2169400 : CollatzResearch.WordTrace tailWord_2169400 prefixEnd_2169400 1113944931863917446223117 := by
  unfold tailWord_2169400
  simp only [CollatzResearch.WordTrace]
  refine ⟨39562259170320889433888827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52749678893761185911851769 39562259170320889433888827)
  ·
    refine ⟨59343388755481334150833241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39562259170320889433888827 59343388755481334150833241)
    ·
      refine ⟨44507541566611000613124931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59343388755481334150833241 44507541566611000613124931)
      ·
        refine ⟨66761312349916500919687397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44507541566611000613124931 66761312349916500919687397)
        ·
          refine ⟨12517746065609343922441387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66761312349916500919687397 12517746065609343922441387)
          ·
            refine ⟨18776619098414015883662081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12517746065609343922441387 18776619098414015883662081)
            ·
              refine ⟨14082464323810511912746561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18776619098414015883662081 14082464323810511912746561)
              ·
                refine ⟨10561848242857883934559921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14082464323810511912746561 10561848242857883934559921)
                ·
                  refine ⟨7921386182143412950919941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10561848242857883934559921 7921386182143412950919941)
                  ·
                    refine ⟨1485259909151889928297489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7921386182143412950919941 1485259909151889928297489)
                    ·
                      refine ⟨1113944931863917446223117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485259909151889928297489 1113944931863917446223117)
                      ·
                        rfl

theorem cell23_2169400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_2169400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169400 prefixEnd_2169400 := by exact prefixLift 2169400
  have htrace : WordTrace (prefixWord ++ tailWord_2169400) baseStart_2169400 baseEnd_2169400 := by
    simpa [prefixWord, tailWord_2169400, baseEnd_2169400] using wordTrace_append hprefix tailTrace_2169400
  have hstable : (prefixWord ++ tailWord_2169400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169400).length < 2 ^ (prefixWord ++ tailWord_2169400).sum := by decide
  have hdescent : baseEnd_2169400 < baseStart_2169400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169403 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 3]
def baseStart_2169403 : Nat := 118140960795 + 2169403 * 2 ^ 59
def prefixEnd_2169403 : Nat := 4983230072969 + 3 ^ 40 * 2169403 * 2
def baseEnd_2169403 : Nat := 1113946472305880934485603

theorem tailTrace_2169403 : CollatzResearch.WordTrace tailWord_2169403 prefixEnd_2169403 1113946472305880934485603 := by
  unfold tailWord_2169403
  simp only [CollatzResearch.WordTrace]
  refine ⟨79124627759630910380136863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52749751839753940253424575 79124627759630910380136863)
  ·
    refine ⟨118686941639446365570205295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79124627759630910380136863 118686941639446365570205295)
    ·
      refine ⟨178030412459169548355307943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118686941639446365570205295 178030412459169548355307943)
      ·
        refine ⟨267045618688754322532961915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178030412459169548355307943 267045618688754322532961915)
        ·
          refine ⟨400568428033131483799442873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267045618688754322532961915 400568428033131483799442873)
          ·
            refine ⟨300426321024848612849582155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400568428033131483799442873 300426321024848612849582155)
            ·
              refine ⟨450639481537272919274373233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300426321024848612849582155 450639481537272919274373233)
              ·
                refine ⟨337979611152954689455779925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450639481537272919274373233 337979611152954689455779925)
                ·
                  refine ⟨3960698568198687767059921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 337979611152954689455779925 3960698568198687767059921)
                  ·
                    refine ⟨2970523926149015825294941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3960698568198687767059921 2970523926149015825294941)
                    ·
                      refine ⟨1113946472305880934485603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2970523926149015825294941 1113946472305880934485603)
                      ·
                        rfl

theorem cell23_2169403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 3].length) (baseStart_2169403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169403 prefixEnd_2169403 := by exact prefixLift 2169403
  have htrace : WordTrace (prefixWord ++ tailWord_2169403) baseStart_2169403 baseEnd_2169403 := by
    simpa [prefixWord, tailWord_2169403, baseEnd_2169403] using wordTrace_append hprefix tailTrace_2169403
  have hstable : (prefixWord ++ tailWord_2169403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169403).length < 2 ^ (prefixWord ++ tailWord_2169403).sum := by decide
  have hdescent : baseEnd_2169403 < baseStart_2169403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169423 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 6]
def baseStart_2169423 : Nat := 118140960795 + 2169423 * 2 ^ 59
def prefixEnd_2169423 : Nat := 4983230072969 + 3 ^ 40 * 2169423 * 2
def baseEnd_2169423 : Nat := 123772971324330095137279

theorem tailTrace_2169423 : CollatzResearch.WordTrace tailWord_2169423 prefixEnd_2169423 123772971324330095137279 := by
  unfold tailWord_2169423
  simp only [CollatzResearch.WordTrace]
  refine ⟨79125357219558453795864923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52750238146372302530576615 79125357219558453795864923)
  ·
    refine ⟨118688035829337680693797385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79125357219558453795864923 118688035829337680693797385)
    ·
      refine ⟨89016026872003260520348039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118688035829337680693797385 89016026872003260520348039)
      ·
        refine ⟨133524040308004890780522059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89016026872003260520348039 133524040308004890780522059)
        ·
          refine ⟨200286060462007336170783089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133524040308004890780522059 200286060462007336170783089)
          ·
            refine ⟨150214545346505502128087317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200286060462007336170783089 150214545346505502128087317)
            ·
              refine ⟨7041306813117445412254093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150214545346505502128087317 7041306813117445412254093)
              ·
                refine ⟨2640490054919042029595285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7041306813117445412254093 2640490054919042029595285)
                ·
                  refine ⟨123772971324330095137279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2640490054919042029595285 123772971324330095137279)
                  ·
                    rfl

theorem cell23_2169423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 6].length) (baseStart_2169423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169423 prefixEnd_2169423 := by exact prefixLift 2169423
  have htrace : WordTrace (prefixWord ++ tailWord_2169423) baseStart_2169423 baseEnd_2169423 := by
    simpa [prefixWord, tailWord_2169423, baseEnd_2169423] using wordTrace_append hprefix tailTrace_2169423
  have hstable : (prefixWord ++ tailWord_2169423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169423).length < 2 ^ (prefixWord ++ tailWord_2169423).sum := by decide
  have hdescent : baseEnd_2169423 < baseStart_2169423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169483 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 1, 6]
def baseStart_2169483 : Nat := 118140960795 + 2169483 * 2 ^ 59
def prefixEnd_2169483 : Nat := 4983230072969 + 3 ^ 40 * 2169483 * 2
def baseEnd_2169483 : Nat := 371329183586080207161745

theorem tailTrace_2169483 : CollatzResearch.WordTrace tailWord_2169483 prefixEnd_2169483 371329183586080207161745 := by
  unfold tailWord_2169483
  simp only [CollatzResearch.WordTrace]
  refine ⟨79127545599341084043049103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52751697066227389362032735 79127545599341084043049103)
  ·
    refine ⟨118691318399011626064573655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79127545599341084043049103 118691318399011626064573655)
    ·
      refine ⟨178036977598517439096860483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118691318399011626064573655 178036977598517439096860483)
      ·
        refine ⟨267055466397776158645290725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178036977598517439096860483 267055466397776158645290725)
        ·
          refine ⟨50072899949583029745992011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267055466397776158645290725 50072899949583029745992011)
          ·
            refine ⟨75109349924374544618988017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50072899949583029745992011 75109349924374544618988017)
            ·
              refine ⟨56332012443280908464241013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75109349924374544618988017 56332012443280908464241013)
              ·
                refine ⟨5281126166557585168522595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56332012443280908464241013 5281126166557585168522595)
                ·
                  refine ⟨7921689249836377752783893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281126166557585168522595 7921689249836377752783893)
                  ·
                    refine ⟨371329183586080207161745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7921689249836377752783893 371329183586080207161745)
                    ·
                      rfl

theorem cell23_2169483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 6].length) (baseStart_2169483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169483 prefixEnd_2169483 := by exact prefixLift 2169483
  have htrace : WordTrace (prefixWord ++ tailWord_2169483) baseStart_2169483 baseEnd_2169483 := by
    simpa [prefixWord, tailWord_2169483, baseEnd_2169483] using wordTrace_append hprefix tailTrace_2169483
  have hstable : (prefixWord ++ tailWord_2169483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169483).length < 2 ^ (prefixWord ++ tailWord_2169483).sum := by decide
  have hdescent : baseEnd_2169483 < baseStart_2169483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169511 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2169511 : Nat := 118140960795 + 2169511 * 2 ^ 59
def prefixEnd_2169511 : Nat := 4983230072969 + 3 ^ 40 * 2169511 * 2
def baseEnd_2169511 : Nat := 1114001928216566511935107

theorem tailTrace_2169511 : CollatzResearch.WordTrace tailWord_2169511 prefixEnd_2169511 1114001928216566511935107 := by
  unfold tailWord_2169511
  simp only [CollatzResearch.WordTrace]
  refine ⟨79128566843239644825068387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52752377895493096550045591 79128566843239644825068387)
  ·
    refine ⟨118692850264859467237602581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79128566843239644825068387 118692850264859467237602581)
    ·
      refine ⟨5563727356165287526762621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118692850264859467237602581 5563727356165287526762621)
      ·
        refine ⟨2086397758561982822535983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5563727356165287526762621 2086397758561982822535983)
        ·
          refine ⟨3129596637842974233803975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086397758561982822535983 3129596637842974233803975)
          ·
            refine ⟨4694394956764461350705963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129596637842974233803975 4694394956764461350705963)
            ·
              refine ⟨7041592435146692026058945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694394956764461350705963 7041592435146692026058945)
              ·
                refine ⟨5281194326360019019544209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7041592435146692026058945 5281194326360019019544209)
                ·
                  refine ⟨3960895744770014264658157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281194326360019019544209 3960895744770014264658157)
                  ·
                    refine ⟨1485335904288755349246809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3960895744770014264658157 1485335904288755349246809)
                    ·
                      refine ⟨1114001928216566511935107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485335904288755349246809 1114001928216566511935107)
                      ·
                        rfl

theorem cell23_2169511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2169511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169511 prefixEnd_2169511 := by exact prefixLift 2169511
  have htrace : WordTrace (prefixWord ++ tailWord_2169511) baseStart_2169511 baseEnd_2169511 := by
    simpa [prefixWord, tailWord_2169511, baseEnd_2169511] using wordTrace_append hprefix tailTrace_2169511
  have hstable : (prefixWord ++ tailWord_2169511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169511).length < 2 ^ (prefixWord ++ tailWord_2169511).sum := by decide
  have hdescent : baseEnd_2169511 < baseStart_2169511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169517 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2169517 : Nat := 118140960795 + 2169517 * 2 ^ 59
def prefixEnd_2169517 : Nat := 4983230072969 + 3 ^ 40 * 2169517 * 2
def baseEnd_2169517 : Nat := 371335003033497829486693

theorem tailTrace_2169517 : CollatzResearch.WordTrace tailWord_2169517 prefixEnd_2169517 371335003033497829486693 := by
  unfold tailWord_2169517
  simp only [CollatzResearch.WordTrace]
  refine ⟨79128785681217907849786805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52752523787478605233191203 79128785681217907849786805)
  ·
    refine ⟨7418323657614178860917513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79128785681217907849786805 7418323657614178860917513)
    ·
      refine ⟨5563742743210634145688135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7418323657614178860917513 5563742743210634145688135)
      ·
        refine ⟨8345614114815951218532203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5563742743210634145688135 8345614114815951218532203)
        ·
          refine ⟨12518421172223926827798305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8345614114815951218532203 12518421172223926827798305)
          ·
            refine ⟨9388815879167945120848729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12518421172223926827798305 9388815879167945120848729)
            ·
              refine ⟨7041611909375958840636547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9388815879167945120848729 7041611909375958840636547)
              ·
                refine ⟨10562417864063938260954821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7041611909375958840636547 10562417864063938260954821)
                ·
                  refine ⟨1980453349511988423929029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10562417864063938260954821 1980453349511988423929029)
                  ·
                    refine ⟨371335003033497829486693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980453349511988423929029 371335003033497829486693)
                    ·
                      rfl

theorem cell23_2169517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2169517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169517 prefixEnd_2169517 := by exact prefixLift 2169517
  have htrace : WordTrace (prefixWord ++ tailWord_2169517) baseStart_2169517 baseEnd_2169517 := by
    simpa [prefixWord, tailWord_2169517, baseEnd_2169517] using wordTrace_append hprefix tailTrace_2169517
  have hstable : (prefixWord ++ tailWord_2169517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169517).length < 2 ^ (prefixWord ++ tailWord_2169517).sum := by decide
  have hdescent : baseEnd_2169517 < baseStart_2169517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169543 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 4, 7]
def baseStart_2169543 : Nat := 118140960795 + 2169543 * 2 ^ 59
def prefixEnd_2169543 : Nat := 4983230072969 + 3 ^ 40 * 2169543 * 2
def baseEnd_2169543 : Nat := 371339453199170128911653

theorem tailTrace_2169543 : CollatzResearch.WordTrace tailWord_2169543 prefixEnd_2169543 371339453199170128911653 := by
  unfold tailWord_2169543
  simp only [CollatzResearch.WordTrace]
  refine ⟨79129733979123714290233283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52753155986082476193488855 79129733979123714290233283)
  ·
    refine ⟨118694600968685571435349925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79129733979123714290233283 118694600968685571435349925)
    ·
      refine ⟨22255237681628544644128111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118694600968685571435349925 22255237681628544644128111)
      ·
        refine ⟨33382856522442816966192167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22255237681628544644128111 33382856522442816966192167)
        ·
          refine ⟨50074284783664225449288251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33382856522442816966192167 50074284783664225449288251)
          ·
            refine ⟨75111427175496338173932377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50074284783664225449288251 75111427175496338173932377)
            ·
              refine ⟨56333570381622253630449283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75111427175496338173932377 56333570381622253630449283)
              ·
                refine ⟨84500355572433380445673925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56333570381622253630449283 84500355572433380445673925)
                ·
                  refine ⟨15843816669831258833563861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84500355572433380445673925 15843816669831258833563861)
                  ·
                    refine ⟨371339453199170128911653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15843816669831258833563861 371339453199170128911653)
                    ·
                      rfl

theorem cell23_2169543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_2169543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169543 prefixEnd_2169543 := by exact prefixLift 2169543
  have htrace : WordTrace (prefixWord ++ tailWord_2169543) baseStart_2169543 baseEnd_2169543 := by
    simpa [prefixWord, tailWord_2169543, baseEnd_2169543] using wordTrace_append hprefix tailTrace_2169543
  have hstable : (prefixWord ++ tailWord_2169543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169543).length < 2 ^ (prefixWord ++ tailWord_2169543).sum := by decide
  have hdescent : baseEnd_2169543 < baseStart_2169543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169544 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_2169544 : Nat := 118140960795 + 2169544 * 2 ^ 59
def prefixEnd_2169544 : Nat := 4983230072969 + 3 ^ 40 * 2169544 * 2
def baseEnd_2169544 : Nat := 1114018873078164882822455

theorem tailTrace_2169544 : CollatzResearch.WordTrace tailWord_2169544 prefixEnd_2169544 1114018873078164882822455 := by
  unfold tailWord_2169544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39564885226060045730509843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52753180301413394307346457 39564885226060045730509843)
  ·
    refine ⟨59347327839090068595764765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39564885226060045730509843 59347327839090068595764765)
    ·
      refine ⟨22255247939658775723411787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59347327839090068595764765 22255247939658775723411787)
      ·
        refine ⟨33382871909488163585117681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22255247939658775723411787 33382871909488163585117681)
        ·
          refine ⟨25037153932116122688838261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33382871909488163585117681 25037153932116122688838261)
          ·
            refine ⟨2347233181135886502078587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25037153932116122688838261 2347233181135886502078587)
            ·
              refine ⟨3520849771703829753117881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347233181135886502078587 3520849771703829753117881)
              ·
                refine ⟨2640637328777872314838411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520849771703829753117881 2640637328777872314838411)
                ·
                  refine ⟨3960955993166808472257617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640637328777872314838411 3960955993166808472257617)
                  ·
                    refine ⟨2970716994875106354193213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3960955993166808472257617 2970716994875106354193213)
                    ·
                      refine ⟨1114018873078164882822455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2970716994875106354193213 1114018873078164882822455)
                      ·
                        rfl

theorem cell23_2169544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_2169544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169544 prefixEnd_2169544 := by exact prefixLift 2169544
  have htrace : WordTrace (prefixWord ++ tailWord_2169544) baseStart_2169544 baseEnd_2169544 := by
    simpa [prefixWord, tailWord_2169544, baseEnd_2169544] using wordTrace_append hprefix tailTrace_2169544
  have hstable : (prefixWord ++ tailWord_2169544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169544).length < 2 ^ (prefixWord ++ tailWord_2169544).sum := by decide
  have hdescent : baseEnd_2169544 < baseStart_2169544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169610 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2169610 : Nat := 118140960795 + 2169610 * 2 ^ 59
def prefixEnd_2169610 : Nat := 4983230072969 + 3 ^ 40 * 2169610 * 2
def baseEnd_2169610 : Nat := 1114052762801361624597151

theorem tailTrace_2169610 : CollatzResearch.WordTrace tailWord_2169610 prefixEnd_2169610 1114052762801361624597151 := by
  unfold tailWord_2169610
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783044417470246183230571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52754785113253989821948189 19783044417470246183230571)
  ·
    refine ⟨29674566626205369274845857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19783044417470246183230571 29674566626205369274845857)
    ·
      refine ⟨22255924969654026956134393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29674566626205369274845857 22255924969654026956134393)
      ·
        refine ⟨16691943727240520217100795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22255924969654026956134393 16691943727240520217100795)
        ·
          refine ⟨25037915590860780325651193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16691943727240520217100795 25037915590860780325651193)
          ·
            refine ⟨18778436693145585244238395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25037915590860780325651193 18778436693145585244238395)
            ·
              refine ⟨28167655039718377866357593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18778436693145585244238395 28167655039718377866357593)
              ·
                refine ⟨21125741279788783399768195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28167655039718377866357593 21125741279788783399768195)
                ·
                  refine ⟨31688611919683175099652293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21125741279788783399768195 31688611919683175099652293)
                  ·
                    refine ⟨5941614734940595331184805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31688611919683175099652293 5941614734940595331184805)
                    ·
                      refine ⟨1114052762801361624597151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5941614734940595331184805 1114052762801361624597151)
                      ·
                        rfl

theorem cell23_2169610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2169610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169610 prefixEnd_2169610 := by exact prefixLift 2169610
  have htrace : WordTrace (prefixWord ++ tailWord_2169610) baseStart_2169610 baseEnd_2169610 := by
    simpa [prefixWord, tailWord_2169610, baseEnd_2169610] using wordTrace_append hprefix tailTrace_2169610
  have hstable : (prefixWord ++ tailWord_2169610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169610).length < 2 ^ (prefixWord ++ tailWord_2169610).sum := by decide
  have hdescent : baseEnd_2169610 < baseStart_2169610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169614 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_2169614 : Nat := 118140960795 + 2169614 * 2 ^ 59
def prefixEnd_2169614 : Nat := 4983230072969 + 3 ^ 40 * 2169614 * 2
def baseEnd_2169614 : Nat := 1114054816723979608947133

theorem tailTrace_2169614 : CollatzResearch.WordTrace tailWord_2169614 prefixEnd_2169614 1114054816723979608947133 := by
  unfold tailWord_2169614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891540445233311677008487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52754882374577662277378597 9891540445233311677008487)
  ·
    refine ⟨14837310667849967515512731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9891540445233311677008487 14837310667849967515512731)
    ·
      refine ⟨22255966001774951273269097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14837310667849967515512731 22255966001774951273269097)
      ·
        refine ⟨16691974501331213454951823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22255966001774951273269097 16691974501331213454951823)
        ·
          refine ⟨25037961751996820182427735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16691974501331213454951823 25037961751996820182427735)
          ·
            refine ⟨37556942627995230273641603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25037961751996820182427735 37556942627995230273641603)
            ·
              refine ⟨56335413941992845410462405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37556942627995230273641603 56335413941992845410462405)
              ·
                refine ⟨10562890114123658514461701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56335413941992845410462405 10562890114123658514461701)
                ·
                  refine ⟨1980541896398185971461569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10562890114123658514461701 1980541896398185971461569)
                  ·
                    refine ⟨1485406422298639478596177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1980541896398185971461569 1485406422298639478596177)
                    ·
                      refine ⟨1114054816723979608947133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485406422298639478596177 1114054816723979608947133)
                      ·
                        rfl

theorem cell23_2169614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_2169614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169614 prefixEnd_2169614 := by exact prefixLift 2169614
  have htrace : WordTrace (prefixWord ++ tailWord_2169614) baseStart_2169614 baseEnd_2169614 := by
    simpa [prefixWord, tailWord_2169614, baseEnd_2169614] using wordTrace_append hprefix tailTrace_2169614
  have hstable : (prefixWord ++ tailWord_2169614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169614).length < 2 ^ (prefixWord ++ tailWord_2169614).sum := by decide
  have hdescent : baseEnd_2169614 < baseStart_2169614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169618 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2169618 : Nat := 118140960795 + 2169618 * 2 ^ 59
def prefixEnd_2169618 : Nat := 4983230072969 + 3 ^ 40 * 2169618 * 2
def baseEnd_2169618 : Nat := 1114056870646597593297115

theorem tailTrace_2169618 : CollatzResearch.WordTrace tailWord_2169618 prefixEnd_2169618 1114056870646597593297115 := by
  unfold tailWord_2169618
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783117363463000524803377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52754979635901334732809005 19783117363463000524803377)
  ·
    refine ⟨14837338022597250393602533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19783117363463000524803377 14837338022597250393602533)
    ·
      refine ⟨2782000879236984448800475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14837338022597250393602533 2782000879236984448800475)
      ·
        refine ⟨4173001318855476673200713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782000879236984448800475 4173001318855476673200713)
        ·
          refine ⟨3129750989141607504900535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4173001318855476673200713 3129750989141607504900535)
          ·
            refine ⟨4694626483712411257350803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129750989141607504900535 4694626483712411257350803)
            ·
              refine ⟨7041939725568616886026205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694626483712411257350803 7041939725568616886026205)
              ·
                refine ⟨2640727397088231332259827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7041939725568616886026205 2640727397088231332259827)
                ·
                  refine ⟨3961091095632346998389741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640727397088231332259827 3961091095632346998389741)
                  ·
                    refine ⟨1485409160862130124396153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3961091095632346998389741 1485409160862130124396153)
                    ·
                      refine ⟨1114056870646597593297115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485409160862130124396153 1114056870646597593297115)
                      ·
                        rfl

theorem cell23_2169618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2169618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169618 prefixEnd_2169618 := by exact prefixLift 2169618
  have htrace : WordTrace (prefixWord ++ tailWord_2169618) baseStart_2169618 baseEnd_2169618 := by
    simpa [prefixWord, tailWord_2169618, baseEnd_2169618] using wordTrace_append hprefix tailTrace_2169618
  have hstable : (prefixWord ++ tailWord_2169618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169618).length < 2 ^ (prefixWord ++ tailWord_2169618).sum := by decide
  have hdescent : baseEnd_2169618 < baseStart_2169618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169631 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 2, 2, 2]
def baseStart_2169631 : Nat := 118140960795 + 2169631 * 2 ^ 59
def prefixEnd_2169631 : Nat := 4983230072969 + 3 ^ 40 * 2169631 * 2
def baseEnd_2169631 : Nat := 1114063545895106042434555

theorem tailTrace_2169631 : CollatzResearch.WordTrace tailWord_2169631 prefixEnd_2169631 1114063545895106042434555 := by
  unfold tailWord_2169631
  simp only [CollatzResearch.WordTrace]
  refine ⟨79132943602804905319436747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52755295735203270212957831 79132943602804905319436747)
  ·
    refine ⟨118699415404207357979155121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79132943602804905319436747 118699415404207357979155121)
    ·
      refine ⟨89024561553155518484366341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118699415404207357979155121 89024561553155518484366341)
      ·
        refine ⟨16692105291216659715818689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89024561553155518484366341 16692105291216659715818689)
        ·
          refine ⟨12519078968412494786864017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16692105291216659715818689 12519078968412494786864017)
          ·
            refine ⟨9389309226309371090148013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12519078968412494786864017 9389309226309371090148013)
            ·
              refine ⟨3520990959866014158805505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9389309226309371090148013 3520990959866014158805505)
              ·
                refine ⟨2640743219899510619104129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520990959866014158805505 2640743219899510619104129)
                ·
                  refine ⟨1980557414924632964328097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640743219899510619104129 1980557414924632964328097)
                  ·
                    refine ⟨1485418061193474723246073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1980557414924632964328097 1485418061193474723246073)
                    ·
                      refine ⟨1114063545895106042434555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485418061193474723246073 1114063545895106042434555)
                      ·
                        rfl

theorem cell23_2169631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_2169631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169631 prefixEnd_2169631 := by exact prefixLift 2169631
  have htrace : WordTrace (prefixWord ++ tailWord_2169631) baseStart_2169631 baseEnd_2169631 := by
    simpa [prefixWord, tailWord_2169631, baseEnd_2169631] using wordTrace_append hprefix tailTrace_2169631
  have hstable : (prefixWord ++ tailWord_2169631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169631).length < 2 ^ (prefixWord ++ tailWord_2169631).sum := by decide
  have hdescent : baseEnd_2169631 < baseStart_2169631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169637 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 5]
def baseStart_2169637 : Nat := 118140960795 + 2169637 * 2 ^ 59
def prefixEnd_2169637 : Nat := 4983230072969 + 3 ^ 40 * 2169637 * 2
def baseEnd_2169637 : Nat := 123785180753225890995503

theorem tailTrace_2169637 : CollatzResearch.WordTrace tailWord_2169637 prefixEnd_2169637 123785180753225890995503 := by
  unfold tailWord_2169637
  simp only [CollatzResearch.WordTrace]
  refine ⟨79133162440783168344155165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52755441627188778896103443 79133162440783168344155165)
  ·
    refine ⟨29674935915293688129058187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79133162440783168344155165 29674935915293688129058187)
    ·
      refine ⟨44512403872940532193587281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29674935915293688129058187 44512403872940532193587281)
      ·
        refine ⟨33384302904705399145190461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44512403872940532193587281 33384302904705399145190461)
        ·
          refine ⟨12519113589264524679446423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33384302904705399145190461 12519113589264524679446423)
          ·
            refine ⟨18778670383896787019169635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12519113589264524679446423 18778670383896787019169635)
            ·
              refine ⟨28168005575845180528754453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18778670383896787019169635 28168005575845180528754453)
              ·
                refine ⟨1320375261367742837285365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28168005575845180528754453 1320375261367742837285365)
                ·
                  refine ⟨123785180753225890995503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1320375261367742837285365 123785180753225890995503)
                  ·
                    rfl

theorem cell23_2169637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_2169637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169637 prefixEnd_2169637 := by exact prefixLift 2169637
  have htrace : WordTrace (prefixWord ++ tailWord_2169637) baseStart_2169637 baseEnd_2169637 := by
    simpa [prefixWord, tailWord_2169637, baseEnd_2169637] using wordTrace_append hprefix tailTrace_2169637
  have hstable : (prefixWord ++ tailWord_2169637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169637).length < 2 ^ (prefixWord ++ tailWord_2169637).sum := by decide
  have hdescent : baseEnd_2169637 < baseStart_2169637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169650 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2169650 : Nat := 118140960795 + 2169650 * 2 ^ 59
def prefixEnd_2169650 : Nat := 4983230072969 + 3 ^ 40 * 2169650 * 2
def baseEnd_2169650 : Nat := 371357767342513822698989

theorem tailTrace_2169650 : CollatzResearch.WordTrace tailWord_2169650 prefixEnd_2169650 371357767342513822698989 := by
  unfold tailWord_2169650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783409147434017891094601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52755757726490714376252269 19783409147434017891094601)
  ·
    refine ⟨14837556860575513418320951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19783409147434017891094601 14837556860575513418320951)
    ·
      refine ⟨22256335290863270127481427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14837556860575513418320951 22256335290863270127481427)
      ·
        refine ⟨33384502936294905191222141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22256335290863270127481427 33384502936294905191222141)
        ·
          refine ⟨12519188601110589446708303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33384502936294905191222141 12519188601110589446708303)
          ·
            refine ⟨18778782901665884170062455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12519188601110589446708303 18778782901665884170062455)
            ·
              refine ⟨28168174352498826255093683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18778782901665884170062455 28168174352498826255093683)
              ·
                refine ⟨42252261528748239382640525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28168174352498826255093683 42252261528748239382640525)
                ·
                  refine ⟨15844598073280589768490197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42252261528748239382640525 15844598073280589768490197)
                  ·
                    refine ⟨371357767342513822698989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15844598073280589768490197 371357767342513822698989)
                    ·
                      rfl

theorem cell23_2169650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2169650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169650 prefixEnd_2169650 := by exact prefixLift 2169650
  have htrace : WordTrace (prefixWord ++ tailWord_2169650) baseStart_2169650 baseEnd_2169650 := by
    simpa [prefixWord, tailWord_2169650, baseEnd_2169650] using wordTrace_append hprefix tailTrace_2169650
  have hstable : (prefixWord ++ tailWord_2169650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169650).length < 2 ^ (prefixWord ++ tailWord_2169650).sum := by decide
  have hdescent : baseEnd_2169650 < baseStart_2169650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169660 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2169660 : Nat := 118140960795 + 2169660 * 2 ^ 59
def prefixEnd_2169660 : Nat := 4983230072969 + 3 ^ 40 * 2169660 * 2
def baseEnd_2169660 : Nat := 1114078436834086428971921

theorem tailTrace_2169660 : CollatzResearch.WordTrace tailWord_2169660 prefixEnd_2169660 1114078436834086428971921 := by
  unfold tailWord_2169660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39567000659849921636121217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52756000879799895514828289 39567000659849921636121217)
  ·
    refine ⟨29675250494887441227090913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39567000659849921636121217 29675250494887441227090913)
    ·
      refine ⟨22256437871165580920318185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29675250494887441227090913 22256437871165580920318185)
      ·
        refine ⟨16692328403374185690238639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22256437871165580920318185 16692328403374185690238639)
        ·
          refine ⟨25038492605061278535357959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16692328403374185690238639 25038492605061278535357959)
          ·
            refine ⟨37557738907591917803036939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25038492605061278535357959 37557738907591917803036939)
            ·
              refine ⟨56336608361387876704555409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37557738907591917803036939 56336608361387876704555409)
              ·
                refine ⟨42252456271040907528416557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56336608361387876704555409 42252456271040907528416557)
                ·
                  refine ⟨15844671101640340323156209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42252456271040907528416557 15844671101640340323156209)
                  ·
                    refine ⟨11883503326230255242367157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15844671101640340323156209 11883503326230255242367157)
                    ·
                      refine ⟨1114078436834086428971921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11883503326230255242367157 1114078436834086428971921)
                      ·
                        rfl

theorem cell23_2169660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2169660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169660 prefixEnd_2169660 := by exact prefixLift 2169660
  have htrace : WordTrace (prefixWord ++ tailWord_2169660) baseStart_2169660 baseEnd_2169660 := by
    simpa [prefixWord, tailWord_2169660, baseEnd_2169660] using wordTrace_append hprefix tailTrace_2169660
  have hstable : (prefixWord ++ tailWord_2169660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169660).length < 2 ^ (prefixWord ++ tailWord_2169660).sum := by decide
  have hdescent : baseEnd_2169660 < baseStart_2169660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169684 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_2169684 : Nat := 118140960795 + 2169684 * 2 ^ 59
def prefixEnd_2169684 : Nat := 4983230072969 + 3 ^ 40 * 2169684 * 2
def baseEnd_2169684 : Nat := 371363586789931445023937

theorem tailTrace_2169684 : CollatzResearch.WordTrace tailWord_2169684 prefixEnd_2169684 371363586789931445023937 := by
  unfold tailWord_2169684
  simp only [CollatzResearch.WordTrace]
  refine ⟨39567438335806447685558053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52756584447741930247410737 39567438335806447685558053)
  ·
    refine ⟨7418894687963708941042135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39567438335806447685558053 7418894687963708941042135)
    ·
      refine ⟨11128342031945563411563203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7418894687963708941042135 11128342031945563411563203)
      ·
        refine ⟨16692513047918345117344805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128342031945563411563203 16692513047918345117344805)
        ·
          refine ⟨3129846196484689709502151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16692513047918345117344805 3129846196484689709502151)
          ·
            refine ⟨4694769294727034564253227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129846196484689709502151 4694769294727034564253227)
            ·
              refine ⟨7042153942090551846379841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694769294727034564253227 7042153942090551846379841)
              ·
                refine ⟨5281615456567913884784881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042153942090551846379841 5281615456567913884784881)
                ·
                  refine ⟨3961211592425935413588661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281615456567913884784881 3961211592425935413588661)
                  ·
                    refine ⟨371363586789931445023937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3961211592425935413588661 371363586789931445023937)
                    ·
                      rfl

theorem cell23_2169684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_2169684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169684 prefixEnd_2169684 := by exact prefixLift 2169684
  have htrace : WordTrace (prefixWord ++ tailWord_2169684) baseStart_2169684 baseEnd_2169684 := by
    simpa [prefixWord, tailWord_2169684, baseEnd_2169684] using wordTrace_append hprefix tailTrace_2169684
  have hstable : (prefixWord ++ tailWord_2169684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169684).length < 2 ^ (prefixWord ++ tailWord_2169684).sum := by decide
  have hdescent : baseEnd_2169684 < baseStart_2169684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169687 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_2169687 : Nat := 118140960795 + 2169687 * 2 ^ 59
def prefixEnd_2169687 : Nat := 4983230072969 + 3 ^ 40 * 2169687 * 2
def baseEnd_2169687 : Nat := 1114092300811757823334297

theorem tailTrace_2169687 : CollatzResearch.WordTrace tailWord_2169687 prefixEnd_2169687 1114092300811757823334297 := by
  unfold tailWord_2169687
  simp only [CollatzResearch.WordTrace]
  refine ⟨79134986090602026883475315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52756657393734684588983543 79134986090602026883475315)
  ·
    refine ⟨118702479135903040325212973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79134986090602026883475315 118702479135903040325212973)
    ·
      refine ⟨44513429675963640121954865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118702479135903040325212973 44513429675963640121954865)
      ·
        refine ⟨33385072256972730091466149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44513429675963640121954865 33385072256972730091466149)
        ·
          refine ⟨6259701048182386892149903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33385072256972730091466149 6259701048182386892149903)
          ·
            refine ⟨9389551572273580338224855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259701048182386892149903 9389551572273580338224855)
            ·
              refine ⟨14084327358410370507337283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9389551572273580338224855 14084327358410370507337283)
              ·
                refine ⟨21126491037615555761005925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14084327358410370507337283 21126491037615555761005925)
                ·
                  refine ⟨3961217069552916705188611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21126491037615555761005925 3961217069552916705188611)
                  ·
                    refine ⟨5941825604329375057782917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3961217069552916705188611 5941825604329375057782917)
                    ·
                      refine ⟨1114092300811757823334297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5941825604329375057782917 1114092300811757823334297)
                      ·
                        rfl

theorem cell23_2169687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_2169687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169687 prefixEnd_2169687 := by exact prefixLift 2169687
  have htrace : WordTrace (prefixWord ++ tailWord_2169687) baseStart_2169687 baseEnd_2169687 := by
    simpa [prefixWord, tailWord_2169687, baseEnd_2169687] using wordTrace_append hprefix tailTrace_2169687
  have hstable : (prefixWord ++ tailWord_2169687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169687).length < 2 ^ (prefixWord ++ tailWord_2169687).sum := by decide
  have hdescent : baseEnd_2169687 < baseStart_2169687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169697 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 3, 4]
def baseStart_2169697 : Nat := 118140960795 + 2169697 * 2 ^ 59
def prefixEnd_2169697 : Nat := 4983230072969 + 3 ^ 40 * 2169697 * 2
def baseEnd_2169697 : Nat := 371365811872767594736417

theorem tailTrace_2169697 : CollatzResearch.WordTrace tailWord_2169697 prefixEnd_2169697 371365811872767594736417 := by
  unfold tailWord_2169697
  simp only [CollatzResearch.WordTrace]
  refine ⟨79135350820565798591339345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52756900547043865727559563 79135350820565798591339345)
  ·
    refine ⟨59351513115424348943504509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79135350820565798591339345 59351513115424348943504509)
    ·
      refine ⟨22256817418284130853814191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59351513115424348943504509 22256817418284130853814191)
      ·
        refine ⟨33385226127426196280721287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22256817418284130853814191 33385226127426196280721287)
        ·
          refine ⟨50077839191139294421081931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33385226127426196280721287 50077839191139294421081931)
          ·
            refine ⟨75116758786708941631622897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50077839191139294421081931 75116758786708941631622897)
            ·
              refine ⟨56337569090031706223717173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75116758786708941631622897 56337569090031706223717173)
              ·
                refine ⟨5281647102190472458473485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56337569090031706223717173 5281647102190472458473485)
                ·
                  refine ⟨1980617663321427171927557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5281647102190472458473485 1980617663321427171927557)
                  ·
                    refine ⟨371365811872767594736417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980617663321427171927557 371365811872767594736417)
                    ·
                      rfl

theorem cell23_2169697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_2169697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169697 prefixEnd_2169697 := by exact prefixLift 2169697
  have htrace : WordTrace (prefixWord ++ tailWord_2169697) baseStart_2169697 baseEnd_2169697 := by
    simpa [prefixWord, tailWord_2169697, baseEnd_2169697] using wordTrace_append hprefix tailTrace_2169697
  have hstable : (prefixWord ++ tailWord_2169697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169697).length < 2 ^ (prefixWord ++ tailWord_2169697).sum := by decide
  have hdescent : baseEnd_2169697 < baseStart_2169697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169757 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2169757 : Nat := 118140960795 + 2169757 * 2 ^ 59
def prefixEnd_2169757 : Nat := 4983230072969 + 3 ^ 40 * 2169757 * 2
def baseEnd_2169757 : Nat := 371376081485857516486325

theorem tailTrace_2169757 : CollatzResearch.WordTrace tailWord_2169757 prefixEnd_2169757 371376081485857516486325 := by
  unfold tailWord_2169757
  simp only [CollatzResearch.WordTrace]
  refine ⟨79137539200348428838523525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52758359466898952559015683 79137539200348428838523525)
  ·
    refine ⟨14838288600065330407223161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79137539200348428838523525 14838288600065330407223161)
    ·
      refine ⟨11128716450048997805417371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14838288600065330407223161 11128716450048997805417371)
      ·
        refine ⟨16693074675073496708126057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128716450048997805417371 16693074675073496708126057)
        ·
          refine ⟨12519806006305122531094543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16693074675073496708126057 12519806006305122531094543)
          ·
            refine ⟨18779709009457683796641815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12519806006305122531094543 18779709009457683796641815)
            ·
              refine ⟨28169563514186525694962723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18779709009457683796641815 28169563514186525694962723)
              ·
                refine ⟨42254345271279788542444085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28169563514186525694962723 42254345271279788542444085)
                ·
                  refine ⟨3961344869182480175854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42254345271279788542444085 3961344869182480175854133)
                  ·
                    refine ⟨371376081485857516486325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3961344869182480175854133 371376081485857516486325)
                    ·
                      rfl

theorem cell23_2169757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2169757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169757 prefixEnd_2169757 := by exact prefixLift 2169757
  have htrace : WordTrace (prefixWord ++ tailWord_2169757) baseStart_2169757 baseEnd_2169757 := by
    simpa [prefixWord, tailWord_2169757, baseEnd_2169757] using wordTrace_append hprefix tailTrace_2169757
  have hstable : (prefixWord ++ tailWord_2169757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169757).length < 2 ^ (prefixWord ++ tailWord_2169757).sum := by decide
  have hdescent : baseEnd_2169757 < baseStart_2169757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169764 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_2169764 : Nat := 118140960795 + 2169764 * 2 ^ 59
def prefixEnd_2169764 : Nat := 4983230072969 + 3 ^ 40 * 2169764 * 2
def baseEnd_2169764 : Nat := 1114131838822154022071443

theorem tailTrace_2169764 : CollatzResearch.WordTrace tailWord_2169764 prefixEnd_2169764 1114131838822154022071443 := by
  unfold tailWord_2169764
  simp only [CollatzResearch.WordTrace]
  refine ⟨39568897255661534517014173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52758529674215379356018897 39568897255661534517014173)
  ·
    refine ⟨14838336470873075443880315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39568897255661534517014173 14838336470873075443880315)
    ·
      refine ⟨22257504706309613165820473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14838336470873075443880315 22257504706309613165820473)
      ·
        refine ⟨16693128529732209874365355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22257504706309613165820473 16693128529732209874365355)
        ·
          refine ⟨25039692794598314811548033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16693128529732209874365355 25039692794598314811548033)
          ·
            refine ⟨18779769595948736108661025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25039692794598314811548033 18779769595948736108661025)
            ·
              refine ⟨14084827196961552081495769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18779769595948736108661025 14084827196961552081495769)
              ·
                refine ⟨10563620397721164061121827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14084827196961552081495769 10563620397721164061121827)
                ·
                  refine ⟨15845430596581746091682741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10563620397721164061121827 15845430596581746091682741)
                  ·
                    refine ⟨1485509118429538696095257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15845430596581746091682741 1485509118429538696095257)
                    ·
                      refine ⟨1114131838822154022071443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485509118429538696095257 1114131838822154022071443)
                      ·
                        rfl

theorem cell23_2169764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_2169764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169764 prefixEnd_2169764 := by exact prefixLift 2169764
  have htrace : WordTrace (prefixWord ++ tailWord_2169764) baseStart_2169764 baseEnd_2169764 := by
    simpa [prefixWord, tailWord_2169764, baseEnd_2169764] using wordTrace_append hprefix tailTrace_2169764
  have hstable : (prefixWord ++ tailWord_2169764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169764).length < 2 ^ (prefixWord ++ tailWord_2169764).sum := by decide
  have hdescent : baseEnd_2169764 < baseStart_2169764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169804 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_2169804 : Nat := 118140960795 + 2169804 * 2 ^ 59
def prefixEnd_2169804 : Nat := 4983230072969 + 3 ^ 40 * 2169804 * 2
def baseEnd_2169804 : Nat := 371384126016111288523753

theorem tailTrace_2169804 : CollatzResearch.WordTrace tailWord_2169804 prefixEnd_2169804 371384126016111288523753 := by
  unfold tailWord_2169804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39569626715589077932742233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52759502287452103910322977 39569626715589077932742233)
  ·
    refine ⟨29677220036691808449556675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39569626715589077932742233 29677220036691808449556675)
    ·
      refine ⟨44515830055037712674335013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29677220036691808449556675 44515830055037712674335013)
      ·
        refine ⟨8346718135319571126437815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44515830055037712674335013 8346718135319571126437815)
        ·
          refine ⟨12520077202979356689656723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8346718135319571126437815 12520077202979356689656723)
          ·
            refine ⟨18780115804469035034485085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12520077202979356689656723 18780115804469035034485085)
            ·
              refine ⟨7042543426675888137931907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18780115804469035034485085 7042543426675888137931907)
              ·
                refine ⟨10563815140013832206897861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7042543426675888137931907 10563815140013832206897861)
                ·
                  refine ⟨1980715338752593538793349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10563815140013832206897861 1980715338752593538793349)
                  ·
                    refine ⟨371384126016111288523753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980715338752593538793349 371384126016111288523753)
                    ·
                      rfl

theorem cell23_2169804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_2169804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169804 prefixEnd_2169804 := by exact prefixLift 2169804
  have htrace : WordTrace (prefixWord ++ tailWord_2169804) baseStart_2169804 baseEnd_2169804 := by
    simpa [prefixWord, tailWord_2169804, baseEnd_2169804] using wordTrace_append hprefix tailTrace_2169804
  have hstable : (prefixWord ++ tailWord_2169804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169804).length < 2 ^ (prefixWord ++ tailWord_2169804).sum := by decide
  have hdescent : baseEnd_2169804 < baseStart_2169804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169821 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2169821 : Nat := 118140960795 + 2169821 * 2 ^ 59
def prefixEnd_2169821 : Nat := 4983230072969 + 3 ^ 40 * 2169821 * 2
def baseEnd_2169821 : Nat := 371387035739820099686227

theorem tailTrace_2169821 : CollatzResearch.WordTrace tailWord_2169821 prefixEnd_2169821 371387035739820099686227 := by
  unfold tailWord_2169821
  simp only [CollatzResearch.WordTrace]
  refine ⟨79139873472116567768853317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52759915648077711845902211 79139873472116567768853317)
  ·
    refine ⟨14838726276021856456659997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79139873472116567768853317 14838726276021856456659997)
    ·
      refine ⟨5564522353508196171247499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14838726276021856456659997 5564522353508196171247499)
      ·
        refine ⟨8346783530262294256871249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564522353508196171247499 8346783530262294256871249)
        ·
          refine ⟨6260087647696720692653437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8346783530262294256871249 6260087647696720692653437)
          ·
            refine ⟨2347532867886270259745039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6260087647696720692653437 2347532867886270259745039)
            ·
              refine ⟨3521299301829405389617559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347532867886270259745039 3521299301829405389617559)
              ·
                refine ⟨5281948952744108084426339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521299301829405389617559 5281948952744108084426339)
                ·
                  refine ⟨7922923429116162126639509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5281948952744108084426339 7922923429116162126639509)
                  ·
                    refine ⟨371387035739820099686227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7922923429116162126639509 371387035739820099686227)
                    ·
                      rfl

theorem cell23_2169821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2169821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169821 prefixEnd_2169821 := by exact prefixLift 2169821
  have htrace : WordTrace (prefixWord ++ tailWord_2169821) baseStart_2169821 baseEnd_2169821 := by
    simpa [prefixWord, tailWord_2169821, baseEnd_2169821] using wordTrace_append hprefix tailTrace_2169821
  have hstable : (prefixWord ++ tailWord_2169821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169821).length < 2 ^ (prefixWord ++ tailWord_2169821).sum := by decide
  have hdescent : baseEnd_2169821 < baseStart_2169821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169831 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2169831 : Nat := 118140960795 + 2169831 * 2 ^ 59
def prefixEnd_2169831 : Nat := 4983230072969 + 3 ^ 40 * 2169831 * 2
def baseEnd_2169831 : Nat := 1114166242026005259933635

theorem tailTrace_2169831 : CollatzResearch.WordTrace tailWord_2169831 prefixEnd_2169831 1114166242026005259933635 := by
  unfold tailWord_2169831
  simp only [CollatzResearch.WordTrace]
  refine ⟨79140238202080339476717347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52760158801386892984478231 79140238202080339476717347)
  ·
    refine ⟨118710357303120509215076021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79140238202080339476717347 118710357303120509215076021)
    ·
      refine ⟨11129095997167547738913377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118710357303120509215076021 11129095997167547738913377)
      ·
        refine ⟨8346821997875660804185033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11129095997167547738913377 8346821997875660804185033)
        ·
          refine ⟨6260116498406745603138775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8346821997875660804185033 6260116498406745603138775)
          ·
            refine ⟨9390174747610118404708163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6260116498406745603138775 9390174747610118404708163)
            ·
              refine ⟨14085262121415177607062245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9390174747610118404708163 14085262121415177607062245)
              ·
                refine ⟨2640986647765345801324171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14085262121415177607062245 2640986647765345801324171)
                ·
                  refine ⟨3961479971648018701986257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640986647765345801324171 3961479971648018701986257)
                  ·
                    refine ⟨2971109978736014026489693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3961479971648018701986257 2971109978736014026489693)
                    ·
                      refine ⟨1114166242026005259933635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2971109978736014026489693 1114166242026005259933635)
                      ·
                        rfl

theorem cell23_2169831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2169831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169831 prefixEnd_2169831 := by exact prefixLift 2169831
  have htrace : WordTrace (prefixWord ++ tailWord_2169831) baseStart_2169831 baseEnd_2169831 := by
    simpa [prefixWord, tailWord_2169831, baseEnd_2169831] using wordTrace_append hprefix tailTrace_2169831
  have hstable : (prefixWord ++ tailWord_2169831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169831).length < 2 ^ (prefixWord ++ tailWord_2169831).sum := by decide
  have hdescent : baseEnd_2169831 < baseStart_2169831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169834 : List Nat := [3, 1, 3, 1, 2, 2, 4, 7]
def baseStart_2169834 : Nat := 118140960795 + 2169834 * 2 ^ 59
def prefixEnd_2169834 : Nat := 4983230072969 + 3 ^ 40 * 2169834 * 2
def baseEnd_2169834 : Nat := 41265473424739583266523

theorem tailTrace_2169834 : CollatzResearch.WordTrace tailWord_2169834 prefixEnd_2169834 41265473424739583266523 := by
  unfold tailWord_2169834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19785086905267367747269139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52760231747379647326051037 19785086905267367747269139)
  ·
    refine ⟨29677630357901051620903709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19785086905267367747269139 29677630357901051620903709)
    ·
      refine ⟨11129111384212894357838891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29677630357901051620903709 11129111384212894357838891)
      ·
        refine ⟨16693667076319341536758337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11129111384212894357838891 16693667076319341536758337)
        ·
          refine ⟨12520250307239506152568753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16693667076319341536758337 12520250307239506152568753)
          ·
            refine ⟨9390187730429629614426565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12520250307239506152568753 9390187730429629614426565)
            ·
              refine ⟨1760660199455555552704981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9390187730429629614426565 1760660199455555552704981)
              ·
                refine ⟨41265473424739583266523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1760660199455555552704981 41265473424739583266523)
                ·
                  rfl

theorem cell23_2169834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_2169834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169834 prefixEnd_2169834 := by exact prefixLift 2169834
  have htrace : WordTrace (prefixWord ++ tailWord_2169834) baseStart_2169834 baseEnd_2169834 := by
    simpa [prefixWord, tailWord_2169834, baseEnd_2169834] using wordTrace_append hprefix tailTrace_2169834
  have hstable : (prefixWord ++ tailWord_2169834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169834).length < 2 ^ (prefixWord ++ tailWord_2169834).sum := by decide
  have hdescent : baseEnd_2169834 < baseStart_2169834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169861 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_2169861 : Nat := 118140960795 + 2169861 * 2 ^ 59
def prefixEnd_2169861 : Nat := 4983230072969 + 3 ^ 40 * 2169861 * 2
def baseEnd_2169861 : Nat := 1114181646445640142558497

theorem tailTrace_2169861 : CollatzResearch.WordTrace tailWord_2169861 prefixEnd_2169861 1114181646445640142558497 := by
  unfold tailWord_2169861
  simp only [CollatzResearch.WordTrace]
  refine ⟨79141332391971654600309437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52760888261314436400206291 79141332391971654600309437)
  ·
    refine ⟨29677999646989370475116039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79141332391971654600309437 29677999646989370475116039)
    ·
      refine ⟨44516999470484055712674059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29677999646989370475116039 44516999470484055712674059)
      ·
        refine ⟨66775499205726083569011089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44516999470484055712674059 66775499205726083569011089)
        ·
          refine ⟨50081624404294562676758317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66775499205726083569011089 50081624404294562676758317)
          ·
            refine ⟨18780609151610461003784369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50081624404294562676758317 18780609151610461003784369)
            ·
              refine ⟨14085456863707845752838277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18780609151610461003784369 14085456863707845752838277)
              ·
                refine ⟨2641023161945221078657177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14085456863707845752838277 2641023161945221078657177)
                ·
                  refine ⟨1980767371458915808992883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641023161945221078657177 1980767371458915808992883)
                  ·
                    refine ⟨2971151057188373713489325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1980767371458915808992883 2971151057188373713489325)
                    ·
                      refine ⟨1114181646445640142558497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2971151057188373713489325 1114181646445640142558497)
                      ·
                        rfl

theorem cell23_2169861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_2169861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2169861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2169861 prefixEnd_2169861 := by exact prefixLift 2169861
  have htrace : WordTrace (prefixWord ++ tailWord_2169861) baseStart_2169861 baseEnd_2169861 := by
    simpa [prefixWord, tailWord_2169861, baseEnd_2169861] using wordTrace_append hprefix tailTrace_2169861
  have hstable : (prefixWord ++ tailWord_2169861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169861).length < 2 ^ (prefixWord ++ tailWord_2169861).sum := by decide
  have hdescent : baseEnd_2169861 < baseStart_2169861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170051 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 1, 5, 2]
def baseStart_2170051 : Nat := 118140960795 + 2170051 * 2 ^ 59
def prefixEnd_2170051 : Nat := 4983230072969 + 3 ^ 40 * 2170051 * 2
def baseEnd_2170051 : Nat := 1114279207769994399182623

theorem tailTrace_2170051 : CollatzResearch.WordTrace tailWord_2170051 prefixEnd_2170051 1114279207769994399182623 := by
  unfold tailWord_2170051
  simp only [CollatzResearch.WordTrace]
  refine ⟨79148262261283317049726007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52765508174188878033150671 79148262261283317049726007)
  ·
    refine ⟨118722393391924975574589011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79148262261283317049726007 118722393391924975574589011)
    ·
      refine ⟨178083590087887463361883517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118722393391924975574589011 178083590087887463361883517)
      ·
        refine ⟨66781346282957798760706319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178083590087887463361883517 66781346282957798760706319)
        ·
          refine ⟨100172019424436698141059479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66781346282957798760706319 100172019424436698141059479)
          ·
            refine ⟨150258029136655047211589219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100172019424436698141059479 150258029136655047211589219)
            ·
              refine ⟨225387043704982570817383829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150258029136655047211589219 225387043704982570817383829)
              ·
                refine ⟨10565017673671058007064867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225387043704982570817383829 10565017673671058007064867)
                ·
                  refine ⟨15847526510506587010597301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10565017673671058007064867 15847526510506587010597301)
                  ·
                    refine ⟨1485705610359992532243497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15847526510506587010597301 1485705610359992532243497)
                    ·
                      refine ⟨1114279207769994399182623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485705610359992532243497 1114279207769994399182623)
                      ·
                        rfl

theorem cell23_2170051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_2170051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170051 prefixEnd_2170051 := by exact prefixLift 2170051
  have htrace : WordTrace (prefixWord ++ tailWord_2170051) baseStart_2170051 baseEnd_2170051 := by
    simpa [prefixWord, tailWord_2170051, baseEnd_2170051] using wordTrace_append hprefix tailTrace_2170051
  have hstable : (prefixWord ++ tailWord_2170051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170051).length < 2 ^ (prefixWord ++ tailWord_2170051).sum := by decide
  have hdescent : baseEnd_2170051 < baseStart_2170051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170092 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 1, 1, 3]
def baseStart_2170092 : Nat := 118140960795 + 2170092 * 2 ^ 59
def prefixEnd_2170092 : Nat := 4983230072969 + 3 ^ 40 * 2170092 * 2
def baseEnd_2170092 : Nat := 1114300260476828738769935

theorem tailTrace_2170092 : CollatzResearch.WordTrace tailWord_2170092 prefixEnd_2170092 1114300260476828738769935 := by
  unfold tailWord_2170092
  simp only [CollatzResearch.WordTrace]
  refine ⟨39574878827067390525984265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52766505102756520701312353 39574878827067390525984265)
  ·
    refine ⟨29681159120300542894488199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39574878827067390525984265 29681159120300542894488199)
    ·
      refine ⟨44521738680450814341732299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29681159120300542894488199 44521738680450814341732299)
      ·
        refine ⟨66782608020676221512598449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44521738680450814341732299 66782608020676221512598449)
        ·
          refine ⟨50086956015507166134448837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66782608020676221512598449 50086956015507166134448837)
          ·
            refine ⟨9391304252907593650209157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50086956015507166134448837 9391304252907593650209157)
            ·
              refine ⟨1760869547420173809414217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9391304252907593650209157 1760869547420173809414217)
              ·
                refine ⟨1320652160565130357060663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760869547420173809414217 1320652160565130357060663)
                ·
                  refine ⟨1980978240847695535590995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320652160565130357060663 1980978240847695535590995)
                  ·
                    refine ⟨2971467361271543303386493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1980978240847695535590995 2971467361271543303386493)
                    ·
                      refine ⟨1114300260476828738769935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2971467361271543303386493 1114300260476828738769935)
                      ·
                        rfl

theorem cell23_2170092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_2170092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170092 prefixEnd_2170092 := by exact prefixLift 2170092
  have htrace : WordTrace (prefixWord ++ tailWord_2170092) baseStart_2170092 baseEnd_2170092 := by
    simpa [prefixWord, tailWord_2170092, baseEnd_2170092] using wordTrace_append hprefix tailTrace_2170092
  have hstable : (prefixWord ++ tailWord_2170092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170092).length < 2 ^ (prefixWord ++ tailWord_2170092).sum := by decide
  have hdescent : baseEnd_2170092 < baseStart_2170092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170108 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_2170108 : Nat := 118140960795 + 2170108 * 2 ^ 59
def prefixEnd_2170108 : Nat := 4983230072969 + 3 ^ 40 * 2170108 * 2
def baseEnd_2170108 : Nat := 371436158722433558723287

theorem tailTrace_2170108 : CollatzResearch.WordTrace tailWord_2170108 prefixEnd_2170108 371436158722433558723287 := by
  unfold tailWord_2170108
  simp only [CollatzResearch.WordTrace]
  refine ⟨39575170611038407892275489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52766894148051210523033985 39575170611038407892275489)
  ·
    refine ⟨29681377958278805919206617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39575170611038407892275489 29681377958278805919206617)
    ·
      refine ⟨22261033468709104439404963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29681377958278805919206617 22261033468709104439404963)
      ·
        refine ⟨33391550203063656659107445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22261033468709104439404963 33391550203063656659107445)
        ·
          refine ⟨3130457831537217811791323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33391550203063656659107445 3130457831537217811791323)
          ·
            refine ⟨4695686747305826717686985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130457831537217811791323 4695686747305826717686985)
            ·
              refine ⟨3521765060479370038265239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4695686747305826717686985 3521765060479370038265239)
              ·
                refine ⟨5282647590719055057397859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521765060479370038265239 5282647590719055057397859)
                ·
                  refine ⟨7923971386078582586096789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282647590719055057397859 7923971386078582586096789)
                  ·
                    refine ⟨371436158722433558723287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7923971386078582586096789 371436158722433558723287)
                    ·
                      rfl

theorem cell23_2170108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_2170108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170108 prefixEnd_2170108 := by exact prefixLift 2170108
  have htrace : WordTrace (prefixWord ++ tailWord_2170108) baseStart_2170108 baseEnd_2170108 := by
    simpa [prefixWord, tailWord_2170108, baseEnd_2170108] using wordTrace_append hprefix tailTrace_2170108
  have hstable : (prefixWord ++ tailWord_2170108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170108).length < 2 ^ (prefixWord ++ tailWord_2170108).sum := by decide
  have hdescent : baseEnd_2170108 < baseStart_2170108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170111 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_2170111 : Nat := 118140960795 + 2170111 * 2 ^ 59
def prefixEnd_2170111 : Nat := 4983230072969 + 3 ^ 40 * 2170111 * 2
def baseEnd_2170111 : Nat := 1114310016609264164432347

theorem tailTrace_2170111 : CollatzResearch.WordTrace tailWord_2170111 prefixEnd_2170111 1114310016609264164432347 := by
  unfold tailWord_2170111
  simp only [CollatzResearch.WordTrace]
  refine ⟨79150450641065947296910187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52766967094043964864606791 79150450641065947296910187)
  ·
    refine ⟨118725675961598920945365281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79150450641065947296910187 118725675961598920945365281)
    ·
      refine ⟨89044256971199190709023961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118725675961598920945365281 89044256971199190709023961)
      ·
        refine ⟨66783192728399393031767971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89044256971199190709023961 66783192728399393031767971)
        ·
          refine ⟨100174789092599089547651957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66783192728399393031767971 100174789092599089547651957)
          ·
            refine ⟨9391386477431164645092371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100174789092599089547651957 9391386477431164645092371)
            ·
              refine ⟨14087079716146746967638557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9391386477431164645092371 14087079716146746967638557)
              ·
                refine ⟨5282654893555030112864459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14087079716146746967638557 5282654893555030112864459)
                ·
                  refine ⟨7923982340332545169296689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282654893555030112864459 7923982340332545169296689)
                  ·
                    refine ⟨5942986755249408876972517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7923982340332545169296689 5942986755249408876972517)
                    ·
                      refine ⟨1114310016609264164432347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5942986755249408876972517 1114310016609264164432347)
                      ·
                        rfl

theorem cell23_2170111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_2170111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170111 prefixEnd_2170111 := by exact prefixLift 2170111
  have htrace : WordTrace (prefixWord ++ tailWord_2170111) baseStart_2170111 baseEnd_2170111 := by
    simpa [prefixWord, tailWord_2170111, baseEnd_2170111] using wordTrace_append hprefix tailTrace_2170111
  have hstable : (prefixWord ++ tailWord_2170111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170111).length < 2 ^ (prefixWord ++ tailWord_2170111).sum := by decide
  have hdescent : baseEnd_2170111 < baseStart_2170111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170115 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 3, 2, 2]
def baseStart_2170115 : Nat := 118140960795 + 2170115 * 2 ^ 59
def prefixEnd_2170115 : Nat := 4983230072969 + 3 ^ 40 * 2170115 * 2
def baseEnd_2170115 : Nat := 1114312070531882148782329

theorem tailTrace_2170115 : CollatzResearch.WordTrace tailWord_2170115 prefixEnd_2170115 1114312070531882148782329 := by
  unfold tailWord_2170115
  simp only [CollatzResearch.WordTrace]
  refine ⟨79150596533051455980055799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52767064355367637320037199 79150596533051455980055799)
  ·
    refine ⟨118725894799577183970083699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79150596533051455980055799 118725894799577183970083699)
    ·
      refine ⟨178088842199365775955125549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118725894799577183970083699 178088842199365775955125549)
      ·
        refine ⟨66783315824762165983172081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178088842199365775955125549 66783315824762165983172081)
        ·
          refine ⟨50087486868571624487379061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66783315824762165983172081 50087486868571624487379061)
          ·
            refine ⟨4695701893928589795691787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50087486868571624487379061 4695701893928589795691787)
            ·
              refine ⟨7043552840892884693537681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695701893928589795691787 7043552840892884693537681)
              ·
                refine ⟨5282664630669663520153261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7043552840892884693537681 5282664630669663520153261)
                ·
                  refine ⟨1980999236501123820057473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5282664630669663520153261 1980999236501123820057473)
                  ·
                    refine ⟨1485749427375842865043105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1980999236501123820057473 1485749427375842865043105)
                    ·
                      refine ⟨1114312070531882148782329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1485749427375842865043105 1114312070531882148782329)
                      ·
                        rfl

theorem cell23_2170115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_2170115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170115 prefixEnd_2170115 := by exact prefixLift 2170115
  have htrace : WordTrace (prefixWord ++ tailWord_2170115) baseStart_2170115 baseEnd_2170115 := by
    simpa [prefixWord, tailWord_2170115, baseEnd_2170115] using wordTrace_append hprefix tailTrace_2170115
  have hstable : (prefixWord ++ tailWord_2170115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170115).length < 2 ^ (prefixWord ++ tailWord_2170115).sum := by decide
  have hdescent : baseEnd_2170115 < baseStart_2170115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170121 : List Nat := [1, 2, 1, 1, 3, 3, 5, 7]
def baseStart_2170121 : Nat := 118140960795 + 2170121 * 2 ^ 59
def prefixEnd_2170121 : Nat := 4983230072969 + 3 ^ 40 * 2170121 * 2
def baseEnd_2170121 : Nat := 41270931533918856492863

theorem tailTrace_2170121 : CollatzResearch.WordTrace tailWord_2170121 prefixEnd_2170121 41270931533918856492863 := by
  unfold tailWord_2170121
  simp only [CollatzResearch.WordTrace]
  refine ⟨79150815371029719004774217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52767210247353146003182811 79150815371029719004774217)
  ·
    refine ⟨59363111528272289253580663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79150815371029719004774217 59363111528272289253580663)
    ·
      refine ⟨89044667292408433880370995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59363111528272289253580663 89044667292408433880370995)
      ·
        refine ⟨133567000938612650820556493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89044667292408433880370995 133567000938612650820556493)
        ·
          refine ⟨50087625351979744057708685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133567000938612650820556493 50087625351979744057708685)
          ·
            refine ⟨18782859506992404021640757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50087625351979744057708685 18782859506992404021640757)
            ·
              refine ⟨1760893078780537877028821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18782859506992404021640757 1760893078780537877028821)
              ·
                refine ⟨41270931533918856492863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1760893078780537877028821 41270931533918856492863)
                ·
                  rfl

theorem cell23_2170121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 7].length) (baseStart_2170121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170121 prefixEnd_2170121 := by exact prefixLift 2170121
  have htrace : WordTrace (prefixWord ++ tailWord_2170121) baseStart_2170121 baseEnd_2170121 := by
    simpa [prefixWord, tailWord_2170121, baseEnd_2170121] using wordTrace_append hprefix tailTrace_2170121
  have hstable : (prefixWord ++ tailWord_2170121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170121).length < 2 ^ (prefixWord ++ tailWord_2170121).sum := by decide
  have hdescent : baseEnd_2170121 < baseStart_2170121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170142 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2170142 : Nat := 118140960795 + 2170142 * 2 ^ 59
def prefixEnd_2170142 : Nat := 4983230072969 + 3 ^ 40 * 2170142 * 2
def baseEnd_2170142 : Nat := 371441978169851181048235

theorem tailTrace_2170142 : CollatzResearch.WordTrace tailWord_2170142 prefixEnd_2170142 371441978169851181048235 := by
  unfold tailWord_2170142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9893947662994204948911085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52767720869302426394192453 9893947662994204948911085)
  ·
    refine ⟨3710230373622826855841657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9893947662994204948911085 3710230373622826855841657)
    ·
      refine ⟨2782672780217120141881243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3710230373622826855841657 2782672780217120141881243)
      ·
        refine ⟨4174009170325680212821865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782672780217120141881243 4174009170325680212821865)
        ·
          refine ⟨3130506877744260159616399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4174009170325680212821865 3130506877744260159616399)
          ·
            refine ⟨4695760316616390239424599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130506877744260159616399 4695760316616390239424599)
            ·
              refine ⟨7043640474924585359136899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695760316616390239424599 7043640474924585359136899)
              ·
                refine ⟨10565460712386878038705349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043640474924585359136899 10565460712386878038705349)
                ·
                  refine ⟨1981023883572539632257253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10565460712386878038705349 1981023883572539632257253)
                  ·
                    refine ⟨371441978169851181048235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1981023883572539632257253 371441978169851181048235)
                    ·
                      rfl

theorem cell23_2170142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2170142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170142 prefixEnd_2170142 := by exact prefixLift 2170142
  have htrace : WordTrace (prefixWord ++ tailWord_2170142) baseStart_2170142 baseEnd_2170142 := by
    simpa [prefixWord, tailWord_2170142, baseEnd_2170142] using wordTrace_append hprefix tailTrace_2170142
  have hstable : (prefixWord ++ tailWord_2170142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170142).length < 2 ^ (prefixWord ++ tailWord_2170142).sum := by decide
  have hdescent : baseEnd_2170142 < baseStart_2170142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170165 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2170165 : Nat := 118140960795 + 2170165 * 2 ^ 59
def prefixEnd_2170165 : Nat := 4983230072969 + 3 ^ 40 * 2170165 * 2
def baseEnd_2170165 : Nat := 1114337744564606953157099

theorem tailTrace_2170165 : CollatzResearch.WordTrace tailWord_2170165 prefixEnd_2170165 1114337744564606953157099 := by
  unfold tailWord_2170165
  simp only [CollatzResearch.WordTrace]
  refine ⟨79152420182870314519375949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52768280121913543012917299 79152420182870314519375949)
  ·
    refine ⟨29682157568576367944765981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79152420182870314519375949 29682157568576367944765981)
    ·
      refine ⟨11130809088216137979287243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29682157568576367944765981 11130809088216137979287243)
      ·
        refine ⟨16696213632324206968930865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11130809088216137979287243 16696213632324206968930865)
        ·
          refine ⟨12522160224243155226698149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16696213632324206968930865 12522160224243155226698149)
          ·
            refine ⟨2347905042045591605005903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12522160224243155226698149 2347905042045591605005903)
            ·
              refine ⟨3521857563068387407508855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347905042045591605005903 3521857563068387407508855)
              ·
                refine ⟨5282786344602581111263283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521857563068387407508855 5282786344602581111263283)
                ·
                  refine ⟨7924179516903871666894925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282786344602581111263283 7924179516903871666894925)
                  ·
                    refine ⟨2971567318838951875085597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7924179516903871666894925 2971567318838951875085597)
                    ·
                      refine ⟨1114337744564606953157099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2971567318838951875085597 1114337744564606953157099)
                      ·
                        rfl

theorem cell23_2170165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2170165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2170165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2170165 prefixEnd_2170165 := by exact prefixLift 2170165
  have htrace : WordTrace (prefixWord ++ tailWord_2170165) baseStart_2170165 baseEnd_2170165 := by
    simpa [prefixWord, tailWord_2170165, baseEnd_2170165] using wordTrace_append hprefix tailTrace_2170165
  have hstable : (prefixWord ++ tailWord_2170165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170165).length < 2 ^ (prefixWord ++ tailWord_2170165).sum := by decide
  have hdescent : baseEnd_2170165 < baseStart_2170165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
