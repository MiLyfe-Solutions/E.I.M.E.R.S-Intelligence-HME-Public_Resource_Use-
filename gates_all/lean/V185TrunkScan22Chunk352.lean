import V185TrunkScan22Chunk351

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3140349 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3140349 : Nat := 118140960795 + 3140349 * 2 ^ 59
def prefixEnd_3140349 : Nat := 4983230072969 + 3 ^ 40 * 3140349 * 2
def baseEnd_3140349 : Nat := 1075005639910826069196869

theorem tailTrace_3140349 : CollatzResearch.WordTrace tailWord_3140349 prefixEnd_3140349 1075005639910826069196869 := by
  unfold tailWord_3140349
  simp only [CollatzResearch.WordTrace]
  refine ⟨114537937700059376754984101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76358625133372917836656067 114537937700059376754984101)
  ·
    refine ⟨21475863318761133141559519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114537937700059376754984101 21475863318761133141559519)
    ·
      refine ⟨32213794978141699712339279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21475863318761133141559519 32213794978141699712339279)
      ·
        refine ⟨48320692467212549568508919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32213794978141699712339279 48320692467212549568508919)
        ·
          refine ⟨72481038700818824352763379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48320692467212549568508919 72481038700818824352763379)
          ·
            refine ⟨108721558051228236529145069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72481038700818824352763379 108721558051228236529145069)
            ·
              refine ⟨40770584269210588698429401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108721558051228236529145069 40770584269210588698429401)
              ·
                refine ⟨30577938201907941523822051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40770584269210588698429401 30577938201907941523822051)
                ·
                  refine ⟨45866907302861912285733077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30577938201907941523822051 45866907302861912285733077)
                  ·
                    refine ⟨1075005639910826069196869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45866907302861912285733077 1075005639910826069196869)
                    ·
                      rfl

theorem cell22_3140349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3140349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140349 prefixEnd_3140349 := by exact prefixLift 3140349
  have htrace : WordTrace (prefixWord ++ tailWord_3140349) baseStart_3140349 baseEnd_3140349 := by
    simpa [prefixWord, tailWord_3140349, baseEnd_3140349] using wordTrace_append hprefix tailTrace_3140349
  have hstable : (prefixWord ++ tailWord_3140349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140349).length < 2 ^ (prefixWord ++ tailWord_3140349).sum := by decide
  have hdescent : baseEnd_3140349 < baseStart_3140349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140406 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3140406 : Nat := 118140960795 + 3140406 * 2 ^ 59
def prefixEnd_3140406 : Nat := 4983230072969 + 3 ^ 40 * 3140406 * 2
def baseEnd_3140406 : Nat := 1075025152175696920521695

theorem tailTrace_3140406 : CollatzResearch.WordTrace tailWord_3140406 prefixEnd_3140406 1075025152175696920521695 := by
  unfold tailWord_3140406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158751041303304718113067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76360011107235250326539381 7158751041303304718113067)
  ·
    refine ⟨10738126561954957077169601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7158751041303304718113067 10738126561954957077169601)
    ·
      refine ⟨8053594921466217807877201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10738126561954957077169601 8053594921466217807877201)
      ·
        refine ⟨6040196191099663355907901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8053594921466217807877201 6040196191099663355907901)
        ·
          refine ⟨2265073571662373758465463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6040196191099663355907901 2265073571662373758465463)
          ·
            refine ⟨3397610357493560637698195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265073571662373758465463 3397610357493560637698195)
            ·
              refine ⟨5096415536240340956547293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397610357493560637698195 5096415536240340956547293)
              ·
                refine ⟨1911155826090127858705235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5096415536240340956547293 1911155826090127858705235)
                ·
                  refine ⟨2866733739135191788057853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911155826090127858705235 2866733739135191788057853)
                  ·
                    refine ⟨1075025152175696920521695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866733739135191788057853 1075025152175696920521695)
                    ·
                      rfl

theorem cell22_3140406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3140406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140406 prefixEnd_3140406 := by exact prefixLift 3140406
  have htrace : WordTrace (prefixWord ++ tailWord_3140406) baseStart_3140406 baseEnd_3140406 := by
    simpa [prefixWord, tailWord_3140406, baseEnd_3140406] using wordTrace_append hprefix tailTrace_3140406
  have hstable : (prefixWord ++ tailWord_3140406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140406).length < 2 ^ (prefixWord ++ tailWord_3140406).sum := by decide
  have hdescent : baseEnd_3140406 < baseStart_3140406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140428 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_3140428 : Nat := 118140960795 + 3140428 * 2 ^ 59
def prefixEnd_3140428 : Nat := 4983230072969 + 3 ^ 40 * 3140428 * 2
def baseEnd_3140428 : Nat := 1075032683225296196471627

theorem tailTrace_3140428 : CollatzResearch.WordTrace tailWord_3140428 prefixEnd_3140428 1075032683225296196471627 := by
  unfold tailWord_3140428
  simp only [CollatzResearch.WordTrace]
  refine ⟨57270409533386586623554969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76360546044515448831406625 57270409533386586623554969)
  ·
    refine ⟨42952807150039939967666227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57270409533386586623554969 42952807150039939967666227)
    ·
      refine ⟨64429210725059909951499341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42952807150039939967666227 64429210725059909951499341)
      ·
        refine ⟨24160954021897466231812253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64429210725059909951499341 24160954021897466231812253)
        ·
          refine ⟨9060357758211549836929595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24160954021897466231812253 9060357758211549836929595)
          ·
            refine ⟨13590536637317324755394393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9060357758211549836929595 13590536637317324755394393)
            ·
              refine ⟨10192902477987993566545795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13590536637317324755394393 10192902477987993566545795)
              ·
                refine ⟨15289353716981990349818693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10192902477987993566545795 15289353716981990349818693)
                ·
                  refine ⟨2866753821934123190591005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15289353716981990349818693 2866753821934123190591005)
                  ·
                    refine ⟨1075032683225296196471627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866753821934123190591005 1075032683225296196471627)
                    ·
                      rfl

theorem cell22_3140428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_3140428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140428 prefixEnd_3140428 := by exact prefixLift 3140428
  have htrace : WordTrace (prefixWord ++ tailWord_3140428) baseStart_3140428 baseEnd_3140428 := by
    simpa [prefixWord, tailWord_3140428, baseEnd_3140428] using wordTrace_append hprefix tailTrace_3140428
  have hstable : (prefixWord ++ tailWord_3140428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140428).length < 2 ^ (prefixWord ++ tailWord_3140428).sum := by decide
  have hdescent : baseEnd_3140428 < baseStart_3140428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140441 : List Nat := [1, 2, 1, 2, 2, 5, 2, 7]
def baseStart_3140441 : Nat := 118140960795 + 3140441 * 2 ^ 59
def prefixEnd_3140441 : Nat := 4983230072969 + 3 ^ 40 * 3140441 * 2
def baseEnd_3140441 : Nat := 119448570376774277321843

theorem tailTrace_3140441 : CollatzResearch.WordTrace tailWord_3140441 prefixEnd_3140441 119448570376774277321843 := by
  unfold tailWord_3140441
  simp only [CollatzResearch.WordTrace]
  refine ⟨114541293215726076467333177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76360862143817384311555451 114541293215726076467333177)
  ·
    refine ⟨85905969911794557350499883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114541293215726076467333177 85905969911794557350499883)
    ·
      refine ⟨128858954867691836025749825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85905969911794557350499883 128858954867691836025749825)
      ·
        refine ⟨96644216150768877019312369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128858954867691836025749825 96644216150768877019312369)
        ·
          refine ⟨72483162113076657764484277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96644216150768877019312369 72483162113076657764484277)
          ·
            refine ⟨6795296448100936665420401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72483162113076657764484277 6795296448100936665420401)
            ·
              refine ⟨5096472336075702499065301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6795296448100936665420401 5096472336075702499065301)
              ·
                refine ⟨119448570376774277321843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5096472336075702499065301 119448570376774277321843)
                ·
                  rfl

theorem cell22_3140441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 7].length) (baseStart_3140441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140441 prefixEnd_3140441 := by exact prefixLift 3140441
  have htrace : WordTrace (prefixWord ++ tailWord_3140441) baseStart_3140441 baseEnd_3140441 := by
    simpa [prefixWord, tailWord_3140441, baseEnd_3140441] using wordTrace_append hprefix tailTrace_3140441
  have hstable : (prefixWord ++ tailWord_3140441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140441).length < 2 ^ (prefixWord ++ tailWord_3140441).sum := by decide
  have hdescent : baseEnd_3140441 < baseStart_3140441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140501 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3140501 : Nat := 118140960795 + 3140501 * 2 ^ 59
def prefixEnd_3140501 : Nat := 4983230072969 + 3 ^ 40 * 3140501 * 2
def baseEnd_3140501 : Nat := 1075057672617148339396403

theorem tailTrace_3140501 : CollatzResearch.WordTrace tailWord_3140501 prefixEnd_3140501 1075057672617148339396403 := by
  unfold tailWord_3140501
  simp only [CollatzResearch.WordTrace]
  refine ⟨114543481595508706714517357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76362321063672471143011571 114543481595508706714517357)
  ·
    refine ⟨42953805598315765017944009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114543481595508706714517357 42953805598315765017944009)
    ·
      refine ⟨32215354198736823763458007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42953805598315765017944009 32215354198736823763458007)
      ·
        refine ⟨48323031298105235645187011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32215354198736823763458007 48323031298105235645187011)
        ·
          refine ⟨72484546947157853467780517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48323031298105235645187011 72484546947157853467780517)
          ·
            refine ⟨13590852552592097525208847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72484546947157853467780517 13590852552592097525208847)
            ·
              refine ⟨20386278828888146287813271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13590852552592097525208847 20386278828888146287813271)
              ·
                refine ⟨30579418243332219431719907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20386278828888146287813271 30579418243332219431719907)
                ·
                  refine ⟨45869127364998329147579861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30579418243332219431719907 45869127364998329147579861)
                  ·
                    refine ⟨1075057672617148339396403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45869127364998329147579861 1075057672617148339396403)
                    ·
                      rfl

theorem cell22_3140501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3140501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140501 prefixEnd_3140501 := by exact prefixLift 3140501
  have htrace : WordTrace (prefixWord ++ tailWord_3140501) baseStart_3140501 baseEnd_3140501 := by
    simpa [prefixWord, tailWord_3140501, baseEnd_3140501] using wordTrace_append hprefix tailTrace_3140501
  have hstable : (prefixWord ++ tailWord_3140501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140501).length < 2 ^ (prefixWord ++ tailWord_3140501).sum := by decide
  have hdescent : baseEnd_3140501 < baseStart_3140501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140561 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3140561 : Nat := 118140960795 + 3140561 * 2 ^ 59
def prefixEnd_3140561 : Nat := 4983230072969 + 3 ^ 40 * 3140561 * 2
def baseEnd_3140561 : Nat := 1075078211843328182896219

theorem tailTrace_3140561 : CollatzResearch.WordTrace tailWord_3140561 prefixEnd_3140561 1075078211843328182896219 := by
  unfold tailWord_3140561
  simp only [CollatzResearch.WordTrace]
  refine ⟨114545669975291336961701537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76363779983527557974467691 114545669975291336961701537)
  ·
    refine ⟨85909252481468502721276153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114545669975291336961701537 85909252481468502721276153)
    ·
      refine ⟨64431939361101377040957115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85909252481468502721276153 64431939361101377040957115)
      ·
        refine ⟨96647909041652065561435673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64431939361101377040957115 96647909041652065561435673)
        ·
          refine ⟨72485931781239049171076755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96647909041652065561435673 72485931781239049171076755)
          ·
            refine ⟨108728897671858573756615133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72485931781239049171076755 108728897671858573756615133)
            ·
              refine ⟨40773336626946965158730675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108728897671858573756615133 40773336626946965158730675)
              ·
                refine ⟨61160004940420447738096013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40773336626946965158730675 61160004940420447738096013)
                ·
                  refine ⟨22935001852657667901786005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61160004940420447738096013 22935001852657667901786005)
                  ·
                    refine ⟨1075078211843328182896219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22935001852657667901786005 1075078211843328182896219)
                    ·
                      rfl

theorem cell22_3140561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3140561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140561 prefixEnd_3140561 := by exact prefixLift 3140561
  have htrace : WordTrace (prefixWord ++ tailWord_3140561) baseStart_3140561 baseEnd_3140561 := by
    simpa [prefixWord, tailWord_3140561, baseEnd_3140561] using wordTrace_append hprefix tailTrace_3140561
  have hstable : (prefixWord ++ tailWord_3140561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140561).length < 2 ^ (prefixWord ++ tailWord_3140561).sum := by decide
  have hdescent : baseEnd_3140561 < baseStart_3140561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140593 : List Nat := [1, 2, 2, 2, 4, 3, 8]
def baseStart_3140593 : Nat := 118140960795 + 3140593 * 2 ^ 59
def prefixEnd_3140593 : Nat := 4983230072969 + 3 ^ 40 * 3140593 * 2
def baseEnd_3140593 : Nat := 39818117262862620966523

theorem tailTrace_3140593 : CollatzResearch.WordTrace tailWord_3140593 prefixEnd_3140593 39818117262862620966523 := by
  unfold tailWord_3140593
  simp only [CollatzResearch.WordTrace]
  refine ⟨114546837111175406426866433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76364558074116937617910955 114546837111175406426866433)
  ·
    refine ⟨85910127833381554820149825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114546837111175406426866433 85910127833381554820149825)
    ·
      refine ⟨64432595875036166115112369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85910127833381554820149825 64432595875036166115112369)
      ·
        refine ⟨48324446906277124586334277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64432595875036166115112369 48324446906277124586334277)
        ·
          refine ⟨9060833794926960859937677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48324446906277124586334277 9060833794926960859937677)
          ·
            refine ⟨3397812673097610322476629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9060833794926960859937677 3397812673097610322476629)
            ·
              refine ⟨39818117262862620966523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3397812673097610322476629 39818117262862620966523)
              ·
                rfl

theorem cell22_3140593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 8].length) (baseStart_3140593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140593 prefixEnd_3140593 := by exact prefixLift 3140593
  have htrace : WordTrace (prefixWord ++ tailWord_3140593) baseStart_3140593 baseEnd_3140593 := by
    simpa [prefixWord, tailWord_3140593, baseEnd_3140593] using wordTrace_append hprefix tailTrace_3140593
  have hstable : (prefixWord ++ tailWord_3140593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140593).length < 2 ^ (prefixWord ++ tailWord_3140593).sum := by decide
  have hdescent : baseEnd_3140593 < baseStart_3140593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140670 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_3140670 : Nat := 118140960795 + 3140670 * 2 ^ 59
def prefixEnd_3140670 : Nat := 4983230072969 + 3 ^ 40 * 3140670 * 2
def baseEnd_3140670 : Nat := 1075115524770888231920885

theorem tailTrace_3140670 : CollatzResearch.WordTrace tailWord_3140670 prefixEnd_3140670 1075115524770888231920885 := by
  unfold tailWord_3140670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14318705691487056072177433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76366430354597632384946309 14318705691487056072177433)
  ·
    refine ⟨10739029268615292054133075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14318705691487056072177433 10739029268615292054133075)
    ·
      refine ⟨16108543902922938081199613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10739029268615292054133075 16108543902922938081199613)
      ·
        refine ⟨6040703963596101780449855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16108543902922938081199613 6040703963596101780449855)
        ·
          refine ⟨9061055945394152670674783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040703963596101780449855 9061055945394152670674783)
          ·
            refine ⟨13591583918091229006012175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9061055945394152670674783 13591583918091229006012175)
            ·
              refine ⟨20387375877136843509018263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13591583918091229006012175 20387375877136843509018263)
              ·
                refine ⟨30581063815705265263527395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20387375877136843509018263 30581063815705265263527395)
                ·
                  refine ⟨45871595723557897895291093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30581063815705265263527395 45871595723557897895291093)
                  ·
                    refine ⟨1075115524770888231920885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45871595723557897895291093 1075115524770888231920885)
                    ·
                      rfl

theorem cell22_3140670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_3140670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140670 prefixEnd_3140670 := by exact prefixLift 3140670
  have htrace : WordTrace (prefixWord ++ tailWord_3140670) baseStart_3140670 baseEnd_3140670 := by
    simpa [prefixWord, tailWord_3140670, baseEnd_3140670] using wordTrace_append hprefix tailTrace_3140670
  have hstable : (prefixWord ++ tailWord_3140670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140670).length < 2 ^ (prefixWord ++ tailWord_3140670).sum := by decide
  have hdescent : baseEnd_3140670 < baseStart_3140670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140698 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_3140698 : Nat := 118140960795 + 3140698 * 2 ^ 59
def prefixEnd_3140698 : Nat := 4983230072969 + 3 ^ 40 * 3140698 * 2
def baseEnd_3140698 : Nat := 1075125109743105492220799

theorem tailTrace_3140698 : CollatzResearch.WordTrace tailWord_3140698 prefixEnd_3140698 1075125109743105492220799 := by
  unfold tailWord_3140698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28637666693948752339859687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76367111183863339572959165 28637666693948752339859687)
  ·
    refine ⟨42956500040923128509789531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28637666693948752339859687 42956500040923128509789531)
    ·
      refine ⟨64434750061384692764684297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42956500040923128509789531 64434750061384692764684297)
      ·
        refine ⟨48326062546038519573513223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64434750061384692764684297 48326062546038519573513223)
        ·
          refine ⟨72489093819057779360269835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48326062546038519573513223 72489093819057779360269835)
          ·
            refine ⟨108733640728586669040404753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72489093819057779360269835 108733640728586669040404753)
            ·
              refine ⟨81550230546440001780303565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108733640728586669040404753 81550230546440001780303565)
              ·
                refine ⟨30581336454915000667613837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81550230546440001780303565 30581336454915000667613837)
                ·
                  refine ⟨11468001170593125250355189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30581336454915000667613837 11468001170593125250355189)
                  ·
                    refine ⟨1075125109743105492220799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11468001170593125250355189 1075125109743105492220799)
                    ·
                      rfl

theorem cell22_3140698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_3140698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140698 prefixEnd_3140698 := by exact prefixLift 3140698
  have htrace : WordTrace (prefixWord ++ tailWord_3140698) baseStart_3140698 baseEnd_3140698 := by
    simpa [prefixWord, tailWord_3140698, baseEnd_3140698] using wordTrace_append hprefix tailTrace_3140698
  have hstable : (prefixWord ++ tailWord_3140698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140698).length < 2 ^ (prefixWord ++ tailWord_3140698).sum := by decide
  have hdescent : baseEnd_3140698 < baseStart_3140698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140717 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 4]
def baseStart_3140717 : Nat := 118140960795 + 3140717 * 2 ^ 59
def prefixEnd_3140717 : Nat := 4983230072969 + 3 ^ 40 * 3140717 * 2
def baseEnd_3140717 : Nat := 358377204610465258665247

theorem tailTrace_3140717 : CollatzResearch.WordTrace tailWord_3140717 prefixEnd_3140717 358377204610465258665247 := by
  unfold tailWord_3140717
  simp only [CollatzResearch.WordTrace]
  refine ⟨114551359762726175604380405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76367573175150783736253603 114551359762726175604380405)
  ·
    refine ⟨10739189977755578962910663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114551359762726175604380405 10739189977755578962910663)
    ·
      refine ⟨16108784966633368444365995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10739189977755578962910663 16108784966633368444365995)
      ·
        refine ⟨24163177449950052666548993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16108784966633368444365995 24163177449950052666548993)
        ·
          refine ⟨18122383087462539499911745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24163177449950052666548993 18122383087462539499911745)
          ·
            refine ⟨13591787315596904624933809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18122383087462539499911745 13591787315596904624933809)
            ·
              refine ⟨10193840486697678468700357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13591787315596904624933809 10193840486697678468700357)
              ·
                refine ⟨1911345091255814712881317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10193840486697678468700357 1911345091255814712881317)
                ·
                  refine ⟨358377204610465258665247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911345091255814712881317 358377204610465258665247)
                  ·
                    rfl

theorem cell22_3140717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_3140717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140717 prefixEnd_3140717 := by exact prefixLift 3140717
  have htrace : WordTrace (prefixWord ++ tailWord_3140717) baseStart_3140717 baseEnd_3140717 := by
    simpa [prefixWord, tailWord_3140717, baseEnd_3140717] using wordTrace_append hprefix tailTrace_3140717
  have hstable : (prefixWord ++ tailWord_3140717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140717).length < 2 ^ (prefixWord ++ tailWord_3140717).sum := by decide
  have hdescent : baseEnd_3140717 < baseStart_3140717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140743 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3140743 : Nat := 118140960795 + 3140743 * 2 ^ 59
def prefixEnd_3140743 : Nat := 4983230072969 + 3 ^ 40 * 3140743 * 2
def baseEnd_3140743 : Nat := 1075140514162740374845661

theorem tailTrace_3140743 : CollatzResearch.WordTrace tailWord_3140743 prefixEnd_3140743 1075140514162740374845661 := by
  unfold tailWord_3140743
  simp only [CollatzResearch.WordTrace]
  refine ⟨114552308060631982044826883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76368205373754654696551255 114552308060631982044826883)
  ·
    refine ⟨171828462090947973067240325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114552308060631982044826883 171828462090947973067240325)
    ·
      refine ⟨32217836642052744950107561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171828462090947973067240325 32217836642052744950107561)
      ·
        refine ⟨24163377481539558712580671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32217836642052744950107561 24163377481539558712580671)
        ·
          refine ⟨36245066222309338068871007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24163377481539558712580671 36245066222309338068871007)
          ·
            refine ⟨54367599333464007103306511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36245066222309338068871007 54367599333464007103306511)
            ·
              refine ⟨81551399000196010654959767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54367599333464007103306511 81551399000196010654959767)
              ·
                refine ⟨122327098500294015982439651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81551399000196010654959767 122327098500294015982439651)
                ·
                  refine ⟨183490647750441023973659477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122327098500294015982439651 183490647750441023973659477)
                  ·
                    refine ⟨1075140514162740374845661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 183490647750441023973659477 1075140514162740374845661)
                    ·
                      rfl

theorem cell22_3140743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3140743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140743 prefixEnd_3140743 := by exact prefixLift 3140743
  have htrace : WordTrace (prefixWord ++ tailWord_3140743) baseStart_3140743 baseEnd_3140743 := by
    simpa [prefixWord, tailWord_3140743, baseEnd_3140743] using wordTrace_append hprefix tailTrace_3140743
  have hstable : (prefixWord ++ tailWord_3140743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140743).length < 2 ^ (prefixWord ++ tailWord_3140743).sum := by decide
  have hdescent : baseEnd_3140743 < baseStart_3140743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140745 : List Nat := [1, 2, 1, 1, 4, 3, 4, 6]
def baseStart_3140745 : Nat := 118140960795 + 3140745 * 2 ^ 59
def prefixEnd_3140745 : Nat := 4983230072969 + 3 ^ 40 * 3140745 * 2
def baseEnd_3140745 : Nat := 119460133200401448477295

theorem tailTrace_3140745 : CollatzResearch.WordTrace tailWord_3140745 prefixEnd_3140745 119460133200401448477295 := by
  unfold tailWord_3140745
  simp only [CollatzResearch.WordTrace]
  refine ⟨114552381006624736386399689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76368254004416490924266459 114552381006624736386399689)
  ·
    refine ⟨85914285754968552289799767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114552381006624736386399689 85914285754968552289799767)
    ·
      refine ⟨128871428632452828434699651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85914285754968552289799767 128871428632452828434699651)
      ·
        refine ⟨193307142948679242652049477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128871428632452828434699651 193307142948679242652049477)
        ·
          refine ⟨36245089302877357997259277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193307142948679242652049477 36245089302877357997259277)
          ·
            refine ⟨13591908488579009248972229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36245089302877357997259277 13591908488579009248972229)
            ·
              refine ⟨2548482841608564234182293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13591908488579009248972229 2548482841608564234182293)
              ·
                refine ⟨119460133200401448477295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2548482841608564234182293 119460133200401448477295)
                ·
                  rfl

theorem cell22_3140745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 6].length) (baseStart_3140745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140745 prefixEnd_3140745 := by exact prefixLift 3140745
  have htrace : WordTrace (prefixWord ++ tailWord_3140745) baseStart_3140745 baseEnd_3140745 := by
    simpa [prefixWord, tailWord_3140745, baseEnd_3140745] using wordTrace_append hprefix tailTrace_3140745
  have hstable : (prefixWord ++ tailWord_3140745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140745).length < 2 ^ (prefixWord ++ tailWord_3140745).sum := by decide
  have hdescent : baseEnd_3140745 < baseStart_3140745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140901 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_3140901 : Nat := 118140960795 + 3140901 * 2 ^ 59
def prefixEnd_3140901 : Nat := 4983230072969 + 3 ^ 40 * 3140901 * 2
def baseEnd_3140901 : Nat := 1075194600791680629395177

theorem tailTrace_3140901 : CollatzResearch.WordTrace tailWord_3140901 prefixEnd_3140901 1075194600791680629395177 := by
  unfold tailWord_3140901
  simp only [CollatzResearch.WordTrace]
  refine ⟨114558070794059575029078557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76372047196039716686052371 114558070794059575029078557)
  ·
    refine ⟨42959276547772340635904459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114558070794059575029078557 42959276547772340635904459)
    ·
      refine ⟨64438914821658510953856689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42959276547772340635904459 64438914821658510953856689)
      ·
        refine ⟨48329186116243883215392517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64438914821658510953856689 48329186116243883215392517)
        ·
          refine ⟨9061722396795728102886097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48329186116243883215392517 9061722396795728102886097)
          ·
            refine ⟨6796291797596796077164573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9061722396795728102886097 6796291797596796077164573)
            ·
              refine ⟨2548609424098798528936715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6796291797596796077164573 2548609424098798528936715)
              ·
                refine ⟨3822914136148197793405073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548609424098798528936715 3822914136148197793405073)
                ·
                  refine ⟨2867185602111148345053805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3822914136148197793405073 2867185602111148345053805)
                  ·
                    refine ⟨1075194600791680629395177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2867185602111148345053805 1075194600791680629395177)
                    ·
                      rfl

theorem cell22_3140901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_3140901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140901 prefixEnd_3140901 := by exact prefixLift 3140901
  have htrace : WordTrace (prefixWord ++ tailWord_3140901) baseStart_3140901 baseEnd_3140901 := by
    simpa [prefixWord, tailWord_3140901, baseEnd_3140901] using wordTrace_append hprefix tailTrace_3140901
  have hstable : (prefixWord ++ tailWord_3140901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140901).length < 2 ^ (prefixWord ++ tailWord_3140901).sum := by decide
  have hdescent : baseEnd_3140901 < baseStart_3140901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140912 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_3140912 : Nat := 118140960795 + 3140912 * 2 ^ 59
def prefixEnd_3140912 : Nat := 4983230072969 + 3 ^ 40 * 3140912 * 2
def baseEnd_3140912 : Nat := 1075198366316480267370143

theorem tailTrace_3140912 : CollatzResearch.WordTrace tailWord_3140912 prefixEnd_3140912 1075198366316480267370143 := by
  unfold tailWord_3140912
  simp only [CollatzResearch.WordTrace]
  refine ⟨57279235998509861953864495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76372314664679815938485993 57279235998509861953864495)
  ·
    refine ⟨85918853997764792930796743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57279235998509861953864495 85918853997764792930796743)
    ·
      refine ⟨128878280996647189396195115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85918853997764792930796743 128878280996647189396195115)
      ·
        refine ⟨193317421494970784094292673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128878280996647189396195115 193317421494970784094292673)
        ·
          refine ⟨144988066121228088070719505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193317421494970784094292673 144988066121228088070719505)
          ·
            refine ⟨108741049590921066053039629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144988066121228088070719505 108741049590921066053039629)
            ·
              refine ⟨40777893596595399769889861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108741049590921066053039629 40777893596595399769889861)
              ·
                refine ⟨7645855049361637456854349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40777893596595399769889861 7645855049361637456854349)
                ·
                  refine ⟨2867195643510614046320381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7645855049361637456854349 2867195643510614046320381)
                  ·
                    refine ⟨1075198366316480267370143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2867195643510614046320381 1075198366316480267370143)
                    ·
                      rfl

theorem cell22_3140912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_3140912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140912 prefixEnd_3140912 := by exact prefixLift 3140912
  have htrace : WordTrace (prefixWord ++ tailWord_3140912) baseStart_3140912 baseEnd_3140912 := by
    simpa [prefixWord, tailWord_3140912, baseEnd_3140912] using wordTrace_append hprefix tailTrace_3140912
  have hstable : (prefixWord ++ tailWord_3140912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140912).length < 2 ^ (prefixWord ++ tailWord_3140912).sum := by decide
  have hdescent : baseEnd_3140912 < baseStart_3140912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140914 : List Nat := [3, 2, 1, 1, 4, 3, 2, 6]
def baseStart_3140914 : Nat := 118140960795 + 3140914 * 2 ^ 59
def prefixEnd_3140914 : Nat := 4983230072969 + 3 ^ 40 * 3140914 * 2
def baseEnd_3140914 : Nat := 119466561217483658757793

theorem tailTrace_3140914 : CollatzResearch.WordTrace tailWord_3140914 prefixEnd_3140914 119466561217483658757793 := by
  unfold tailWord_3140914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28639636235753119562325449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76372363295341652166201197 28639636235753119562325449)
  ·
    refine ⟨21479727176814839671744087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28639636235753119562325449 21479727176814839671744087)
    ·
      refine ⟨32219590765222259507616131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21479727176814839671744087 32219590765222259507616131)
      ·
        refine ⟨48329386147833389261424197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32219590765222259507616131 48329386147833389261424197)
        ·
          refine ⟨9061759902718760486517037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48329386147833389261424197 9061759902718760486517037)
          ·
            refine ⟨3398159963519535182443889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9061759902718760486517037 3398159963519535182443889)
            ·
              refine ⟨2548619972639651386832917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398159963519535182443889 2548619972639651386832917)
              ·
                refine ⟨119466561217483658757793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2548619972639651386832917 119466561217483658757793)
                ·
                  rfl

theorem cell22_3140914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_3140914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140914 prefixEnd_3140914 := by exact prefixLift 3140914
  have htrace : WordTrace (prefixWord ++ tailWord_3140914) baseStart_3140914 baseEnd_3140914 := by
    simpa [prefixWord, tailWord_3140914, baseEnd_3140914] using wordTrace_append hprefix tailTrace_3140914
  have hstable : (prefixWord ++ tailWord_3140914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140914).length < 2 ^ (prefixWord ++ tailWord_3140914).sum := by decide
  have hdescent : baseEnd_3140914 < baseStart_3140914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140942 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_3140942 : Nat := 118140960795 + 3140942 * 2 ^ 59
def prefixEnd_3140942 : Nat := 4983230072969 + 3 ^ 40 * 3140942 * 2
def baseEnd_3140942 : Nat := 358402878643190063040017

theorem tailTrace_3140942 : CollatzResearch.WordTrace tailWord_3140942 prefixEnd_3140942 358402878643190063040017 := by
  unfold tailWord_3140942
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319945773363879878915135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76373044124607359354214053 14319945773363879878915135)
  ·
    refine ⟨21479918660045819818372703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14319945773363879878915135 21479918660045819818372703)
    ·
      refine ⟨32219877990068729727559055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21479918660045819818372703 32219877990068729727559055)
      ·
        refine ⟨48329816985103094591338583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32219877990068729727559055 48329816985103094591338583)
        ·
          refine ⟨72494725477654641887007875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48329816985103094591338583 72494725477654641887007875)
          ·
            refine ⟨108742088216481962830511813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72494725477654641887007875 108742088216481962830511813)
            ·
              refine ⟨20389141540590368030720965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108742088216481962830511813 20389141540590368030720965)
              ·
                refine ⟨3822964038860694005760181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20389141540590368030720965 3822964038860694005760181)
                ·
                  refine ⟨358402878643190063040017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3822964038860694005760181 358402878643190063040017)
                  ·
                    rfl

theorem cell22_3140942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_3140942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3140942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3140942 prefixEnd_3140942 := by exact prefixLift 3140942
  have htrace : WordTrace (prefixWord ++ tailWord_3140942) baseStart_3140942 baseEnd_3140942 := by
    simpa [prefixWord, tailWord_3140942, baseEnd_3140942] using wordTrace_append hprefix tailTrace_3140942
  have hstable : (prefixWord ++ tailWord_3140942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140942).length < 2 ^ (prefixWord ++ tailWord_3140942).sum := by decide
  have hdescent : baseEnd_3140942 < baseStart_3140942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141004 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 4]
def baseStart_3141004 : Nat := 118140960795 + 3141004 * 2 ^ 59
def prefixEnd_3141004 : Nat := 4983230072969 + 3 ^ 40 * 3141004 * 2
def baseEnd_3141004 : Nat := 358409953265540898023287

theorem tailTrace_3141004 : CollatzResearch.WordTrace tailWord_3141004 prefixEnd_3141004 358409953265540898023287 := by
  unfold tailWord_3141004
  simp only [CollatzResearch.WordTrace]
  refine ⟨57280913756343211810039033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76374551675124282413385377 57280913756343211810039033)
  ·
    refine ⟨42960685317257408857529275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57280913756343211810039033 42960685317257408857529275)
    ·
      refine ⟨64441027975886113286293913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42960685317257408857529275 64441027975886113286293913)
      ·
        refine ⟨48330770981914584964720435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64441027975886113286293913 48330770981914584964720435)
        ·
          refine ⟨72496156472871877447080653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48330770981914584964720435 72496156472871877447080653)
          ·
            refine ⟨27186058677326954042655245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72496156472871877447080653 27186058677326954042655245)
            ·
              refine ⟨10194772003997607765995717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27186058677326954042655245 10194772003997607765995717)
              ·
                refine ⟨1911519750749551456124197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10194772003997607765995717 1911519750749551456124197)
                ·
                  refine ⟨358409953265540898023287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911519750749551456124197 358409953265540898023287)
                  ·
                    rfl

theorem cell22_3141004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_3141004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141004 prefixEnd_3141004 := by exact prefixLift 3141004
  have htrace : WordTrace (prefixWord ++ tailWord_3141004) baseStart_3141004 baseEnd_3141004 := by
    simpa [prefixWord, tailWord_3141004, baseEnd_3141004] using wordTrace_append hprefix tailTrace_3141004
  have hstable : (prefixWord ++ tailWord_3141004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141004).length < 2 ^ (prefixWord ++ tailWord_3141004).sum := by decide
  have hdescent : baseEnd_3141004 < baseStart_3141004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141092 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3141092 : Nat := 118140960795 + 3141092 * 2 ^ 59
def prefixEnd_3141092 : Nat := 4983230072969 + 3 ^ 40 * 3141092 * 2
def baseEnd_3141092 : Nat := 1075259983995019797869591

theorem tailTrace_3141092 : CollatzResearch.WordTrace tailWord_3141092 prefixEnd_3141092 1075259983995019797869591 := by
  unfold tailWord_3141092
  simp only [CollatzResearch.WordTrace]
  refine ⟨57282518568183807324640765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76376691424245076432854353 57282518568183807324640765)
  ·
    refine ⟨21480944463068927746740287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57282518568183807324640765 21480944463068927746740287)
    ·
      refine ⟨32221416694603391620110431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21480944463068927746740287 32221416694603391620110431)
      ·
        refine ⟨48332125041905087430165647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32221416694603391620110431 48332125041905087430165647)
        ·
          refine ⟨72498187562857631145248471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48332125041905087430165647 72498187562857631145248471)
          ·
            refine ⟨108747281344286446717872707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72498187562857631145248471 108747281344286446717872707)
            ·
              refine ⟨163120922016429670076809061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108747281344286446717872707 163120922016429670076809061)
              ·
                refine ⟨30585172878080563139401699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163120922016429670076809061 30585172878080563139401699)
                ·
                  refine ⟨45877759317120844709102549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30585172878080563139401699 45877759317120844709102549)
                  ·
                    refine ⟨1075259983995019797869591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45877759317120844709102549 1075259983995019797869591)
                    ·
                      rfl

theorem cell22_3141092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3141092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141092 prefixEnd_3141092 := by exact prefixLift 3141092
  have htrace : WordTrace (prefixWord ++ tailWord_3141092) baseStart_3141092 baseEnd_3141092 := by
    simpa [prefixWord, tailWord_3141092, baseEnd_3141092] using wordTrace_append hprefix tailTrace_3141092
  have hstable : (prefixWord ++ tailWord_3141092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141092).length < 2 ^ (prefixWord ++ tailWord_3141092).sum := by decide
  have hdescent : baseEnd_3141092 < baseStart_3141092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141141 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_3141141 : Nat := 118140960795 + 3141141 * 2 ^ 59
def prefixEnd_3141141 : Nat := 4983230072969 + 3 ^ 40 * 3141141 * 2
def baseEnd_3141141 : Nat := 1075276757696400003394441

theorem tailTrace_3141141 : CollatzResearch.WordTrace tailWord_3141141 prefixEnd_3141141 1075276757696400003394441 := by
  unfold tailWord_3141141
  simp only [CollatzResearch.WordTrace]
  refine ⟨114566824313190096017815277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76377882875460064011876851 114566824313190096017815277)
  ·
    refine ⟨42962559117446286006680729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114566824313190096017815277 42962559117446286006680729)
    ·
      refine ⟨32221919338084714505010547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42962559117446286006680729 32221919338084714505010547)
      ·
        refine ⟨48332879007127071757515821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32221919338084714505010547 48332879007127071757515821)
        ·
          refine ⟨18124829627672651909068433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48332879007127071757515821 18124829627672651909068433)
          ·
            refine ⟨13593622220754488931801325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18124829627672651909068433 13593622220754488931801325)
            ·
              refine ⟨5097608332782933349425497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13593622220754488931801325 5097608332782933349425497)
              ·
                refine ⟨3823206249587200012069123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097608332782933349425497 3823206249587200012069123)
                ·
                  refine ⟨5734809374380800018103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823206249587200012069123 5734809374380800018103685)
                  ·
                    refine ⟨1075276757696400003394441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5734809374380800018103685 1075276757696400003394441)
                    ·
                      rfl

theorem cell22_3141141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_3141141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141141 prefixEnd_3141141 := by exact prefixLift 3141141
  have htrace : WordTrace (prefixWord ++ tailWord_3141141) baseStart_3141141 baseEnd_3141141 := by
    simpa [prefixWord, tailWord_3141141, baseEnd_3141141] using wordTrace_append hprefix tailTrace_3141141
  have hstable : (prefixWord ++ tailWord_3141141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141141).length < 2 ^ (prefixWord ++ tailWord_3141141).sum := by decide
  have hdescent : baseEnd_3141141 < baseStart_3141141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141154 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3141154 : Nat := 118140960795 + 3141154 * 2 ^ 59
def prefixEnd_3141154 : Nat := 4983230072969 + 3 ^ 40 * 3141154 * 2
def baseEnd_3141154 : Nat := 1075281207862072302819401

theorem tailTrace_3141154 : CollatzResearch.WordTrace tailWord_3141154 prefixEnd_3141154 1075281207862072302819401 := by
  unfold tailWord_3141154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28641824615535749809509629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76378198974761999492025677 28641824615535749809509629)
  ·
    refine ⟨10740684230825906178566111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28641824615535749809509629 10740684230825906178566111)
    ·
      refine ⟨16111026346238859267849167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740684230825906178566111 16111026346238859267849167)
      ·
        refine ⟨24166539519358288901773751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16111026346238859267849167 24166539519358288901773751)
        ·
          refine ⟨36249809279037433352660627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24166539519358288901773751 36249809279037433352660627)
          ·
            refine ⟨54374713918556150028990941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36249809279037433352660627 54374713918556150028990941)
            ·
              refine ⟨20390517719458556260871603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54374713918556150028990941 20390517719458556260871603)
              ·
                refine ⟨30585776579187834391307405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20390517719458556260871603 30585776579187834391307405)
                ·
                  refine ⟨11469666217195437896740277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30585776579187834391307405 11469666217195437896740277)
                  ·
                    refine ⟨1075281207862072302819401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11469666217195437896740277 1075281207862072302819401)
                    ·
                      rfl

theorem cell22_3141154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3141154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141154 prefixEnd_3141154 := by exact prefixLift 3141154
  have htrace : WordTrace (prefixWord ++ tailWord_3141154) baseStart_3141154 baseEnd_3141154 := by
    simpa [prefixWord, tailWord_3141154, baseEnd_3141154] using wordTrace_append hprefix tailTrace_3141154
  have hstable : (prefixWord ++ tailWord_3141154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141154).length < 2 ^ (prefixWord ++ tailWord_3141154).sum := by decide
  have hdescent : baseEnd_3141154 < baseStart_3141154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141171 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 2, 3]
def baseStart_3141171 : Nat := 118140960795 + 3141171 * 2 ^ 59
def prefixEnd_3141171 : Nat := 4983230072969 + 3 ^ 40 * 3141171 * 2
def baseEnd_3141171 : Nat := 1075287027309489925144349

theorem tailTrace_3141171 : CollatzResearch.WordTrace tailWord_3141171 prefixEnd_3141171 1075287027309489925144349 := by
  unfold tailWord_3141171
  simp only [CollatzResearch.WordTrace]
  refine ⟨114567918503081411141407367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76378612335387607427604911 114567918503081411141407367)
  ·
    refine ⟨171851877754622116712111051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114567918503081411141407367 171851877754622116712111051)
    ·
      refine ⟨257777816631933175068166577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171851877754622116712111051 257777816631933175068166577)
      ·
        refine ⟨193333362473949881301124933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257777816631933175068166577 193333362473949881301124933)
        ·
          refine ⟨36250005463865602743960925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193333362473949881301124933 36250005463865602743960925)
          ·
            refine ⟨13593752048949601028985347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36250005463865602743960925 13593752048949601028985347)
            ·
              refine ⟨20390628073424401543478021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13593752048949601028985347 20390628073424401543478021)
              ·
                refine ⟨3823242763767075289402129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20390628073424401543478021 3823242763767075289402129)
                ·
                  refine ⟨2867432072825306467051597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823242763767075289402129 2867432072825306467051597)
                  ·
                    refine ⟨1075287027309489925144349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2867432072825306467051597 1075287027309489925144349)
                    ·
                      rfl

theorem cell22_3141171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 3].length) (baseStart_3141171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141171 prefixEnd_3141171 := by exact prefixLift 3141171
  have htrace : WordTrace (prefixWord ++ tailWord_3141171) baseStart_3141171 baseEnd_3141171 := by
    simpa [prefixWord, tailWord_3141171, baseEnd_3141171] using wordTrace_append hprefix tailTrace_3141171
  have hstable : (prefixWord ++ tailWord_3141171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141171).length < 2 ^ (prefixWord ++ tailWord_3141171).sum := by decide
  have hdescent : baseEnd_3141171 < baseStart_3141171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141173 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 4]
def baseStart_3141173 : Nat := 118140960795 + 3141173 * 2 ^ 59
def prefixEnd_3141173 : Nat := 4983230072969 + 3 ^ 40 * 3141173 * 2
def baseEnd_3141173 : Nat := 358429237316787528864781

theorem tailTrace_3141173 : CollatzResearch.WordTrace tailWord_3141173 prefixEnd_3141173 358429237316787528864781 := by
  unfold tailWord_3141173
  simp only [CollatzResearch.WordTrace]
  refine ⟨114567991449074165482980173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76378660966049443655320115 114567991449074165482980173)
  ·
    refine ⟨42962996793402812056117565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114567991449074165482980173 42962996793402812056117565)
    ·
      refine ⟨16111123797526054521044087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42962996793402812056117565 16111123797526054521044087)
      ·
        refine ⟨24166685696289081781566131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16111123797526054521044087 24166685696289081781566131)
        ·
          refine ⟨36250028544433622672349197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24166685696289081781566131 36250028544433622672349197)
          ·
            refine ⟨13593760704162608502130949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36250028544433622672349197 13593760704162608502130949)
            ·
              refine ⟨2548830132030489094149553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13593760704162608502130949 2548830132030489094149553)
              ·
                refine ⟨1911622599022866820612165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2548830132030489094149553 1911622599022866820612165)
                ·
                  refine ⟨358429237316787528864781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911622599022866820612165 358429237316787528864781)
                  ·
                    rfl

theorem cell22_3141173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_3141173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141173 prefixEnd_3141173 := by exact prefixLift 3141173
  have htrace : WordTrace (prefixWord ++ tailWord_3141173) baseStart_3141173 baseEnd_3141173 := by
    simpa [prefixWord, tailWord_3141173, baseEnd_3141173] using wordTrace_append hprefix tailTrace_3141173
  have hstable : (prefixWord ++ tailWord_3141173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141173).length < 2 ^ (prefixWord ++ tailWord_3141173).sum := by decide
  have hdescent : baseEnd_3141173 < baseStart_3141173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141304 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_3141304 : Nat := 118140960795 + 3141304 * 2 ^ 59
def prefixEnd_3141304 : Nat := 4983230072969 + 3 ^ 40 * 3141304 * 2
def baseEnd_3141304 : Nat := 1075332555927521911568941

theorem tailTrace_3141304 : CollatzResearch.WordTrace tailWord_3141304 prefixEnd_3141304 1075332555927521911568941 := by
  unfold tailWord_3141304
  simp only [CollatzResearch.WordTrace]
  refine ⟨57286384705799787427999483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76381846274399716570665977 57286384705799787427999483)
  ·
    refine ⟨85929577058699681141999225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57286384705799787427999483 85929577058699681141999225)
    ·
      refine ⟨64447182794024760856499419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85929577058699681141999225 64447182794024760856499419)
      ·
        refine ⟨96670774191037141284749129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64447182794024760856499419 96670774191037141284749129)
        ·
          refine ⟨72503080643277855963561847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96670774191037141284749129 72503080643277855963561847)
          ·
            refine ⟨108754620964916783945342771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72503080643277855963561847 108754620964916783945342771)
            ·
              refine ⟨163131931447375175918014157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108754620964916783945342771 163131931447375175918014157)
              ·
                refine ⟨61174474292765690969255309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163131931447375175918014157 61174474292765690969255309)
                ·
                  refine ⟨22940427859787134113470741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61174474292765690969255309 22940427859787134113470741)
                  ·
                    refine ⟨1075332555927521911568941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22940427859787134113470741 1075332555927521911568941)
                    ·
                      rfl

theorem cell22_3141304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_3141304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141304 prefixEnd_3141304 := by exact prefixLift 3141304
  have htrace : WordTrace (prefixWord ++ tailWord_3141304) baseStart_3141304 baseEnd_3141304 := by
    simpa [prefixWord, tailWord_3141304, baseEnd_3141304] using wordTrace_append hprefix tailTrace_3141304
  have hstable : (prefixWord ++ tailWord_3141304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141304).length < 2 ^ (prefixWord ++ tailWord_3141304).sum := by decide
  have hdescent : baseEnd_3141304 < baseStart_3141304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141310 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_3141310 : Nat := 118140960795 + 3141310 * 2 ^ 59
def prefixEnd_3141310 : Nat := 4983230072969 + 3 ^ 40 * 3141310 * 2
def baseEnd_3141310 : Nat := 1075334609850139895918923

theorem tailTrace_3141310 : CollatzResearch.WordTrace tailWord_3141310 prefixEnd_3141310 1075334609850139895918923 := by
  unfold tailWord_3141310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14321623531197229735089673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76381992166385225253811589 14321623531197229735089673)
  ·
    refine ⟨10741217648397922301317255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14321623531197229735089673 10741217648397922301317255)
    ·
      refine ⟨16111826472596883451975883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10741217648397922301317255 16111826472596883451975883)
      ·
        refine ⟨24167739708895325177963825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16111826472596883451975883 24167739708895325177963825)
        ·
          refine ⟨18125804781671493883472869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24167739708895325177963825 18125804781671493883472869)
          ·
            refine ⟨3398588396563405103151163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18125804781671493883472869 3398588396563405103151163)
            ·
              refine ⟨5097882594845107654726745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398588396563405103151163 5097882594845107654726745)
              ·
                refine ⟨3823411946133830741045059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097882594845107654726745 3823411946133830741045059)
                ·
                  refine ⟨5735117919200746111567589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823411946133830741045059 5735117919200746111567589)
                  ·
                    refine ⟨1075334609850139895918923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5735117919200746111567589 1075334609850139895918923)
                    ·
                      rfl

theorem cell22_3141310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_3141310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141310 prefixEnd_3141310 := by exact prefixLift 3141310
  have htrace : WordTrace (prefixWord ++ tailWord_3141310) baseStart_3141310 baseEnd_3141310 := by
    simpa [prefixWord, tailWord_3141310, baseEnd_3141310] using wordTrace_append hprefix tailTrace_3141310
  have hstable : (prefixWord ++ tailWord_3141310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141310).length < 2 ^ (prefixWord ++ tailWord_3141310).sum := by decide
  have hdescent : baseEnd_3141310 < baseStart_3141310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141319 : List Nat := [1, 1, 4, 1, 1, 1, 3, 10]
def baseStart_3141319 : Nat := 118140960795 + 3141319 * 2 ^ 59
def prefixEnd_3141319 : Nat := 4983230072969 + 3 ^ 40 * 3141319 * 2
def baseEnd_3141319 : Nat := 119481965637118541382655

theorem tailTrace_3141319 : CollatzResearch.WordTrace tailWord_3141319 prefixEnd_3141319 119481965637118541382655 := by
  unfold tailWord_3141319
  simp only [CollatzResearch.WordTrace]
  refine ⟨114573316506545232417795011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76382211004363488278530007 114573316506545232417795011)
  ·
    refine ⟨171859974759817848626692517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114573316506545232417795011 171859974759817848626692517)
    ·
      refine ⟨32223745267465846617504847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171859974759817848626692517 32223745267465846617504847)
      ·
        refine ⟨48335617901198769926257271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32223745267465846617504847 48335617901198769926257271)
        ·
          refine ⟨72503426851798154889385907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48335617901198769926257271 72503426851798154889385907)
          ·
            refine ⟨108755140277697232334078861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72503426851798154889385907 108755140277697232334078861)
            ·
              refine ⟨40783177604136462125279573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108755140277697232334078861 40783177604136462125279573)
              ·
                refine ⟨119481965637118541382655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40783177604136462125279573 119481965637118541382655)
                ·
                  rfl

theorem cell22_3141319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 10].length) (baseStart_3141319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141319 prefixEnd_3141319 := by exact prefixLift 3141319
  have htrace : WordTrace (prefixWord ++ tailWord_3141319) baseStart_3141319 baseEnd_3141319 := by
    simpa [prefixWord, tailWord_3141319, baseEnd_3141319] using wordTrace_append hprefix tailTrace_3141319
  have hstable : (prefixWord ++ tailWord_3141319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141319).length < 2 ^ (prefixWord ++ tailWord_3141319).sum := by decide
  have hdescent : baseEnd_3141319 < baseStart_3141319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141411 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 5, 4]
def baseStart_3141411 : Nat := 118140960795 + 3141411 * 2 ^ 59
def prefixEnd_3141411 : Nat := 4983230072969 + 3 ^ 40 * 3141411 * 2
def baseEnd_3141411 : Nat := 1075369184214209299143613

theorem tailTrace_3141411 : CollatzResearch.WordTrace tailWord_3141411 prefixEnd_3141411 1075369184214209299143613 := by
  unfold tailWord_3141411
  simp only [CollatzResearch.WordTrace]
  refine ⟨114576672022211932130144087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76384448014807954753429391 114576672022211932130144087)
  ·
    refine ⟨171865008033317898195216131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114576672022211932130144087 171865008033317898195216131)
    ·
      refine ⟨257797512049976847292824197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171865008033317898195216131 257797512049976847292824197)
      ·
        refine ⟨48337033509370658867404537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257797512049976847292824197 48337033509370658867404537)
        ·
          refine ⟨36252775132027994150553403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48337033509370658867404537 36252775132027994150553403)
          ·
            refine ⟨54379162698041991225830105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36252775132027994150553403 54379162698041991225830105)
            ·
              refine ⟨40784372023531493419372579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54379162698041991225830105 40784372023531493419372579)
              ·
                refine ⟨61176558035297240129058869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40784372023531493419372579 61176558035297240129058869)
                ·
                  refine ⟨5735302315809116262099269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61176558035297240129058869 5735302315809116262099269)
                  ·
                    refine ⟨1075369184214209299143613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5735302315809116262099269 1075369184214209299143613)
                    ·
                      rfl

theorem cell22_3141411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_3141411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141411 prefixEnd_3141411 := by exact prefixLift 3141411
  have htrace : WordTrace (prefixWord ++ tailWord_3141411) baseStart_3141411 baseEnd_3141411 := by
    simpa [prefixWord, tailWord_3141411, baseEnd_3141411] using wordTrace_append hprefix tailTrace_3141411
  have hstable : (prefixWord ++ tailWord_3141411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141411).length < 2 ^ (prefixWord ++ tailWord_3141411).sum := by decide
  have hdescent : baseEnd_3141411 < baseStart_3141411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141460 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3141460 : Nat := 118140960795 + 3141460 * 2 ^ 59
def prefixEnd_3141460 : Nat := 4983230072969 + 3 ^ 40 * 3141460 * 2
def baseEnd_3141460 : Nat := 358461985971863168222821

theorem tailTrace_3141460 : CollatzResearch.WordTrace tailWord_3141460 prefixEnd_3141460 358461985971863168222821 := by
  unfold tailWord_3141460
  simp only [CollatzResearch.WordTrace]
  refine ⟨57289229599517206749338917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76385639466022942332451889 57289229599517206749338917)
  ·
    refine ⟨10741730549909476265501047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57289229599517206749338917 10741730549909476265501047)
    ·
      refine ⟨16112595824864214398251571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10741730549909476265501047 16112595824864214398251571)
      ·
        refine ⟨24168893737296321597377357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16112595824864214398251571 24168893737296321597377357)
        ·
          refine ⟨9063335151486120599016509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24168893737296321597377357 9063335151486120599016509)
          ·
            refine ⟨3398750681807295224631191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9063335151486120599016509 3398750681807295224631191)
            ·
              refine ⟨5098126022710942836946787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398750681807295224631191 5098126022710942836946787)
              ·
                refine ⟨7647189034066414255420181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098126022710942836946787 7647189034066414255420181)
                ·
                  refine ⟨358461985971863168222821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7647189034066414255420181 358461985971863168222821)
                  ·
                    rfl

theorem cell22_3141460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3141460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141460 prefixEnd_3141460 := by exact prefixLift 3141460
  have htrace : WordTrace (prefixWord ++ tailWord_3141460) baseStart_3141460 baseEnd_3141460 := by
    simpa [prefixWord, tailWord_3141460, baseEnd_3141460] using wordTrace_append hprefix tailTrace_3141460
  have hstable : (prefixWord ++ tailWord_3141460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141460).length < 2 ^ (prefixWord ++ tailWord_3141460).sum := by decide
  have hdescent : baseEnd_3141460 < baseStart_3141460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141471 : List Nat := [1, 1, 2, 3, 1, 4, 1, 9]
def baseStart_3141471 : Nat := 118140960795 + 3141471 * 2 ^ 59
def prefixEnd_3141471 : Nat := 4983230072969 + 3 ^ 40 * 3141471 * 2
def baseEnd_3141471 : Nat := 119487747048932126960381

theorem tailTrace_3141471 : CollatzResearch.WordTrace tailWord_3141471 prefixEnd_3141471 119487747048932126960381 := by
  unfold tailWord_3141471
  simp only [CollatzResearch.WordTrace]
  refine ⟨114578860401994562377328267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76385906934663041584885511 114578860401994562377328267)
  ·
    refine ⟨171868290602991843565992401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114578860401994562377328267 171868290602991843565992401)
    ·
      refine ⟨128901217952243882674494301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171868290602991843565992401 128901217952243882674494301)
      ·
        refine ⟨48337956732091456002935363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128901217952243882674494301 48337956732091456002935363)
        ·
          refine ⟨72506935098137184004403045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48337956732091456002935363 72506935098137184004403045)
          ·
            refine ⟨13595050330900722000825571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72506935098137184004403045 13595050330900722000825571)
            ·
              refine ⟨20392575496351083001238357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13595050330900722000825571 20392575496351083001238357)
              ·
                refine ⟨119487747048932126960381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20392575496351083001238357 119487747048932126960381)
                ·
                  rfl

theorem cell22_3141471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 9].length) (baseStart_3141471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141471 prefixEnd_3141471 := by exact prefixLift 3141471
  have htrace : WordTrace (prefixWord ++ tailWord_3141471) baseStart_3141471 baseEnd_3141471 := by
    simpa [prefixWord, tailWord_3141471, baseEnd_3141471] using wordTrace_append hprefix tailTrace_3141471
  have hstable : (prefixWord ++ tailWord_3141471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141471).length < 2 ^ (prefixWord ++ tailWord_3141471).sum := by decide
  have hdescent : baseEnd_3141471 < baseStart_3141471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141505 : List Nat := [1, 2, 4, 4, 2, 9]
def baseStart_3141505 : Nat := 118140960795 + 3141505 * 2 ^ 59
def prefixEnd_3141505 : Nat := 4983230072969 + 3 ^ 40 * 3141505 * 2
def baseEnd_3141505 : Nat := 13276560028829930707325

theorem tailTrace_3141505 : CollatzResearch.WordTrace tailWord_3141505 prefixEnd_3141505 13276560028829930707325 := by
  unfold tailWord_3141505
  simp only [CollatzResearch.WordTrace]
  refine ⟨114580100483871386184065969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76386733655914257456043979 114580100483871386184065969)
  ·
    refine ⟨85935075362903539638049477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114580100483871386184065969 85935075362903539638049477)
    ·
      refine ⟨16112826630544413682134277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85935075362903539638049477 16112826630544413682134277)
      ·
        refine ⟨3021154993227077565400177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16112826630544413682134277 3021154993227077565400177)
        ·
          refine ⟨2265866244920308174050133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3021154993227077565400177 2265866244920308174050133)
          ·
            refine ⟨13276560028829930707325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2265866244920308174050133 13276560028829930707325)
            ·
              rfl

theorem cell22_3141505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 9].length) (baseStart_3141505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141505 prefixEnd_3141505 := by exact prefixLift 3141505
  have htrace : WordTrace (prefixWord ++ tailWord_3141505) baseStart_3141505 baseEnd_3141505 := by
    simpa [prefixWord, tailWord_3141505, baseEnd_3141505] using wordTrace_append hprefix tailTrace_3141505
  have hstable : (prefixWord ++ tailWord_3141505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141505).length < 2 ^ (prefixWord ++ tailWord_3141505).sum := by decide
  have hdescent : baseEnd_3141505 < baseStart_3141505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141537 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3141537 : Nat := 118140960795 + 3141537 * 2 ^ 59
def prefixEnd_3141537 : Nat := 4983230072969 + 3 ^ 40 * 3141537 * 2
def baseEnd_3141537 : Nat := 1075412316589186970493227

theorem tailTrace_3141537 : CollatzResearch.WordTrace tailWord_3141537 prefixEnd_3141537 1075412316589186970493227 := by
  unfold tailWord_3141537
  simp only [CollatzResearch.WordTrace]
  refine ⟨114581267619755455649230865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76387511746503637099487243 114581267619755455649230865)
  ·
    refine ⟨85935950714816591736923149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114581267619755455649230865 85935950714816591736923149)
    ·
      refine ⟨32225981518056221901346181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85935950714816591736923149 32225981518056221901346181)
      ·
        refine ⟨6042371534635541606502409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32225981518056221901346181 6042371534635541606502409)
        ·
          refine ⟨4531778650976656204876807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6042371534635541606502409 4531778650976656204876807)
          ·
            refine ⟨6797667976464984307315211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531778650976656204876807 6797667976464984307315211)
            ·
              refine ⟨10196501964697476460972817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797667976464984307315211 10196501964697476460972817)
              ·
                refine ⟨7647376473523107345729613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10196501964697476460972817 7647376473523107345729613)
                ·
                  refine ⟨2867766177571165254648605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7647376473523107345729613 2867766177571165254648605)
                  ·
                    refine ⟨1075412316589186970493227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2867766177571165254648605 1075412316589186970493227)
                    ·
                      rfl

theorem cell22_3141537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3141537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141537 prefixEnd_3141537 := by exact prefixLift 3141537
  have htrace : WordTrace (prefixWord ++ tailWord_3141537) baseStart_3141537 baseEnd_3141537 := by
    simpa [prefixWord, tailWord_3141537, baseEnd_3141537] using wordTrace_append hprefix tailTrace_3141537
  have hstable : (prefixWord ++ tailWord_3141537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141537).length < 2 ^ (prefixWord ++ tailWord_3141537).sum := by decide
  have hdescent : baseEnd_3141537 < baseStart_3141537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141578 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_3141578 : Nat := 118140960795 + 3141578 * 2 ^ 59
def prefixEnd_3141578 : Nat := 4983230072969 + 3 ^ 40 * 3141578 * 2
def baseEnd_3141578 : Nat := 358475450575692176739367

theorem tailTrace_3141578 : CollatzResearch.WordTrace tailWord_3141578 prefixEnd_3141578 358475450575692176739367 := by
  unfold tailWord_3141578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28645690753151729912868347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76388508675071279767648925 28645690753151729912868347)
  ·
    refine ⟨42968536129727594869302521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28645690753151729912868347 42968536129727594869302521)
    ·
      refine ⟨32226402097295696151976891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42968536129727594869302521 32226402097295696151976891)
      ·
        refine ⟨48339603145943544227965337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32226402097295696151976891 48339603145943544227965337)
        ·
          refine ⟨36254702359457658170974003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48339603145943544227965337 36254702359457658170974003)
          ·
            refine ⟨54382053539186487256461005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36254702359457658170974003 54382053539186487256461005)
            ·
              refine ⟨20393270077194932721172877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54382053539186487256461005 20393270077194932721172877)
              ·
                refine ⟨7647476278948099770439829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20393270077194932721172877 7647476278948099770439829)
                ·
                  refine ⟨358475450575692176739367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7647476278948099770439829 358475450575692176739367)
                  ·
                    rfl

theorem cell22_3141578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_3141578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141578 prefixEnd_3141578 := by exact prefixLift 3141578
  have htrace : WordTrace (prefixWord ++ tailWord_3141578) baseStart_3141578 baseEnd_3141578 := by
    simpa [prefixWord, tailWord_3141578, baseEnd_3141578] using wordTrace_append hprefix tailTrace_3141578
  have hstable : (prefixWord ++ tailWord_3141578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141578).length < 2 ^ (prefixWord ++ tailWord_3141578).sum := by decide
  have hdescent : baseEnd_3141578 < baseStart_3141578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141610 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_3141610 : Nat := 118140960795 + 3141610 * 2 ^ 59
def prefixEnd_3141610 : Nat := 4983230072969 + 3 ^ 40 * 3141610 * 2
def baseEnd_3141610 : Nat := 1075437305981039113418003

theorem tailTrace_3141610 : CollatzResearch.WordTrace tailWord_3141610 prefixEnd_3141610 1075437305981039113418003 := by
  unfold tailWord_3141610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28645982537122747279159571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76389286765660659411092189 28645982537122747279159571)
  ·
    refine ⟨42968973805684120918739357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28645982537122747279159571 42968973805684120918739357)
    ·
      refine ⟨16113365177131545344527259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42968973805684120918739357 16113365177131545344527259)
      ·
        refine ⟨24170047765697318016790889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16113365177131545344527259 24170047765697318016790889)
        ·
          refine ⟨18127535824272988512593167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24170047765697318016790889 18127535824272988512593167)
          ·
            refine ⟨27191303736409482768889751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18127535824272988512593167 27191303736409482768889751)
            ·
              refine ⟨40786955604614224153334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27191303736409482768889751 40786955604614224153334627)
              ·
                refine ⟨61180433406921336230001941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40786955604614224153334627 61180433406921336230001941)
                ·
                  refine ⟨2867832815949437635781341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61180433406921336230001941 2867832815949437635781341)
                  ·
                    refine ⟨1075437305981039113418003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2867832815949437635781341 1075437305981039113418003)
                    ·
                      rfl

theorem cell22_3141610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_3141610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141610 prefixEnd_3141610 := by exact prefixLift 3141610
  have htrace : WordTrace (prefixWord ++ tailWord_3141610) baseStart_3141610 baseEnd_3141610 := by
    simpa [prefixWord, tailWord_3141610, baseEnd_3141610] using wordTrace_append hprefix tailTrace_3141610
  have hstable : (prefixWord ++ tailWord_3141610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141610).length < 2 ^ (prefixWord ++ tailWord_3141610).sum := by decide
  have hdescent : baseEnd_3141610 < baseStart_3141610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141625 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_3141625 : Nat := 118140960795 + 3141625 * 2 ^ 59
def prefixEnd_3141625 : Nat := 4983230072969 + 3 ^ 40 * 3141625 * 2
def baseEnd_3141625 : Nat := 1075442440787584074292957

theorem tailTrace_3141625 : CollatzResearch.WordTrace tailWord_3141625 prefixEnd_3141625 1075442440787584074292957 := by
  unfold tailWord_3141625
  simp only [CollatzResearch.WordTrace]
  refine ⟨114584477243436646678434329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76389651495624431118956219 114584477243436646678434329)
  ·
    refine ⟨85938357932577485008825747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114584477243436646678434329 85938357932577485008825747)
    ·
      refine ⟨128907536898866227513238621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85938357932577485008825747 128907536898866227513238621)
      ·
        refine ⟨48340326337074835317464483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128907536898866227513238621 48340326337074835317464483)
        ·
          refine ⟨72510489505612252976196725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48340326337074835317464483 72510489505612252976196725)
          ·
            refine ⟨6797858391151148716518443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72510489505612252976196725 6797858391151148716518443)
            ·
              refine ⟨10196787586726723074777665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797858391151148716518443 10196787586726723074777665)
              ·
                refine ⟨7647590690045042306083249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10196787586726723074777665 7647590690045042306083249)
                ·
                  refine ⟨5735693017533781729562437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7647590690045042306083249 5735693017533781729562437)
                  ·
                    refine ⟨1075442440787584074292957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5735693017533781729562437 1075442440787584074292957)
                    ·
                      rfl

theorem cell22_3141625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_3141625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141625 prefixEnd_3141625 := by exact prefixLift 3141625
  have htrace : WordTrace (prefixWord ++ tailWord_3141625) baseStart_3141625 baseEnd_3141625 := by
    simpa [prefixWord, tailWord_3141625, baseEnd_3141625] using wordTrace_append hprefix tailTrace_3141625
  have hstable : (prefixWord ++ tailWord_3141625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141625).length < 2 ^ (prefixWord ++ tailWord_3141625).sum := by decide
  have hdescent : baseEnd_3141625 < baseStart_3141625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141685 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 5]
def baseStart_3141685 : Nat := 118140960795 + 3141685 * 2 ^ 59
def prefixEnd_3141685 : Nat := 4983230072969 + 3 ^ 40 * 3141685 * 2
def baseEnd_3141685 : Nat := 358487660004587972597591

theorem tailTrace_3141685 : CollatzResearch.WordTrace tailWord_3141685 prefixEnd_3141685 358487660004587972597591 := by
  unfold tailWord_3141685
  simp only [CollatzResearch.WordTrace]
  refine ⟨114586665623219276925618509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76391110415479517950412339 114586665623219276925618509)
  ·
    refine ⟨42969999608707228847106941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114586665623219276925618509 42969999608707228847106941)
    ·
      refine ⟨16113749853265210817665103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42969999608707228847106941 16113749853265210817665103)
      ·
        refine ⟨24170624779897816226497655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16113749853265210817665103 24170624779897816226497655)
        ·
          refine ⟨36255937169846724339746483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24170624779897816226497655 36255937169846724339746483)
          ·
            refine ⟨54383905754770086509619725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36255937169846724339746483 54383905754770086509619725)
            ·
              refine ⟨20393964658038782441107397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54383905754770086509619725 20393964658038782441107397)
              ·
                refine ⟨3823868373382271707707637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20393964658038782441107397 3823868373382271707707637)
                ·
                  refine ⟨358487660004587972597591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3823868373382271707707637 358487660004587972597591)
                  ·
                    rfl

theorem cell22_3141685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_3141685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141685 prefixEnd_3141685 := by exact prefixLift 3141685
  have htrace : WordTrace (prefixWord ++ tailWord_3141685) baseStart_3141685 baseEnd_3141685 := by
    simpa [prefixWord, tailWord_3141685, baseEnd_3141685] using wordTrace_append hprefix tailTrace_3141685
  have hstable : (prefixWord ++ tailWord_3141685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141685).length < 2 ^ (prefixWord ++ tailWord_3141685).sum := by decide
  have hdescent : baseEnd_3141685 < baseStart_3141685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141794 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3141794 : Nat := 118140960795 + 3141794 * 2 ^ 59
def prefixEnd_3141794 : Nat := 4983230072969 + 3 ^ 40 * 3141794 * 2
def baseEnd_3141794 : Nat := 1075500292941323966817439

theorem tailTrace_3141794 : CollatzResearch.WordTrace tailWord_3141794 prefixEnd_3141794 1075500292941323966817439 := by
  unfold tailWord_3141794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28647660294956097135334109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76393760786549592360890957 28647660294956097135334109)
  ·
    refine ⟨10742872610608536425750291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28647660294956097135334109 10742872610608536425750291)
    ·
      refine ⟨16114308915912804638625437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742872610608536425750291 16114308915912804638625437)
      ·
        refine ⟨6042865843467301739484539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16114308915912804638625437 6042865843467301739484539)
        ·
          refine ⟨9064298765200952609226809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042865843467301739484539 9064298765200952609226809)
          ·
            refine ⟨6798224073900714456920107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9064298765200952609226809 6798224073900714456920107)
            ·
              refine ⟨10197336110851071685380161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798224073900714456920107 10197336110851071685380161)
              ·
                refine ⟨7648002083138303764035121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197336110851071685380161 7648002083138303764035121)
                ·
                  refine ⟨5736001562353727823026341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648002083138303764035121 5736001562353727823026341)
                  ·
                    refine ⟨1075500292941323966817439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5736001562353727823026341 1075500292941323966817439)
                    ·
                      rfl

theorem cell22_3141794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3141794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141794 prefixEnd_3141794 := by exact prefixLift 3141794
  have htrace : WordTrace (prefixWord ++ tailWord_3141794) baseStart_3141794 baseEnd_3141794 := by
    simpa [prefixWord, tailWord_3141794, baseEnd_3141794] using wordTrace_append hprefix tailTrace_3141794
  have hstable : (prefixWord ++ tailWord_3141794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141794).length < 2 ^ (prefixWord ++ tailWord_3141794).sum := by decide
  have hdescent : baseEnd_3141794 < baseStart_3141794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141869 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3141869 : Nat := 118140960795 + 3141869 * 2 ^ 59
def prefixEnd_3141869 : Nat := 4983230072969 + 3 ^ 40 * 3141869 * 2
def baseEnd_3141869 : Nat := 1075525966974048771192209

theorem tailTrace_3141869 : CollatzResearch.WordTrace tailWord_3141869 prefixEnd_3141869 1075525966974048771192209 := by
  unfold tailWord_3141869
  simp only [CollatzResearch.WordTrace]
  refine ⟨114593376654552676350316661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76395584436368450900211107 114593376654552676350316661)
  ·
    refine ⟨10743129061364313407842187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114593376654552676350316661 10743129061364313407842187)
    ·
      refine ⟨16114693592046470111763281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743129061364313407842187 16114693592046470111763281)
      ·
        refine ⟨12086020194034852583822461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16114693592046470111763281 12086020194034852583822461)
        ·
          refine ⟨4532257572763069718933423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12086020194034852583822461 4532257572763069718933423)
          ·
            refine ⟨6798386359144604578400135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532257572763069718933423 6798386359144604578400135)
            ·
              refine ⟨10197579538716906867600203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798386359144604578400135 10197579538716906867600203)
              ·
                refine ⟨15296369308075360301400305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10197579538716906867600203 15296369308075360301400305)
                ·
                  refine ⟨11472276981056520226050229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15296369308075360301400305 11472276981056520226050229)
                  ·
                    refine ⟨1075525966974048771192209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11472276981056520226050229 1075525966974048771192209)
                    ·
                      rfl

theorem cell22_3141869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3141869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141869 prefixEnd_3141869 := by exact prefixLift 3141869
  have htrace : WordTrace (prefixWord ++ tailWord_3141869) baseStart_3141869 baseEnd_3141869 := by
    simpa [prefixWord, tailWord_3141869, baseEnd_3141869] using wordTrace_append hprefix tailTrace_3141869
  have hstable : (prefixWord ++ tailWord_3141869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141869).length < 2 ^ (prefixWord ++ tailWord_3141869).sum := by decide
  have hdescent : baseEnd_3141869 < baseStart_3141869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141882 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_3141882 : Nat := 118140960795 + 3141882 * 2 ^ 59
def prefixEnd_3141882 : Nat := 4983230072969 + 3 ^ 40 * 3141882 * 2
def baseEnd_3141882 : Nat := 358510139046573690205723

theorem tailTrace_3141882 : CollatzResearch.WordTrace tailWord_3141882 prefixEnd_3141882 358510139046573690205723 := by
  unfold tailWord_3141882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28648462700876394892634975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76395900535670386380359933 28648462700876394892634975)
  ·
    refine ⟨42972694051314592338952463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28648462700876394892634975 42972694051314592338952463)
    ·
      refine ⟨64459041076971888508428695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42972694051314592338952463 64459041076971888508428695)
      ·
        refine ⟨96688561615457832762643043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64459041076971888508428695 96688561615457832762643043)
        ·
          refine ⟨145032842423186749143964565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96688561615457832762643043 145032842423186749143964565)
          ·
            refine ⟨6798414488586878866123339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145032842423186749143964565 6798414488586878866123339)
            ·
              refine ⟨10197621732880318299185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798414488586878866123339 10197621732880318299185009)
              ·
                refine ⟨7648216299660238724388757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197621732880318299185009 7648216299660238724388757)
                ·
                  refine ⟨358510139046573690205723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7648216299660238724388757 358510139046573690205723)
                  ·
                    rfl

theorem cell22_3141882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_3141882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141882 prefixEnd_3141882 := by exact prefixLift 3141882
  have htrace : WordTrace (prefixWord ++ tailWord_3141882) baseStart_3141882 baseEnd_3141882 := by
    simpa [prefixWord, tailWord_3141882, baseEnd_3141882] using wordTrace_append hprefix tailTrace_3141882
  have hstable : (prefixWord ++ tailWord_3141882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141882).length < 2 ^ (prefixWord ++ tailWord_3141882).sum := by decide
  have hdescent : baseEnd_3141882 < baseStart_3141882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141897 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_3141897 : Nat := 118140960795 + 3141897 * 2 ^ 59
def prefixEnd_3141897 : Nat := 4983230072969 + 3 ^ 40 * 3141897 * 2
def baseEnd_3141897 : Nat := 1075535551946266031492123

theorem tailTrace_3141897 : CollatzResearch.WordTrace tailWord_3141897 prefixEnd_3141897 1075535551946266031492123 := by
  unfold tailWord_3141897
  simp only [CollatzResearch.WordTrace]
  refine ⟨114594397898451237132335945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76396265265634158088223963 114594397898451237132335945)
  ·
    refine ⟨85945798423838427849251959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114594397898451237132335945 85945798423838427849251959)
    ·
      refine ⟨128918697635757641773877939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85945798423838427849251959 128918697635757641773877939)
      ·
        refine ⟨193378046453636462660816909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128918697635757641773877939 193378046453636462660816909)
        ·
          refine ⟨72516767420113673497806341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193378046453636462660816909 72516767420113673497806341)
          ·
            refine ⟨13596893891271313780838689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72516767420113673497806341 13596893891271313780838689)
            ·
              refine ⟨10197670418453485335629017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13596893891271313780838689 10197670418453485335629017)
              ·
                refine ⟨7648252813840114001721763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197670418453485335629017 7648252813840114001721763)
                ·
                  refine ⟨11472379220760171002582645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648252813840114001721763 11472379220760171002582645)
                  ·
                    refine ⟨1075535551946266031492123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11472379220760171002582645 1075535551946266031492123)
                    ·
                      rfl

theorem cell22_3141897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_3141897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141897 prefixEnd_3141897 := by exact prefixLift 3141897
  have htrace : WordTrace (prefixWord ++ tailWord_3141897) baseStart_3141897 baseEnd_3141897 := by
    simpa [prefixWord, tailWord_3141897, baseEnd_3141897] using wordTrace_append hprefix tailTrace_3141897
  have hstable : (prefixWord ++ tailWord_3141897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141897).length < 2 ^ (prefixWord ++ tailWord_3141897).sum := by decide
  have hdescent : baseEnd_3141897 < baseStart_3141897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141899 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 4]
def baseStart_3141899 : Nat := 118140960795 + 3141899 * 2 ^ 59
def prefixEnd_3141899 : Nat := 4983230072969 + 3 ^ 40 * 3141899 * 2
def baseEnd_3141899 : Nat := 358512078862379564314039

theorem tailTrace_3141899 : CollatzResearch.WordTrace tailWord_3141899 prefixEnd_3141899 358512078862379564314039 := by
  unfold tailWord_3141899
  simp only [CollatzResearch.WordTrace]
  refine ⟨114594470844443991473908751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76396313896295994315939167 114594470844443991473908751)
  ·
    refine ⟨171891706266665987210863127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114594470844443991473908751 171891706266665987210863127)
    ·
      refine ⟨257837559399998980816294691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171891706266665987210863127 257837559399998980816294691)
      ·
        refine ⟨386756339099998471224442037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257837559399998980816294691 386756339099998471224442037)
        ·
          refine ⟨36258406790624856677291441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386756339099998471224442037 36258406790624856677291441)
          ·
            refine ⟨27193805092968642507968581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36258406790624856677291441 27193805092968642507968581)
            ·
              refine ⟨5098838454931620470244109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27193805092968642507968581 5098838454931620470244109)
              ·
                refine ⟨1912064420599357676341541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5098838454931620470244109 1912064420599357676341541)
                ·
                  refine ⟨358512078862379564314039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912064420599357676341541 358512078862379564314039)
                  ·
                    rfl

theorem cell22_3141899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 4].length) (baseStart_3141899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141899 prefixEnd_3141899 := by exact prefixLift 3141899
  have htrace : WordTrace (prefixWord ++ tailWord_3141899) baseStart_3141899 baseEnd_3141899 := by
    simpa [prefixWord, tailWord_3141899, baseEnd_3141899] using wordTrace_append hprefix tailTrace_3141899
  have hstable : (prefixWord ++ tailWord_3141899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141899).length < 2 ^ (prefixWord ++ tailWord_3141899).sum := by decide
  have hdescent : baseEnd_3141899 < baseStart_3141899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141912 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_3141912 : Nat := 118140960795 + 3141912 * 2 ^ 59
def prefixEnd_3141912 : Nat := 4983230072969 + 3 ^ 40 * 3141912 * 2
def baseEnd_3141912 : Nat := 1075540686752810992367077

theorem tailTrace_3141912 : CollatzResearch.WordTrace tailWord_3141912 prefixEnd_3141912 1075540686752810992367077 := by
  unfold tailWord_3141912
  simp only [CollatzResearch.WordTrace]
  refine ⟨57297472496698447347065995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76396629995597929796087993 57297472496698447347065995)
  ·
    refine ⟨85946208745047671020598993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57297472496698447347065995 85946208745047671020598993)
    ·
      refine ⟨64459656558785753265449245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85946208745047671020598993 64459656558785753265449245)
      ·
        refine ⟨24172371209544657474543467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64459656558785753265449245 24172371209544657474543467)
        ·
          refine ⟨36258556814316986211815201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24172371209544657474543467 36258556814316986211815201)
          ·
            refine ⟨27193917610737739658861401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36258556814316986211815201 27193917610737739658861401)
            ·
              refine ⟨20395438208053304744146051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27193917610737739658861401 20395438208053304744146051)
              ·
                refine ⟨30593157312079957116219077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20395438208053304744146051 30593157312079957116219077)
                ·
                  refine ⟨5736216996014991959291077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30593157312079957116219077 5736216996014991959291077)
                  ·
                    refine ⟨1075540686752810992367077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5736216996014991959291077 1075540686752810992367077)
                    ·
                      rfl

theorem cell22_3141912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_3141912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141912 prefixEnd_3141912 := by exact prefixLift 3141912
  have htrace : WordTrace (prefixWord ++ tailWord_3141912) baseStart_3141912 baseEnd_3141912 := by
    simpa [prefixWord, tailWord_3141912, baseEnd_3141912] using wordTrace_append hprefix tailTrace_3141912
  have hstable : (prefixWord ++ tailWord_3141912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141912).length < 2 ^ (prefixWord ++ tailWord_3141912).sum := by decide
  have hdescent : baseEnd_3141912 < baseStart_3141912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141987 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_3141987 : Nat := 118140960795 + 3141987 * 2 ^ 59
def prefixEnd_3141987 : Nat := 4983230072969 + 3 ^ 40 * 3141987 * 2
def baseEnd_3141987 : Nat := 1075566360785535796741847

theorem tailTrace_3141987 : CollatzResearch.WordTrace tailWord_3141987 prefixEnd_3141987 1075566360785535796741847 := by
  unfold tailWord_3141987
  simp only [CollatzResearch.WordTrace]
  refine ⟨114597680468125182503112215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76398453645416788335408143 114597680468125182503112215)
  ·
    refine ⟨171896520702187773754668323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114597680468125182503112215 171896520702187773754668323)
    ·
      refine ⟨257844781053281660632002485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171896520702187773754668323 257844781053281660632002485)
      ·
        refine ⟨24172948223745155684250233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257844781053281660632002485 24172948223745155684250233)
        ·
          refine ⟨18129711167808866763187675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24172948223745155684250233 18129711167808866763187675)
          ·
            refine ⟨27194566751713300144781513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18129711167808866763187675 27194566751713300144781513)
            ·
              refine ⟨20395925063784975108586135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27194566751713300144781513 20395925063784975108586135)
              ·
                refine ⟨30593887595677462662879203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20395925063784975108586135 30593887595677462662879203)
                ·
                  refine ⟨45890831393516193994318805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30593887595677462662879203 45890831393516193994318805)
                  ·
                    refine ⟨1075566360785535796741847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45890831393516193994318805 1075566360785535796741847)
                    ·
                      rfl

theorem cell22_3141987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_3141987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141987 prefixEnd_3141987 := by exact prefixLift 3141987
  have htrace : WordTrace (prefixWord ++ tailWord_3141987) baseStart_3141987 baseEnd_3141987 := by
    simpa [prefixWord, tailWord_3141987, baseEnd_3141987] using wordTrace_append hprefix tailTrace_3141987
  have hstable : (prefixWord ++ tailWord_3141987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141987).length < 2 ^ (prefixWord ++ tailWord_3141987).sum := by decide
  have hdescent : baseEnd_3141987 < baseStart_3141987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3141989 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 5]
def baseStart_3141989 : Nat := 118140960795 + 3141989 * 2 ^ 59
def prefixEnd_3141989 : Nat := 4983230072969 + 3 ^ 40 * 3141989 * 2
def baseEnd_3141989 : Nat := 358522348475469486063947

theorem tailTrace_3141989 : CollatzResearch.WordTrace tailWord_3141989 prefixEnd_3141989 358522348475469486063947 := by
  unfold tailWord_3141989
  simp only [CollatzResearch.WordTrace]
  refine ⟨114597753414117936844685021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76398502276078624563123347 114597753414117936844685021)
  ·
    refine ⟨42974157530294226316756883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114597753414117936844685021 42974157530294226316756883)
    ·
      refine ⟨64461236295441339475135325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42974157530294226316756883 64461236295441339475135325)
      ·
        refine ⟨24172963610790502303175747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64461236295441339475135325 24172963610790502303175747)
        ·
          refine ⟨36259445416185753454763621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24172963610790502303175747 36259445416185753454763621)
          ·
            refine ⟨6798646015534828772768179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36259445416185753454763621 6798646015534828772768179)
            ·
              refine ⟨10197969023302243159152269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798646015534828772768179 10197969023302243159152269)
              ·
                refine ⟨3824238383738341184682101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10197969023302243159152269 3824238383738341184682101)
                ·
                  refine ⟨358522348475469486063947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3824238383738341184682101 358522348475469486063947)
                  ·
                    rfl

theorem cell22_3141989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_3141989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3141989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3141989 prefixEnd_3141989 := by exact prefixLift 3141989
  have htrace : WordTrace (prefixWord ++ tailWord_3141989) baseStart_3141989 baseEnd_3141989 := by
    simpa [prefixWord, tailWord_3141989, baseEnd_3141989] using wordTrace_append hprefix tailTrace_3141989
  have hstable : (prefixWord ++ tailWord_3141989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3141989).length < 2 ^ (prefixWord ++ tailWord_3141989).sum := by decide
  have hdescent : baseEnd_3141989 < baseStart_3141989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3141989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142100 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3142100 : Nat := 118140960795 + 3142100 * 2 ^ 59
def prefixEnd_3142100 : Nat := 4983230072969 + 3 ^ 40 * 3142100 * 2
def baseEnd_3142100 : Nat := 1075605042994841168666501

theorem tailTrace_3142100 : CollatzResearch.WordTrace tailWord_3142100 prefixEnd_3142100 1075605042994841168666501 := by
  unfold tailWord_3142100
  simp only [CollatzResearch.WordTrace]
  refine ⟨57300900958357901400987877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76401201277810535201317169 57300900958357901400987877)
  ·
    refine ⟨10743918929692106512685227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57300900958357901400987877 10743918929692106512685227)
    ·
      refine ⟨16115878394538159769027841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743918929692106512685227 16115878394538159769027841)
      ·
        refine ⟨12086908795903619826770881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16115878394538159769027841 12086908795903619826770881)
        ·
          refine ⟨9065181596927714870078161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12086908795903619826770881 9065181596927714870078161)
          ·
            refine ⟨6798886197695786152558621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9065181596927714870078161 6798886197695786152558621)
            ·
              refine ⟨2549582324135919807209483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6798886197695786152558621 2549582324135919807209483)
              ·
                refine ⟨3824373486203879710814225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549582324135919807209483 3824373486203879710814225)
                ·
                  refine ⟨2868280114652909783110669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3824373486203879710814225 2868280114652909783110669)
                  ·
                    refine ⟨1075605042994841168666501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868280114652909783110669 1075605042994841168666501)
                    ·
                      rfl

theorem cell22_3142100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3142100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142100 prefixEnd_3142100 := by exact prefixLift 3142100
  have htrace : WordTrace (prefixWord ++ tailWord_3142100) baseStart_3142100 baseEnd_3142100 := by
    simpa [prefixWord, tailWord_3142100, baseEnd_3142100] using wordTrace_append hprefix tailTrace_3142100
  have hstable : (prefixWord ++ tailWord_3142100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142100).length < 2 ^ (prefixWord ++ tailWord_3142100).sum := by decide
  have hdescent : baseEnd_3142100 < baseStart_3142100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142111 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 3, 3]
def baseStart_3142111 : Nat := 118140960795 + 3142111 * 2 ^ 59
def prefixEnd_3142111 : Nat := 4983230072969 + 3 ^ 40 * 3142111 * 2
def baseEnd_3142111 : Nat := 1075608808519640806641467

theorem tailTrace_3142111 : CollatzResearch.WordTrace tailWord_3142111 prefixEnd_3142111 1075608808519640806641467 := by
  unfold tailWord_3142111
  simp only [CollatzResearch.WordTrace]
  refine ⟨114602203119675951680626187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76401468746450634453750791 114602203119675951680626187)
  ·
    refine ⟨171903304679513927520939281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114602203119675951680626187 171903304679513927520939281)
    ·
      refine ⟨128927478509635445640704461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171903304679513927520939281 128927478509635445640704461)
      ·
        refine ⟨48347804441113292115264173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128927478509635445640704461 48347804441113292115264173)
        ·
          refine ⟨18130426665417484543224065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48347804441113292115264173 18130426665417484543224065)
          ·
            refine ⟨13597819999063113407418049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18130426665417484543224065 13597819999063113407418049)
            ·
              refine ⟨10198364999297335055563537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13597819999063113407418049 10198364999297335055563537)
              ·
                refine ⟨7648773749473001291672653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10198364999297335055563537 7648773749473001291672653)
                ·
                  refine ⟨2868290156052375484377245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7648773749473001291672653 2868290156052375484377245)
                  ·
                    refine ⟨1075608808519640806641467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868290156052375484377245 1075608808519640806641467)
                    ·
                      rfl

theorem cell22_3142111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_3142111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142111 prefixEnd_3142111 := by exact prefixLift 3142111
  have htrace : WordTrace (prefixWord ++ tailWord_3142111) baseStart_3142111 baseEnd_3142111 := by
    simpa [prefixWord, tailWord_3142111, baseEnd_3142111] using wordTrace_append hprefix tailTrace_3142111
  have hstable : (prefixWord ++ tailWord_3142111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142111).length < 2 ^ (prefixWord ++ tailWord_3142111).sum := by decide
  have hdescent : baseEnd_3142111 < baseStart_3142111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142158 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_3142158 : Nat := 118140960795 + 3142158 * 2 ^ 59
def prefixEnd_3142158 : Nat := 4983230072969 + 3 ^ 40 * 3142158 * 2
def baseEnd_3142158 : Nat := 358541632526716116905441

theorem tailTrace_3142158 : CollatzResearch.WordTrace tailWord_3142158 prefixEnd_3142158 358541632526716116905441 := by
  unfold tailWord_3142158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325489668813209838448391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76402611567003785805058085 14325489668813209838448391)
  ·
    refine ⟨21488234503219814757672587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14325489668813209838448391 21488234503219814757672587)
    ·
      refine ⟨32232351754829722136508881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21488234503219814757672587 32232351754829722136508881)
      ·
        refine ⟨24174263816122291602381661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32232351754829722136508881 24174263816122291602381661)
        ·
          refine ⟨9065348931045859350893123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24174263816122291602381661 9065348931045859350893123)
          ·
            refine ⟨13598023396568789026339685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9065348931045859350893123 13598023396568789026339685)
            ·
              refine ⟨2549629386856647942438691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13598023396568789026339685 2549629386856647942438691)
              ·
                refine ⟨3824444080284971913658037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549629386856647942438691 3824444080284971913658037)
                ·
                  refine ⟨358541632526716116905441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3824444080284971913658037 358541632526716116905441)
                  ·
                    rfl

theorem cell22_3142158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_3142158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142158 prefixEnd_3142158 := by exact prefixLift 3142158
  have htrace : WordTrace (prefixWord ++ tailWord_3142158) baseStart_3142158 baseEnd_3142158 := by
    simpa [prefixWord, tailWord_3142158, baseEnd_3142158] using wordTrace_append hprefix tailTrace_3142158
  have hstable : (prefixWord ++ tailWord_3142158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142158).length < 2 ^ (prefixWord ++ tailWord_3142158).sum := by decide
  have hdescent : baseEnd_3142158 < baseStart_3142158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142196 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3142196 : Nat := 118140960795 + 3142196 * 2 ^ 59
def prefixEnd_3142196 : Nat := 4983230072969 + 3 ^ 40 * 3142196 * 2
def baseEnd_3142196 : Nat := 1075637905756728918266207

theorem tailTrace_3142196 : CollatzResearch.WordTrace tailWord_3142196 prefixEnd_3142196 1075637905756728918266207 := by
  unfold tailWord_3142196
  simp only [CollatzResearch.WordTrace]
  refine ⟨57302651662184005598735221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76403535549578674131646961 57302651662184005598735221)
  ·
    refine ⟨5372123593329750524881427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57302651662184005598735221 5372123593329750524881427)
    ·
      refine ⟨8058185389994625787322141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372123593329750524881427 8058185389994625787322141)
      ·
        refine ⟨3021819521247984670245803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8058185389994625787322141 3021819521247984670245803)
        ·
          refine ⟨4532729281871977005368705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021819521247984670245803 4532729281871977005368705)
          ·
            refine ⟨3399546961403982754026529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4532729281871977005368705 3399546961403982754026529)
            ·
              refine ⟨2549660221052987065519897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399546961403982754026529 2549660221052987065519897)
              ·
                refine ⟨1912245165789740299139923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549660221052987065519897 1912245165789740299139923)
                ·
                  refine ⟨2868367748684610448709885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912245165789740299139923 2868367748684610448709885)
                  ·
                    refine ⟨1075637905756728918266207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868367748684610448709885 1075637905756728918266207)
                    ·
                      rfl

theorem cell22_3142196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3142196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142196 prefixEnd_3142196 := by exact prefixLift 3142196
  have htrace : WordTrace (prefixWord ++ tailWord_3142196) baseStart_3142196 baseEnd_3142196 := by
    simpa [prefixWord, tailWord_3142196, baseEnd_3142196] using wordTrace_append hprefix tailTrace_3142196
  have hstable : (prefixWord ++ tailWord_3142196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142196).length < 2 ^ (prefixWord ++ tailWord_3142196).sum := by decide
  have hdescent : baseEnd_3142196 < baseStart_3142196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142218 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_3142218 : Nat := 118140960795 + 3142218 * 2 ^ 59
def prefixEnd_3142218 : Nat := 4983230072969 + 3 ^ 40 * 3142218 * 2
def baseEnd_3142218 : Nat := 1075645436806328194216139

theorem tailTrace_3142218 : CollatzResearch.WordTrace tailWord_3142218 prefixEnd_3142218 1075645436806328194216139 := by
  unfold tailWord_3142218
  simp only [CollatzResearch.WordTrace]
  refine ⟨28651526432572077238692827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76404070486858872636514205 28651526432572077238692827)
  ·
    refine ⟨42977289648858115858039241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28651526432572077238692827 42977289648858115858039241)
    ·
      refine ⟨32232967236643586893529431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42977289648858115858039241 32232967236643586893529431)
      ·
        refine ⟨48349450854965380340294147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32232967236643586893529431 48349450854965380340294147)
        ·
          refine ⟨72524176282448070510441221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48349450854965380340294147 72524176282448070510441221)
          ·
            refine ⟨13598283052959013220707729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72524176282448070510441221 13598283052959013220707729)
            ·
              refine ⟨10198712289719259915530797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13598283052959013220707729 10198712289719259915530797)
              ·
                refine ⟨3824517108644722468324049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10198712289719259915530797 3824517108644722468324049)
                ·
                  refine ⟨2868387831483541851243037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3824517108644722468324049 2868387831483541851243037)
                  ·
                    refine ⟨1075645436806328194216139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868387831483541851243037 1075645436806328194216139)
                    ·
                      rfl

theorem cell22_3142218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_3142218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142218 prefixEnd_3142218 := by exact prefixLift 3142218
  have htrace : WordTrace (prefixWord ++ tailWord_3142218) baseStart_3142218 baseEnd_3142218 := by
    simpa [prefixWord, tailWord_3142218, baseEnd_3142218] using wordTrace_append hprefix tailTrace_3142218
  have hstable : (prefixWord ++ tailWord_3142218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142218).length < 2 ^ (prefixWord ++ tailWord_3142218).sum := by decide
  have hdescent : baseEnd_3142218 < baseStart_3142218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142231 : List Nat := [1, 1, 3, 2, 2, 2, 5, 6]
def baseStart_3142231 : Nat := 118140960795 + 3142231 * 2 ^ 59
def prefixEnd_3142231 : Nat := 4983230072969 + 3 ^ 40 * 3142231 * 2
def baseEnd_3142231 : Nat := 119516654108000054849011

theorem tailTrace_3142231 : CollatzResearch.WordTrace tailWord_3142231 prefixEnd_3142231 119516654108000054849011 := by
  unfold tailWord_3142231
  simp only [CollatzResearch.WordTrace]
  refine ⟨114606579879241212174994547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76404386586160808116663031 114606579879241212174994547)
  ·
    refine ⟨171909869818861818262491821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114606579879241212174994547 171909869818861818262491821)
    ·
      refine ⟨64466201182073181848434433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171909869818861818262491821 64466201182073181848434433)
      ·
        refine ⟨48349650886554886386325825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64466201182073181848434433 48349650886554886386325825)
        ·
          refine ⟨36262238164916164789744369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48349650886554886386325825 36262238164916164789744369)
          ·
            refine ⟨27196678623687123592308277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36262238164916164789744369 27196678623687123592308277)
            ·
              refine ⟨2549688620970667836778901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27196678623687123592308277 2549688620970667836778901)
              ·
                refine ⟨119516654108000054849011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2549688620970667836778901 119516654108000054849011)
                ·
                  rfl

theorem cell22_3142231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 6].length) (baseStart_3142231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142231 prefixEnd_3142231 := by exact prefixLift 3142231
  have htrace : WordTrace (prefixWord ++ tailWord_3142231) baseStart_3142231 baseEnd_3142231 := by
    simpa [prefixWord, tailWord_3142231, baseEnd_3142231] using wordTrace_append hprefix tailTrace_3142231
  have hstable : (prefixWord ++ tailWord_3142231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142231).length < 2 ^ (prefixWord ++ tailWord_3142231).sum := by decide
  have hdescent : baseEnd_3142231 < baseStart_3142231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142314 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3142314 : Nat := 118140960795 + 3142314 * 2 ^ 59
def prefixEnd_3142314 : Nat := 4983230072969 + 3 ^ 40 * 3142314 * 2
def baseEnd_3142314 : Nat := 1075678299568215943815845

theorem tailTrace_3142314 : CollatzResearch.WordTrace tailWord_3142314 prefixEnd_3142314 1075678299568215943815845 := by
  unfold tailWord_3142314
  simp only [CollatzResearch.WordTrace]
  refine ⟨28652401784485129337566499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76406404758627011566843997 28652401784485129337566499)
  ·
    refine ⟨42978602676727694006349749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28652401784485129337566499 42978602676727694006349749)
    ·
      refine ⟨4029244000943221313095289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42978602676727694006349749 4029244000943221313095289)
      ·
        refine ⟨3021933000707415984821467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029244000943221313095289 3021933000707415984821467)
        ·
          refine ⟨4532899501061123977232201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021933000707415984821467 4532899501061123977232201)
          ·
            refine ⟨3399674625795842982924151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4532899501061123977232201 3399674625795842982924151)
            ·
              refine ⟨5099511938693764474386227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399674625795842982924151 5099511938693764474386227)
              ·
                refine ⟨7649267908040646711579341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099511938693764474386227 7649267908040646711579341)
                ·
                  refine ⟨2868475465515242516842253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7649267908040646711579341 2868475465515242516842253)
                  ·
                    refine ⟨1075678299568215943815845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868475465515242516842253 1075678299568215943815845)
                    ·
                      rfl

theorem cell22_3142314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3142314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142314 prefixEnd_3142314 := by exact prefixLift 3142314
  have htrace : WordTrace (prefixWord ++ tailWord_3142314) baseStart_3142314 baseEnd_3142314 := by
    simpa [prefixWord, tailWord_3142314, baseEnd_3142314] using wordTrace_append hprefix tailTrace_3142314
  have hstable : (prefixWord ++ tailWord_3142314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142314).length < 2 ^ (prefixWord ++ tailWord_3142314).sum := by decide
  have hdescent : baseEnd_3142314 < baseStart_3142314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142327 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 5]
def baseStart_3142327 : Nat := 118140960795 + 3142327 * 2 ^ 59
def prefixEnd_3142327 : Nat := 4983230072969 + 3 ^ 40 * 3142327 * 2
def baseEnd_3142327 : Nat := 358560916577962747746935

theorem tailTrace_3142327 : CollatzResearch.WordTrace tailWord_3142327 prefixEnd_3142327 358560916577962747746935 := by
  unfold tailWord_3142327
  simp only [CollatzResearch.WordTrace]
  refine ⟨114610081286893420570489235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76406720857928947046992823 114610081286893420570489235)
  ·
    refine ⟨171915121930340130855733853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114610081286893420570489235 171915121930340130855733853)
    ·
      refine ⟨64468170723877549070900195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171915121930340130855733853 64468170723877549070900195)
      ·
        refine ⟨96702256085816323606350293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64468170723877549070900195 96702256085816323606350293)
        ·
          refine ⟨2266459127011320084523835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 96702256085816323606350293 2266459127011320084523835)
          ·
            refine ⟨3399688690516980126785753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266459127011320084523835 3399688690516980126785753)
            ·
              refine ⟨2549766517887735095089315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399688690516980126785753 2549766517887735095089315)
              ·
                refine ⟨3824649776831602642633973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549766517887735095089315 3824649776831602642633973)
                ·
                  refine ⟨358560916577962747746935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3824649776831602642633973 358560916577962747746935)
                  ·
                    rfl

theorem cell22_3142327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 5].length) (baseStart_3142327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142327 prefixEnd_3142327 := by exact prefixLift 3142327
  have htrace : WordTrace (prefixWord ++ tailWord_3142327) baseStart_3142327 baseEnd_3142327 := by
    simpa [prefixWord, tailWord_3142327, baseEnd_3142327] using wordTrace_append hprefix tailTrace_3142327
  have hstable : (prefixWord ++ tailWord_3142327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142327).length < 2 ^ (prefixWord ++ tailWord_3142327).sum := by decide
  have hdescent : baseEnd_3142327 < baseStart_3142327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142340 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3142340 : Nat := 118140960795 + 3142340 * 2 ^ 59
def prefixEnd_3142340 : Nat := 4983230072969 + 3 ^ 40 * 3142340 * 2
def baseEnd_3142340 : Nat := 1075687199899560542665765

theorem tailTrace_3142340 : CollatzResearch.WordTrace tailWord_3142340 prefixEnd_3142340 1075687199899560542665765 := by
  unfold tailWord_3142340
  simp only [CollatzResearch.WordTrace]
  refine ⟨57305277717923161895356237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76407036957230882527141649 57305277717923161895356237)
  ·
    refine ⟨21489479144221185710758589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57305277717923161895356237 21489479144221185710758589)
    ·
      refine ⟨8058554679082944641534471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21489479144221185710758589 8058554679082944641534471)
      ·
        refine ⟨12087832018624416962301707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8058554679082944641534471 12087832018624416962301707)
        ·
          refine ⟨18131748027936625443452561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12087832018624416962301707 18131748027936625443452561)
          ·
            refine ⟨13598811020952469082589421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18131748027936625443452561 13598811020952469082589421)
            ·
              refine ⟨5099554132857175905971033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13598811020952469082589421 5099554132857175905971033)
              ·
                refine ⟨3824665599642881929478275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5099554132857175905971033 3824665599642881929478275)
                ·
                  refine ⟨5736998399464322894217413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824665599642881929478275 5736998399464322894217413)
                  ·
                    refine ⟨1075687199899560542665765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5736998399464322894217413 1075687199899560542665765)
                    ·
                      rfl

theorem cell22_3142340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3142340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142340 prefixEnd_3142340 := by exact prefixLift 3142340
  have htrace : WordTrace (prefixWord ++ tailWord_3142340) baseStart_3142340 baseEnd_3142340 := by
    simpa [prefixWord, tailWord_3142340, baseEnd_3142340] using wordTrace_append hprefix tailTrace_3142340
  have hstable : (prefixWord ++ tailWord_3142340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142340).length < 2 ^ (prefixWord ++ tailWord_3142340).sum := by decide
  have hdescent : baseEnd_3142340 < baseStart_3142340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142372 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3142372 : Nat := 118140960795 + 3142372 * 2 ^ 59
def prefixEnd_3142372 : Nat := 4983230072969 + 3 ^ 40 * 3142372 * 2
def baseEnd_3142372 : Nat := 358566051384507708621889

theorem tailTrace_3142372 : CollatzResearch.WordTrace tailWord_3142372 prefixEnd_3142372 358566051384507708621889 := by
  unfold tailWord_3142372
  simp only [CollatzResearch.WordTrace]
  refine ⟨57305861285865196627938685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76407815047820262170584913 57305861285865196627938685)
  ·
    refine ⟨21489697982199448735477007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57305861285865196627938685 21489697982199448735477007)
    ·
      refine ⟨32234546973299173103215511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21489697982199448735477007 32234546973299173103215511)
      ·
        refine ⟨48351820459948759654823267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32234546973299173103215511 48351820459948759654823267)
        ·
          refine ⟨72527730689923139482234901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48351820459948759654823267 72527730689923139482234901)
          ·
            refine ⟨3399737376090147163229761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72527730689923139482234901 3399737376090147163229761)
            ·
              refine ⟨2549803032067610372422321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399737376090147163229761 2549803032067610372422321)
              ·
                refine ⟨1912352274050707779316741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549803032067610372422321 1912352274050707779316741)
                ·
                  refine ⟨358566051384507708621889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912352274050707779316741 358566051384507708621889)
                  ·
                    rfl

theorem cell22_3142372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3142372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142372 prefixEnd_3142372 := by exact prefixLift 3142372
  have htrace : WordTrace (prefixWord ++ tailWord_3142372) baseStart_3142372 baseEnd_3142372 := by
    simpa [prefixWord, tailWord_3142372, baseEnd_3142372] using wordTrace_append hprefix tailTrace_3142372
  have hstable : (prefixWord ++ tailWord_3142372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142372).length < 2 ^ (prefixWord ++ tailWord_3142372).sum := by decide
  have hdescent : baseEnd_3142372 < baseStart_3142372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142383 : List Nat := [1, 1, 2, 1, 5, 4, 1, 7]
def baseStart_3142383 : Nat := 118140960795 + 3142383 * 2 ^ 59
def prefixEnd_3142383 : Nat := 4983230072969 + 3 ^ 40 * 3142383 * 2
def baseEnd_3142383 : Nat := 119522435519813640426737

theorem tailTrace_3142383 : CollatzResearch.WordTrace tailWord_3142383 prefixEnd_3142383 119522435519813640426737 := by
  unfold tailWord_3142383
  simp only [CollatzResearch.WordTrace]
  refine ⟨114612123774690542134527803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76408082516460361423018535 114612123774690542134527803)
  ·
    refine ⟨171918185662035813201791705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114612123774690542134527803 171918185662035813201791705)
    ·
      refine ⟨128938639246526859901343779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171918185662035813201791705 128938639246526859901343779)
      ·
        refine ⟨193407958869790289852015669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128938639246526859901343779 193407958869790289852015669)
        ·
          refine ⟨18131996144042839673626469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193407958869790289852015669 18131996144042839673626469)
          ·
            refine ⟨3399749277008032438804963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18131996144042839673626469 3399749277008032438804963)
            ·
              refine ⟨5099623915512048658207445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399749277008032438804963 5099623915512048658207445)
              ·
                refine ⟨119522435519813640426737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5099623915512048658207445 119522435519813640426737)
                ·
                  rfl

theorem cell22_3142383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 7].length) (baseStart_3142383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142383 prefixEnd_3142383 := by exact prefixLift 3142383
  have htrace : WordTrace (prefixWord ++ tailWord_3142383) baseStart_3142383 baseEnd_3142383 := by
    simpa [prefixWord, tailWord_3142383, baseEnd_3142383] using wordTrace_append hprefix tailTrace_3142383
  have hstable : (prefixWord ++ tailWord_3142383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142383).length < 2 ^ (prefixWord ++ tailWord_3142383).sum := by decide
  have hdescent : baseEnd_3142383 < baseStart_3142383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142402 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3142402 : Nat := 118140960795 + 3142402 * 2 ^ 59
def prefixEnd_3142402 : Nat := 4983230072969 + 3 ^ 40 * 3142402 * 2
def baseEnd_3142402 : Nat := 1075708423766613047615575

theorem tailTrace_3142402 : CollatzResearch.WordTrace tailWord_3142402 prefixEnd_3142402 1075708423766613047615575 := by
  unfold tailWord_3142402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28653204190405427094867365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76408544507747805586312973 28653204190405427094867365)
  ·
    refine ⟨5372475785701017580287631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28653204190405427094867365 5372475785701017580287631)
    ·
      refine ⟨8058713678551526370431447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372475785701017580287631 8058713678551526370431447)
      ·
        refine ⟨12088070517827289555647171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8058713678551526370431447 12088070517827289555647171)
        ·
          refine ⟨18132105776740934333470757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088070517827289555647171 18132105776740934333470757)
          ·
            refine ⟨3399769833138925187525767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18132105776740934333470757 3399769833138925187525767)
            ·
              refine ⟨5099654749708387781288651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399769833138925187525767 5099654749708387781288651)
              ·
                refine ⟨7649482124562581671932977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099654749708387781288651 7649482124562581671932977)
                ·
                  refine ⟨5737111593421936253949733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7649482124562581671932977 5737111593421936253949733)
                  ·
                    refine ⟨1075708423766613047615575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737111593421936253949733 1075708423766613047615575)
                    ·
                      rfl

theorem cell22_3142402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3142402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142402 prefixEnd_3142402 := by exact prefixLift 3142402
  have htrace : WordTrace (prefixWord ++ tailWord_3142402) baseStart_3142402 baseEnd_3142402 := by
    simpa [prefixWord, tailWord_3142402, baseEnd_3142402] using wordTrace_append hprefix tailTrace_3142402
  have hstable : (prefixWord ++ tailWord_3142402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142402).length < 2 ^ (prefixWord ++ tailWord_3142402).sum := by decide
  have hdescent : baseEnd_3142402 < baseStart_3142402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142411 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 7]
def baseStart_3142411 : Nat := 118140960795 + 3142411 * 2 ^ 59
def prefixEnd_3142411 : Nat := 4983230072969 + 3 ^ 40 * 3142411 * 2
def baseEnd_3142411 : Nat := 358570501550180008046849

theorem tailTrace_3142411 : CollatzResearch.WordTrace tailWord_3142411 prefixEnd_3142411 358570501550180008046849 := by
  unfold tailWord_3142411
  simp only [CollatzResearch.WordTrace]
  refine ⟨114613145018589102916547087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76408763345726068611031391 114613145018589102916547087)
  ·
    refine ⟨171919717527883654374820631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114613145018589102916547087 171919717527883654374820631)
    ·
      refine ⟨257879576291825481562230947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171919717527883654374820631 257879576291825481562230947)
      ·
        refine ⟨386819364437738222343346421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257879576291825481562230947 386819364437738222343346421)
        ·
          refine ⟨36264315416037958344688727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386819364437738222343346421 36264315416037958344688727)
          ·
            refine ⟨54396473124056937517033091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36264315416037958344688727 54396473124056937517033091)
            ·
              refine ⟨81594709686085406275549637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54396473124056937517033091 81594709686085406275549637)
              ·
                refine ⟨15299008066141013676665557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81594709686085406275549637 15299008066141013676665557)
                ·
                  refine ⟨358570501550180008046849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15299008066141013676665557 358570501550180008046849)
                  ·
                    rfl

theorem cell22_3142411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_3142411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142411 prefixEnd_3142411 := by exact prefixLift 3142411
  have htrace : WordTrace (prefixWord ++ tailWord_3142411) baseStart_3142411 baseEnd_3142411 := by
    simpa [prefixWord, tailWord_3142411, baseEnd_3142411] using wordTrace_append hprefix tailTrace_3142411
  have hstable : (prefixWord ++ tailWord_3142411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142411).length < 2 ^ (prefixWord ++ tailWord_3142411).sum := by decide
  have hdescent : baseEnd_3142411 < baseStart_3142411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142428 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_3142428 : Nat := 118140960795 + 3142428 * 2 ^ 59
def prefixEnd_3142428 : Nat := 4983230072969 + 3 ^ 40 * 3142428 * 2
def baseEnd_3142428 : Nat := 358572441365985882155165

theorem tailTrace_3142428 : CollatzResearch.WordTrace tailWord_3142428 prefixEnd_3142428 358572441365985882155165 := by
  unfold tailWord_3142428
  simp only [CollatzResearch.WordTrace]
  refine ⟨57306882529763757409957969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76409176706351676546610625 57306882529763757409957969)
  ·
    refine ⟨42980161897322818057468477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57306882529763757409957969 42980161897322818057468477)
    ·
      refine ⟨16117560711496056771550679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42980161897322818057468477 16117560711496056771550679)
      ·
        refine ⟨24176341067244085157326019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16117560711496056771550679 24176341067244085157326019)
        ·
          refine ⟨36264511600866127735989029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24176341067244085157326019 36264511600866127735989029)
          ·
            refine ⟨6799595925162398950497943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36264511600866127735989029 6799595925162398950497943)
            ·
              refine ⟨10199393887743598425746915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799595925162398950497943 10199393887743598425746915)
              ·
                refine ⟨15299090831615397638620373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10199393887743598425746915 15299090831615397638620373)
                ·
                  refine ⟨358572441365985882155165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15299090831615397638620373 358572441365985882155165)
                  ·
                    rfl

theorem cell22_3142428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_3142428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142428 prefixEnd_3142428 := by exact prefixLift 3142428
  have htrace : WordTrace (prefixWord ++ tailWord_3142428) baseStart_3142428 baseEnd_3142428 := by
    simpa [prefixWord, tailWord_3142428, baseEnd_3142428] using wordTrace_append hprefix tailTrace_3142428
  have hstable : (prefixWord ++ tailWord_3142428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142428).length < 2 ^ (prefixWord ++ tailWord_3142428).sum := by decide
  have hdescent : baseEnd_3142428 < baseStart_3142428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142432 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 1, 3]
def baseStart_3142432 : Nat := 118140960795 + 3142432 * 2 ^ 59
def prefixEnd_3142432 : Nat := 4983230072969 + 3 ^ 40 * 3142432 * 2
def baseEnd_3142432 : Nat := 1075718693379702969365483

theorem tailTrace_3142432 : CollatzResearch.WordTrace tailWord_3142432 prefixEnd_3142432 1075718693379702969365483 := by
  unfold tailWord_3142432
  simp only [CollatzResearch.WordTrace]
  refine ⟨57306955475756511751530775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76409273967675349002041033 57306955475756511751530775)
  ·
    refine ⟨85960433213634767627296163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57306955475756511751530775 85960433213634767627296163)
    ·
      refine ⟨128940649820452151440944245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85960433213634767627296163 128940649820452151440944245)
      ·
        refine ⟨12088185920667389197588523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128940649820452151440944245 12088185920667389197588523)
        ·
          refine ⟨18132278881001083796382785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088185920667389197588523 18132278881001083796382785)
          ·
            refine ⟨13599209160750812847287089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18132278881001083796382785 13599209160750812847287089)
            ·
              refine ⟨10199406870563109635465317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13599209160750812847287089 10199406870563109635465317)
              ·
                refine ⟨1912388788230583056649747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10199406870563109635465317 1912388788230583056649747)
                ·
                  refine ⟨2868583182345874584974621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912388788230583056649747 2868583182345874584974621)
                  ·
                    refine ⟨1075718693379702969365483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868583182345874584974621 1075718693379702969365483)
                    ·
                      rfl

theorem cell22_3142432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_3142432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142432 prefixEnd_3142432 := by exact prefixLift 3142432
  have htrace : WordTrace (prefixWord ++ tailWord_3142432) baseStart_3142432 baseEnd_3142432 := by
    simpa [prefixWord, tailWord_3142432, baseEnd_3142432] using wordTrace_append hprefix tailTrace_3142432
  have hstable : (prefixWord ++ tailWord_3142432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142432).length < 2 ^ (prefixWord ++ tailWord_3142432).sum := by decide
  have hdescent : baseEnd_3142432 < baseStart_3142432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142490 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_3142490 : Nat := 118140960795 + 3142490 * 2 ^ 59
def prefixEnd_3142490 : Nat := 4983230072969 + 3 ^ 40 * 3142490 * 2
def baseEnd_3142490 : Nat := 358579515988336717138435

theorem tailTrace_3142490 : CollatzResearch.WordTrace tailWord_3142490 prefixEnd_3142490 358579515988336717138435 := by
  unfold tailWord_3142490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654006596325724852168231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76410684256868599605781949 28654006596325724852168231)
  ·
    refine ⟨42981009894488587278252347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28654006596325724852168231 42981009894488587278252347)
    ·
      refine ⟨64471514841732880917378521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42981009894488587278252347 64471514841732880917378521)
      ·
        refine ⟨48353636131299660688033891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64471514841732880917378521 48353636131299660688033891)
        ·
          refine ⟨72530454196949491032050837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48353636131299660688033891 72530454196949491032050837)
          ·
            refine ⟨3399865040482007392127383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72530454196949491032050837 3399865040482007392127383)
            ·
              refine ⟨5099797560723011088191075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399865040482007392127383 5099797560723011088191075)
              ·
                refine ⟨7649696341084516632286613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099797560723011088191075 7649696341084516632286613)
                ·
                  refine ⟨358579515988336717138435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7649696341084516632286613 358579515988336717138435)
                  ·
                    rfl

theorem cell22_3142490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_3142490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142490 prefixEnd_3142490 := by exact prefixLift 3142490
  have htrace : WordTrace (prefixWord ++ tailWord_3142490) baseStart_3142490 baseEnd_3142490 := by
    simpa [prefixWord, tailWord_3142490, baseEnd_3142490] using wordTrace_append hprefix tailTrace_3142490
  have hstable : (prefixWord ++ tailWord_3142490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142490).length < 2 ^ (prefixWord ++ tailWord_3142490).sum := by decide
  have hdescent : baseEnd_3142490 < baseStart_3142490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142526 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3142526 : Nat := 118140960795 + 3142526 * 2 ^ 59
def prefixEnd_3142526 : Nat := 4983230072969 + 3 ^ 40 * 3142526 * 2
def baseEnd_3142526 : Nat := 1075750871500718057515195

theorem tailTrace_3142526 : CollatzResearch.WordTrace tailWord_3142526 prefixEnd_3142526 1075750871500718057515195 := by
  unfold tailWord_3142526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14327167426646559694622929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76411559608781651704655621 14327167426646559694622929)
  ·
    refine ⟨10745375569984919770967197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14327167426646559694622929 10745375569984919770967197)
    ·
      refine ⟨4029515838744344914112699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10745375569984919770967197 4029515838744344914112699)
      ·
        refine ⟨6044273758116517371169049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029515838744344914112699 6044273758116517371169049)
        ·
          refine ⟨4533205318587388028376787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6044273758116517371169049 4533205318587388028376787)
          ·
            refine ⟨6799807977881082042565181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533205318587388028376787 6799807977881082042565181)
            ·
              refine ⟨2549927991705405765961943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6799807977881082042565181 2549927991705405765961943)
              ·
                refine ⟨3824891987558108648942915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549927991705405765961943 3824891987558108648942915)
                ·
                  refine ⟨5737337981337162973414373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824891987558108648942915 5737337981337162973414373)
                  ·
                    refine ⟨1075750871500718057515195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737337981337162973414373 1075750871500718057515195)
                    ·
                      rfl

theorem cell22_3142526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3142526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142526 prefixEnd_3142526 := by exact prefixLift 3142526
  have htrace : WordTrace (prefixWord ++ tailWord_3142526) baseStart_3142526 baseEnd_3142526 := by
    simpa [prefixWord, tailWord_3142526, baseEnd_3142526] using wordTrace_append hprefix tailTrace_3142526
  have hstable : (prefixWord ++ tailWord_3142526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142526).length < 2 ^ (prefixWord ++ tailWord_3142526).sum := by decide
  have hdescent : baseEnd_3142526 < baseStart_3142526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142584 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 1, 3]
def baseStart_3142584 : Nat := 118140960795 + 3142584 * 2 ^ 59
def prefixEnd_3142584 : Nat := 4983230072969 + 3 ^ 40 * 3142584 * 2
def baseEnd_3142584 : Nat := 1075770726086025239565017

theorem tailTrace_3142584 : CollatzResearch.WordTrace tailWord_3142584 prefixEnd_3142584 1075770726086025239565017 := by
  unfold tailWord_3142584
  simp only [CollatzResearch.WordTrace]
  refine ⟨57309727423481176731297403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76412969897974902308396537 57309727423481176731297403)
  ·
    refine ⟨85964591135221765096946105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57309727423481176731297403 85964591135221765096946105)
    ·
      refine ⟨64473443351416323822709579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85964591135221765096946105 64473443351416323822709579)
      ·
        refine ⟨96710165027124485734064369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64473443351416323822709579 96710165027124485734064369)
        ·
          refine ⟨72532623770343364300548277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96710165027124485734064369 72532623770343364300548277)
          ·
            refine ⟨6799933478469690403176401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72532623770343364300548277 6799933478469690403176401)
            ·
              refine ⟨5099950108852267802382301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799933478469690403176401 5099950108852267802382301)
              ·
                refine ⟨1912481290819600425893363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5099950108852267802382301 1912481290819600425893363)
                ·
                  refine ⟨2868721936229400638840045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912481290819600425893363 2868721936229400638840045)
                  ·
                    refine ⟨1075770726086025239565017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868721936229400638840045 1075770726086025239565017)
                    ·
                      rfl

theorem cell22_3142584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_3142584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142584 prefixEnd_3142584 := by exact prefixLift 3142584
  have htrace : WordTrace (prefixWord ++ tailWord_3142584) baseStart_3142584 baseEnd_3142584 := by
    simpa [prefixWord, tailWord_3142584, baseEnd_3142584] using wordTrace_append hprefix tailTrace_3142584
  have hstable : (prefixWord ++ tailWord_3142584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142584).length < 2 ^ (prefixWord ++ tailWord_3142584).sum := by decide
  have hdescent : baseEnd_3142584 < baseStart_3142584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142627 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 1, 4]
def baseStart_3142627 : Nat := 118140960795 + 3142627 * 2 ^ 59
def prefixEnd_3142627 : Nat := 4983230072969 + 3 ^ 40 * 3142627 * 2
def baseEnd_3142627 : Nat := 1075785445864787460739885

theorem tailTrace_3142627 : CollatzResearch.WordTrace tailWord_3142627 prefixEnd_3142627 1075785445864787460739885 := by
  unfold tailWord_3142627
  simp only [CollatzResearch.WordTrace]
  refine ⟨114621023185806571806410135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76414015457204381204273423 114621023185806571806410135)
  ·
    refine ⟨171931534778709857709615203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114621023185806571806410135 171931534778709857709615203)
    ·
      refine ⟨257897302168064786564422805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171931534778709857709615203 257897302168064786564422805)
      ·
        refine ⟨12088936039128036870207319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257897302168064786564422805 12088936039128036870207319)
        ·
          refine ⟨18133404058692055305310979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088936039128036870207319 18133404058692055305310979)
          ·
            refine ⟨27200106088038082957966469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18133404058692055305310979 27200106088038082957966469)
            ·
              refine ⟨5100019891507140554618713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27200106088038082957966469 5100019891507140554618713)
              ·
                refine ⟨3825014918630355415964035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100019891507140554618713 3825014918630355415964035)
                ·
                  refine ⟨5737522377945533123946053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825014918630355415964035 5737522377945533123946053)
                  ·
                    refine ⟨1075785445864787460739885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737522377945533123946053 1075785445864787460739885)
                    ·
                      rfl

theorem cell22_3142627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 4].length) (baseStart_3142627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142627 prefixEnd_3142627 := by exact prefixLift 3142627
  have htrace : WordTrace (prefixWord ++ tailWord_3142627) baseStart_3142627 baseEnd_3142627 := by
    simpa [prefixWord, tailWord_3142627, baseEnd_3142627] using wordTrace_append hprefix tailTrace_3142627
  have hstable : (prefixWord ++ tailWord_3142627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142627).length < 2 ^ (prefixWord ++ tailWord_3142627).sum := by decide
  have hdescent : baseEnd_3142627 < baseStart_3142627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142657 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3142657 : Nat := 118140960795 + 3142657 * 2 ^ 59
def prefixEnd_3142657 : Nat := 4983230072969 + 3 ^ 40 * 3142657 * 2
def baseEnd_3142657 : Nat := 1075795715477877382489793

theorem tailTrace_3142657 : CollatzResearch.WordTrace tailWord_3142657 prefixEnd_3142657 1075795715477877382489793 := by
  unfold tailWord_3142657
  simp only [CollatzResearch.WordTrace]
  refine ⟨114622117375697886930002225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76414744917131924620001483 114622117375697886930002225)
  ·
    refine ⟨85966588031773415197501669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114622117375697886930002225 85966588031773415197501669)
    ·
      refine ⟨16118735255957515349531563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85966588031773415197501669 16118735255957515349531563)
      ·
        refine ⟨24178102883936273024297345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16118735255957515349531563 24178102883936273024297345)
        ·
          refine ⟨18133577162952204768223009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24178102883936273024297345 18133577162952204768223009)
          ·
            refine ⟨13600182872214153576167257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18133577162952204768223009 13600182872214153576167257)
            ·
              refine ⟨10200137154160615182125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13600182872214153576167257 10200137154160615182125443)
              ·
                refine ⟨15300205731240922773188165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200137154160615182125443 15300205731240922773188165)
                ·
                  refine ⟨2868788574607673019972781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15300205731240922773188165 2868788574607673019972781)
                  ·
                    refine ⟨1075795715477877382489793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868788574607673019972781 1075795715477877382489793)
                    ·
                      rfl

theorem cell22_3142657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3142657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142657 prefixEnd_3142657 := by exact prefixLift 3142657
  have htrace : WordTrace (prefixWord ++ tailWord_3142657) baseStart_3142657 baseEnd_3142657 := by
    simpa [prefixWord, tailWord_3142657, baseEnd_3142657] using wordTrace_append hprefix tailTrace_3142657
  have hstable : (prefixWord ++ tailWord_3142657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142657).length < 2 ^ (prefixWord ++ tailWord_3142657).sum := by decide
  have hdescent : baseEnd_3142657 < baseStart_3142657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142670 : List Nat := [4, 1, 1, 2, 2, 2, 1, 9]
def baseStart_3142670 : Nat := 118140960795 + 3142670 * 2 ^ 59
def prefixEnd_3142670 : Nat := 4983230072969 + 3 ^ 40 * 3142670 * 2
def baseEnd_3142670 : Nat := 119533351738172186879417

theorem tailTrace_3142670 : CollatzResearch.WordTrace tailWord_3142670 prefixEnd_3142670 119533351738172186879417 := by
  unfold tailWord_3142670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14327823940581348768778183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76415061016433860100150309 14327823940581348768778183)
  ·
    refine ⟨21491735910872023153167275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14327823940581348768778183 21491735910872023153167275)
    ·
      refine ⟨32237603866308034729750913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21491735910872023153167275 32237603866308034729750913)
      ·
        refine ⟨24178202899731026047313185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32237603866308034729750913 24178202899731026047313185)
        ·
          refine ⟨18133652174798269535484889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24178202899731026047313185 18133652174798269535484889)
          ·
            refine ⟨13600239131098702151613667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18133652174798269535484889 13600239131098702151613667)
            ·
              refine ⟨20400358696648053227420501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13600239131098702151613667 20400358696648053227420501)
              ·
                refine ⟨119533351738172186879417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20400358696648053227420501 119533351738172186879417)
                ·
                  rfl

theorem cell22_3142670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_3142670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142670 prefixEnd_3142670 := by exact prefixLift 3142670
  have htrace : WordTrace (prefixWord ++ tailWord_3142670) baseStart_3142670 baseEnd_3142670 := by
    simpa [prefixWord, tailWord_3142670, baseEnd_3142670] using wordTrace_append hprefix tailTrace_3142670
  have hstable : (prefixWord ++ tailWord_3142670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142670).length < 2 ^ (prefixWord ++ tailWord_3142670).sum := by decide
  have hdescent : baseEnd_3142670 < baseStart_3142670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142730 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3142730 : Nat := 118140960795 + 3142730 * 2 ^ 59
def prefixEnd_3142730 : Nat := 4983230072969 + 3 ^ 40 * 3142730 * 2
def baseEnd_3142730 : Nat := 1075820704869729525414569

theorem tailTrace_3142730 : CollatzResearch.WordTrace tailWord_3142730 prefixEnd_3142730 1075820704869729525414569 := by
  unfold tailWord_3142730
  simp only [CollatzResearch.WordTrace]
  refine ⟨28656194976108355099352411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76416519936288946931606429 28656194976108355099352411)
  ·
    refine ⟨42984292464162532649028617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28656194976108355099352411 42984292464162532649028617)
    ·
      refine ⟨32238219348121899486771463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42984292464162532649028617 32238219348121899486771463)
      ·
        refine ⟨48357329022182849230157195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32238219348121899486771463 48357329022182849230157195)
        ·
          refine ⟨72535993533274273845235793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48357329022182849230157195 72535993533274273845235793)
          ·
            refine ⟨54401995149955705383926845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72535993533274273845235793 54401995149955705383926845)
            ·
              refine ⟨20400748181233389518972567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54401995149955705383926845 20400748181233389518972567)
              ·
                refine ⟨30601122271850084278458851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20400748181233389518972567 30601122271850084278458851)
                ·
                  refine ⟨45901683407775126417688277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30601122271850084278458851 45901683407775126417688277)
                  ·
                    refine ⟨1075820704869729525414569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45901683407775126417688277 1075820704869729525414569)
                    ·
                      rfl

theorem cell22_3142730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3142730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142730 prefixEnd_3142730 := by exact prefixLift 3142730
  have htrace : WordTrace (prefixWord ++ tailWord_3142730) baseStart_3142730 baseEnd_3142730 := by
    simpa [prefixWord, tailWord_3142730, baseEnd_3142730] using wordTrace_append hprefix tailTrace_3142730
  have hstable : (prefixWord ++ tailWord_3142730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142730).length < 2 ^ (prefixWord ++ tailWord_3142730).sum := by decide
  have hdescent : baseEnd_3142730 < baseStart_3142730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142807 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3142807 : Nat := 118140960795 + 3142807 * 2 ^ 59
def prefixEnd_3142807 : Nat := 4983230072969 + 3 ^ 40 * 3142807 * 2
def baseEnd_3142807 : Nat := 1075847063543326991239333

theorem tailTrace_3142807 : CollatzResearch.WordTrace tailWord_3142807 prefixEnd_3142807 1075847063543326991239333 := by
  unfold tailWord_3142807
  simp only [CollatzResearch.WordTrace]
  refine ⟨114627588325154462547962675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76418392216769641698641783 114627588325154462547962675)
  ·
    refine ⟨171941382487731693821944013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114627588325154462547962675 171941382487731693821944013)
    ·
      refine ⟨64478018432899385183229005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171941382487731693821944013 64478018432899385183229005)
      ·
        refine ⟨24179256912337269443710877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64478018432899385183229005 24179256912337269443710877)
        ·
          refine ⟨9067221342126476041391579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24179256912337269443710877 9067221342126476041391579)
          ·
            refine ⟨13600832013189714062087369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067221342126476041391579 13600832013189714062087369)
            ·
              refine ⟨10200624009892285546565527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13600832013189714062087369 10200624009892285546565527)
              ·
                refine ⟨15300936014838428319848291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200624009892285546565527 15300936014838428319848291)
                ·
                  refine ⟨22951404022257642479772437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15300936014838428319848291 22951404022257642479772437)
                  ·
                    refine ⟨1075847063543326991239333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22951404022257642479772437 1075847063543326991239333)
                    ·
                      rfl

theorem cell22_3142807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3142807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142807 prefixEnd_3142807 := by exact prefixLift 3142807
  have htrace : WordTrace (prefixWord ++ tailWord_3142807) baseStart_3142807 baseEnd_3142807 := by
    simpa [prefixWord, tailWord_3142807, baseEnd_3142807] using wordTrace_append hprefix tailTrace_3142807
  have hstable : (prefixWord ++ tailWord_3142807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142807).length < 2 ^ (prefixWord ++ tailWord_3142807).sum := by decide
  have hdescent : baseEnd_3142807 < baseStart_3142807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142826 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3142826 : Nat := 118140960795 + 3142826 * 2 ^ 59
def prefixEnd_3142826 : Nat := 4983230072969 + 3 ^ 40 * 3142826 * 2
def baseEnd_3142826 : Nat := 1075853567631617275014275

theorem tailTrace_3142826 : CollatzResearch.WordTrace tailWord_3142826 prefixEnd_3142826 1075853567631617275014275 := by
  unfold tailWord_3142826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28657070328021407198226083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76418854208057085861936221 28657070328021407198226083)
  ·
    refine ⟨42985605492032110797339125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28657070328021407198226083 42985605492032110797339125)
    ·
      refine ⟨4029900514878010387250543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42985605492032110797339125 4029900514878010387250543)
      ·
        refine ⟨6044850772317015580875815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029900514878010387250543 6044850772317015580875815)
        ·
          refine ⟨9067276158475523371313723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044850772317015580875815 9067276158475523371313723)
          ·
            refine ⟨13600914237713285056970585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067276158475523371313723 13600914237713285056970585)
            ·
              refine ⟨10200685678284963792727939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13600914237713285056970585 10200685678284963792727939)
              ·
                refine ⟨15301028517427445689091909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200685678284963792727939 15301028517427445689091909)
                ·
                  refine ⟨2868942847017646066704733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15301028517427445689091909 2868942847017646066704733)
                  ·
                    refine ⟨1075853567631617275014275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2868942847017646066704733 1075853567631617275014275)
                    ·
                      rfl

theorem cell22_3142826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3142826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142826 prefixEnd_3142826 := by exact prefixLift 3142826
  have htrace : WordTrace (prefixWord ++ tailWord_3142826) baseStart_3142826 baseEnd_3142826 := by
    simpa [prefixWord, tailWord_3142826, baseEnd_3142826] using wordTrace_append hprefix tailTrace_3142826
  have hstable : (prefixWord ++ tailWord_3142826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142826).length < 2 ^ (prefixWord ++ tailWord_3142826).sum := by decide
  have hdescent : baseEnd_3142826 < baseStart_3142826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142946 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_3142946 : Nat := 118140960795 + 3142946 * 2 ^ 59
def prefixEnd_3142946 : Nat := 4983230072969 + 3 ^ 40 * 3142946 * 2
def baseEnd_3142946 : Nat := 358631548694658987337969

theorem tailTrace_3142946 : CollatzResearch.WordTrace tailWord_3142946 prefixEnd_3142946 358631548694658987337969 := by
  unfold tailWord_3142946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28658164517912722321818173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76421772047767259524848461 28658164517912722321818173)
  ·
    refine ⟨10746811694217270870681815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28658164517912722321818173 10746811694217270870681815)
    ·
      refine ⟨16120217541325906306022723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10746811694217270870681815 16120217541325906306022723)
      ·
        refine ⟨24180326311988859459034085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16120217541325906306022723 24180326311988859459034085)
        ·
          refine ⟨4533811183497911148568891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24180326311988859459034085 4533811183497911148568891)
          ·
            refine ⟨6800716775246866722853337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533811183497911148568891 6800716775246866722853337)
            ·
              refine ⟨5100537581435150042140003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800716775246866722853337 5100537581435150042140003)
              ·
                refine ⟨7650806372152725063210005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100537581435150042140003 7650806372152725063210005)
                ·
                  refine ⟨358631548694658987337969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7650806372152725063210005 358631548694658987337969)
                  ·
                    rfl

theorem cell22_3142946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_3142946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142946 prefixEnd_3142946 := by exact prefixLift 3142946
  have htrace : WordTrace (prefixWord ++ tailWord_3142946) baseStart_3142946 baseEnd_3142946 := by
    simpa [prefixWord, tailWord_3142946, baseEnd_3142946] using wordTrace_append hprefix tailTrace_3142946
  have hstable : (prefixWord ++ tailWord_3142946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142946).length < 2 ^ (prefixWord ++ tailWord_3142946).sum := by decide
  have hdescent : baseEnd_3142946 < baseStart_3142946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142961 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_3142961 : Nat := 118140960795 + 3142961 * 2 ^ 59
def prefixEnd_3142961 : Nat := 4983230072969 + 3 ^ 40 * 3142961 * 2
def baseEnd_3142961 : Nat := 1075899780890521922888861

theorem tailTrace_3142961 : CollatzResearch.WordTrace tailWord_3142961 prefixEnd_3142961 1075899780890521922888861 := by
  unfold tailWord_3142961
  simp only [CollatzResearch.WordTrace]
  refine ⟨114633205166596546849068737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76422136777731031232712491 114633205166596546849068737)
  ·
    refine ⟨85974903874947410136801553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114633205166596546849068737 85974903874947410136801553)
    ·
      refine ⟨64481177906210557602601165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85974903874947410136801553 64481177906210557602601165)
      ·
        refine ⟨24180441714828959100975437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64481177906210557602601165 24180441714828959100975437)
        ·
          refine ⟨9067665643060859662865789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24180441714828959100975437 9067665643060859662865789)
          ·
            refine ⟨3400374616147822373574671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9067665643060859662865789 3400374616147822373574671)
            ·
              refine ⟨5100561924221733560362007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400374616147822373574671 5100561924221733560362007)
              ·
                refine ⟨7650842886332600340543011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100561924221733560362007 7650842886332600340543011)
                ·
                  refine ⟨11476264329498900510814517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7650842886332600340543011 11476264329498900510814517)
                  ·
                    refine ⟨1075899780890521922888861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11476264329498900510814517 1075899780890521922888861)
                    ·
                      rfl

theorem cell22_3142961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_3142961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142961 prefixEnd_3142961 := by exact prefixLift 3142961
  have htrace : WordTrace (prefixWord ++ tailWord_3142961) baseStart_3142961 baseEnd_3142961 := by
    simpa [prefixWord, tailWord_3142961, baseEnd_3142961] using wordTrace_append hprefix tailTrace_3142961
  have hstable : (prefixWord ++ tailWord_3142961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142961).length < 2 ^ (prefixWord ++ tailWord_3142961).sum := by decide
  have hdescent : baseEnd_3142961 < baseStart_3142961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142974 : List Nat := [4, 2, 1, 2, 1, 1, 3, 8]
def baseStart_3142974 : Nat := 118140960795 + 3142974 * 2 ^ 59
def prefixEnd_3142974 : Nat := 4983230072969 + 3 ^ 40 * 3142974 * 2
def baseEnd_3142974 : Nat := 119544914561799358034869

theorem tailTrace_3142974 : CollatzResearch.WordTrace tailWord_3142974 prefixEnd_3142974 119544914561799358034869 := by
  unfold tailWord_3142974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14329209914443681258661497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76422452877032966712861317 14329209914443681258661497)
  ·
    refine ⟨10746907435832760943996123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14329209914443681258661497 10746907435832760943996123)
    ·
      refine ⟨16120361153749141415994185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10746907435832760943996123 16120361153749141415994185)
      ·
        refine ⟨12090270865311856061995639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16120361153749141415994185 12090270865311856061995639)
        ·
          refine ⟨18135406297967784092993459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12090270865311856061995639 18135406297967784092993459)
          ·
            refine ⟨27203109446951676139490189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18135406297967784092993459 27203109446951676139490189)
            ·
              refine ⟨10201166042606878552308821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27203109446951676139490189 10201166042606878552308821)
              ·
                refine ⟨119544914561799358034869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10201166042606878552308821 119544914561799358034869)
                ·
                  rfl

theorem cell22_3142974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_3142974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142974 prefixEnd_3142974 := by exact prefixLift 3142974
  have htrace : WordTrace (prefixWord ++ tailWord_3142974) baseStart_3142974 baseEnd_3142974 := by
    simpa [prefixWord, tailWord_3142974, baseEnd_3142974] using wordTrace_append hprefix tailTrace_3142974
  have hstable : (prefixWord ++ tailWord_3142974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142974).length < 2 ^ (prefixWord ++ tailWord_3142974).sum := by decide
  have hdescent : baseEnd_3142974 < baseStart_3142974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3142980 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 4]
def baseStart_3142980 : Nat := 118140960795 + 3142980 * 2 ^ 59
def prefixEnd_3142980 : Nat := 4983230072969 + 3 ^ 40 * 3142980 * 2
def baseEnd_3142980 : Nat := 358635428326270735554601

theorem tailTrace_3142980 : CollatzResearch.WordTrace tailWord_3142980 prefixEnd_3142980 358635428326270735554601 := by
  unfold tailWord_3142980
  simp only [CollatzResearch.WordTrace]
  refine ⟨57316949076763856547005197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76422598769018475396006929 57316949076763856547005197)
  ·
    refine ⟨21493855903786446205126949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57316949076763856547005197 21493855903786446205126949)
    ·
      refine ⟨4030097981959958663461303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21493855903786446205126949 4030097981959958663461303)
      ·
        refine ⟨6045146972939937995191955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030097981959958663461303 6045146972939937995191955)
        ·
          refine ⟨9067720459409906992787933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045146972939937995191955 9067720459409906992787933)
          ·
            refine ⟨3400395172278715122295475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9067720459409906992787933 3400395172278715122295475)
            ·
              refine ⟨5100592758418072683443213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400395172278715122295475 5100592758418072683443213)
              ·
                refine ⟨1912722284406777256291205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5100592758418072683443213 1912722284406777256291205)
                ·
                  refine ⟨358635428326270735554601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912722284406777256291205 358635428326270735554601)
                  ·
                    rfl

theorem cell22_3142980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_3142980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3142980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3142980 prefixEnd_3142980 := by exact prefixLift 3142980
  have htrace : WordTrace (prefixWord ++ tailWord_3142980) baseStart_3142980 baseEnd_3142980 := by
    simpa [prefixWord, tailWord_3142980, baseEnd_3142980] using wordTrace_append hprefix tailTrace_3142980
  have hstable : (prefixWord ++ tailWord_3142980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3142980).length < 2 ^ (prefixWord ++ tailWord_3142980).sum := by decide
  have hdescent : baseEnd_3142980 < baseStart_3142980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3142980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143068 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_3143068 : Nat := 118140960795 + 3143068 * 2 ^ 59
def prefixEnd_3143068 : Nat := 4983230072969 + 3 ^ 40 * 3143068 * 2
def baseEnd_3143068 : Nat := 1075936409177209310463533

theorem tailTrace_3143068 : CollatzResearch.WordTrace tailWord_3143068 prefixEnd_3143068 1075936409177209310463533 := by
  unfold tailWord_3143068
  simp only [CollatzResearch.WordTrace]
  refine ⟨57318553888604452061606929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76424738518139269415475905 57318553888604452061606929)
  ·
    refine ⟨42988915416453339046205197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57318553888604452061606929 42988915416453339046205197)
    ·
      refine ⟨16120843281170002142326949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42988915416453339046205197 16120843281170002142326949)
      ·
        refine ⟨3022658115219375401686303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16120843281170002142326949 3022658115219375401686303)
        ·
          refine ⟨4533987172829063102529455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022658115219375401686303 4533987172829063102529455)
          ·
            refine ⟨6800980759243594653794183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533987172829063102529455 6800980759243594653794183)
            ·
              refine ⟨10201471138865391980691275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800980759243594653794183 10201471138865391980691275)
              ·
                refine ⟨15302206708298087971036913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201471138865391980691275 15302206708298087971036913)
                ·
                  refine ⟨11476655031223565978277685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15302206708298087971036913 11476655031223565978277685)
                  ·
                    refine ⟨1075936409177209310463533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11476655031223565978277685 1075936409177209310463533)
                    ·
                      rfl

theorem cell22_3143068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_3143068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143068 prefixEnd_3143068 := by exact prefixLift 3143068
  have htrace : WordTrace (prefixWord ++ tailWord_3143068) baseStart_3143068 baseEnd_3143068 := by
    simpa [prefixWord, tailWord_3143068, baseEnd_3143068] using wordTrace_append hprefix tailTrace_3143068
  have hstable : (prefixWord ++ tailWord_3143068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143068).length < 2 ^ (prefixWord ++ tailWord_3143068).sum := by decide
  have hdescent : baseEnd_3143068 < baseStart_3143068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143130 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_3143130 : Nat := 118140960795 + 3143130 * 2 ^ 59
def prefixEnd_3143130 : Nat := 4983230072969 + 3 ^ 40 * 3143130 * 2
def baseEnd_3143130 : Nat := 1075957633044261815413343

theorem tailTrace_3143130 : CollatzResearch.WordTrace tailWord_3143130 prefixEnd_3143130 1075957633044261815413343 := by
  unfold tailWord_3143130
  simp only [CollatzResearch.WordTrace]
  refine ⟨28659842275746072177992711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76426246068656192474647229 28659842275746072177992711)
  ·
    refine ⟨42989763413619108266989067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28659842275746072177992711 42989763413619108266989067)
    ·
      refine ⟨64484645120428662400483601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42989763413619108266989067 64484645120428662400483601)
      ·
        refine ⟨48363483840321496800362701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64484645120428662400483601 48363483840321496800362701)
        ·
          refine ⟨18136306440120561300136013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48363483840321496800362701 18136306440120561300136013)
          ·
            refine ⟨6801114915045210487551005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18136306440120561300136013 6801114915045210487551005)
            ·
              refine ⟨2550418093141953932831627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6801114915045210487551005 2550418093141953932831627)
              ·
                refine ⟨3825627139712930899247441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550418093141953932831627 3825627139712930899247441)
                ·
                  refine ⟨2869220354784698174435581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825627139712930899247441 2869220354784698174435581)
                  ·
                    refine ⟨1075957633044261815413343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869220354784698174435581 1075957633044261815413343)
                    ·
                      rfl

theorem cell22_3143130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_3143130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143130 prefixEnd_3143130 := by exact prefixLift 3143130
  have htrace : WordTrace (prefixWord ++ tailWord_3143130) baseStart_3143130 baseEnd_3143130 := by
    simpa [prefixWord, tailWord_3143130, baseEnd_3143130] using wordTrace_append hprefix tailTrace_3143130
  have hstable : (prefixWord ++ tailWord_3143130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143130).length < 2 ^ (prefixWord ++ tailWord_3143130).sum := by decide
  have hdescent : baseEnd_3143130 < baseStart_3143130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143143 : List Nat := [1, 1, 5, 2, 1, 4, 2, 6]
def baseStart_3143143 : Nat := 118140960795 + 3143143 * 2 ^ 59
def prefixEnd_3143143 : Nat := 4983230072969 + 3 ^ 40 * 3143143 * 2
def baseEnd_3143143 : Nat := 119551342578881568315367

theorem tailTrace_3143143 : CollatzResearch.WordTrace tailWord_3143143 prefixEnd_3143143 119551342578881568315367 := by
  unfold tailWord_3143143
  simp only [CollatzResearch.WordTrace]
  refine ⟨114639843251937191932194083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76426562167958127954796055 114639843251937191932194083)
  ·
    refine ⟨171959764877905787898291125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114639843251937191932194083 171959764877905787898291125)
    ·
      refine ⟨16121227957303667615464793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171959764877905787898291125 16121227957303667615464793)
      ·
        refine ⟨12090920967977750711598595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16121227957303667615464793 12090920967977750711598595)
        ·
          refine ⟨18136381451966626067397893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12090920967977750711598595 18136381451966626067397893)
          ·
            refine ⟨3400571522243742387637105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18136381451966626067397893 3400571522243742387637105)
            ·
              refine ⟨2550428641682806790727829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3400571522243742387637105 2550428641682806790727829)
              ·
                refine ⟨119551342578881568315367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2550428641682806790727829 119551342578881568315367)
                ·
                  rfl

theorem cell22_3143143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 6].length) (baseStart_3143143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143143 prefixEnd_3143143 := by exact prefixLift 3143143
  have htrace : WordTrace (prefixWord ++ tailWord_3143143) baseStart_3143143 baseEnd_3143143 := by
    simpa [prefixWord, tailWord_3143143, baseEnd_3143143] using wordTrace_append hprefix tailTrace_3143143
  have hstable : (prefixWord ++ tailWord_3143143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143143).length < 2 ^ (prefixWord ++ tailWord_3143143).sum := by decide
  have hdescent : baseEnd_3143143 < baseStart_3143143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143175 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 3, 3]
def baseStart_3143175 : Nat := 118140960795 + 3143175 * 2 ^ 59
def prefixEnd_3143175 : Nat := 4983230072969 + 3 ^ 40 * 3143175 * 2
def baseEnd_3143175 : Nat := 1075973037463896698038205

theorem tailTrace_3143175 : CollatzResearch.WordTrace tailWord_3143175 prefixEnd_3143175 1075973037463896698038205 := by
  unfold tailWord_3143175
  simp only [CollatzResearch.WordTrace]
  refine ⟨114641010387821261397358979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76427340258547507598239319 114641010387821261397358979)
  ·
    refine ⟨171961515581731892096038469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114641010387821261397358979 171961515581731892096038469)
    ·
      refine ⟨32242784171574729768007213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171961515581731892096038469 32242784171574729768007213)
      ·
        refine ⟨12091044064340523663002705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32242784171574729768007213 12091044064340523663002705)
        ·
          refine ⟨9068283048255392747252029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12091044064340523663002705 9068283048255392747252029)
          ·
            refine ⟨3400606143095772280219511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9068283048255392747252029 3400606143095772280219511)
            ·
              refine ⟨5100909214643658420329267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400606143095772280219511 5100909214643658420329267)
              ·
                refine ⟨7651363821965487630493901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100909214643658420329267 7651363821965487630493901)
                ·
                  refine ⟨2869261433237057861435213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7651363821965487630493901 2869261433237057861435213)
                  ·
                    refine ⟨1075973037463896698038205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869261433237057861435213 1075973037463896698038205)
                    ·
                      rfl

theorem cell22_3143175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_3143175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143175 prefixEnd_3143175 := by exact prefixLift 3143175
  have htrace : WordTrace (prefixWord ++ tailWord_3143175) baseStart_3143175 baseEnd_3143175 := by
    simpa [prefixWord, tailWord_3143175, baseEnd_3143175] using wordTrace_append hprefix tailTrace_3143175
  have hstable : (prefixWord ++ tailWord_3143175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143175).length < 2 ^ (prefixWord ++ tailWord_3143175).sum := by decide
  have hdescent : baseEnd_3143175 < baseStart_3143175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143181 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3143181 : Nat := 118140960795 + 3143181 * 2 ^ 59
def prefixEnd_3143181 : Nat := 4983230072969 + 3 ^ 40 * 3143181 * 2
def baseEnd_3143181 : Nat := 1075975091386514682388187

theorem tailTrace_3143181 : CollatzResearch.WordTrace tailWord_3143181 prefixEnd_3143181 1075975091386514682388187 := by
  unfold tailWord_3143181
  simp only [CollatzResearch.WordTrace]
  refine ⟨114641229225799524422077397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76427486150533016281384931 114641229225799524422077397)
  ·
    refine ⟨2686903809979676353642439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114641229225799524422077397 2686903809979676353642439)
    ·
      refine ⟨4030355714969514530463659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686903809979676353642439 4030355714969514530463659)
      ·
        refine ⟨6045533572454271795695489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030355714969514530463659 6045533572454271795695489)
        ·
          refine ⟨4534150179340703846771617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6045533572454271795695489 4534150179340703846771617)
          ·
            refine ⟨3400612634505527885078713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4534150179340703846771617 3400612634505527885078713)
            ·
              refine ⟨2550459475879145913809035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3400612634505527885078713 2550459475879145913809035)
              ·
                refine ⟨3825689213818718870713553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550459475879145913809035 3825689213818718870713553)
                ·
                  refine ⟨2869266910364039153035165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825689213818718870713553 2869266910364039153035165)
                  ·
                    refine ⟨1075975091386514682388187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869266910364039153035165 1075975091386514682388187)
                    ·
                      rfl

theorem cell22_3143181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3143181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143181 prefixEnd_3143181 := by exact prefixLift 3143181
  have htrace : WordTrace (prefixWord ++ tailWord_3143181) baseStart_3143181 baseEnd_3143181 := by
    simpa [prefixWord, tailWord_3143181, baseEnd_3143181] using wordTrace_append hprefix tailTrace_3143181
  have hstable : (prefixWord ++ tailWord_3143181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143181).length < 2 ^ (prefixWord ++ tailWord_3143181).sum := by decide
  have hdescent : baseEnd_3143181 < baseStart_3143181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143246 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3143246 : Nat := 118140960795 + 3143246 * 2 ^ 59
def prefixEnd_3143246 : Nat := 4983230072969 + 3 ^ 40 * 3143246 * 2
def baseEnd_3143246 : Nat := 1075997342214876179512987

theorem tailTrace_3143246 : CollatzResearch.WordTrace tailWord_3143246 prefixEnd_3143246 1075997342214876179512987 := by
  unfold tailWord_3143246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330449996320505065399199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76429066647042693682129061 14330449996320505065399199)
  ·
    refine ⟨21495674994480757598098799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14330449996320505065399199 21495674994480757598098799)
    ·
      refine ⟨32243512491721136397148199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21495674994480757598098799 32243512491721136397148199)
      ·
        refine ⟨48365268737581704595722299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32243512491721136397148199 48365268737581704595722299)
        ·
          refine ⟨72547903106372556893583449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48365268737581704595722299 72547903106372556893583449)
          ·
            refine ⟨54410927329779417670187587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72547903106372556893583449 54410927329779417670187587)
            ·
              refine ⟨81616390994669126505281381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54410927329779417670187587 81616390994669126505281381)
              ·
                refine ⟨15303073311500461219740259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81616390994669126505281381 15303073311500461219740259)
                ·
                  refine ⟨22954609967250691829610389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15303073311500461219740259 22954609967250691829610389)
                  ·
                    refine ⟨1075997342214876179512987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22954609967250691829610389 1075997342214876179512987)
                    ·
                      rfl

theorem cell22_3143246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3143246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143246 prefixEnd_3143246 := by exact prefixLift 3143246
  have htrace : WordTrace (prefixWord ++ tailWord_3143246) baseStart_3143246 baseEnd_3143246 := by
    simpa [prefixWord, tailWord_3143246, baseEnd_3143246] using wordTrace_append hprefix tailTrace_3143246
  have hstable : (prefixWord ++ tailWord_3143246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143246).length < 2 ^ (prefixWord ++ tailWord_3143246).sum := by decide
  have hdescent : baseEnd_3143246 < baseStart_3143246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143248 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_3143248 : Nat := 118140960795 + 3143248 * 2 ^ 59
def prefixEnd_3143248 : Nat := 4983230072969 + 3 ^ 40 * 3143248 * 2
def baseEnd_3143248 : Nat := 1075998026855748840962981

theorem tailTrace_3143248 : CollatzResearch.WordTrace tailWord_3143248 prefixEnd_3143248 1075998026855748840962981 := by
  unfold tailWord_3143248
  simp only [CollatzResearch.WordTrace]
  refine ⟨57321836458278397432383199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76429115277704529909844265 57321836458278397432383199)
  ·
    refine ⟨85982754687417596148574799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57321836458278397432383199 85982754687417596148574799)
    ·
      refine ⟨128974132031126394222862199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85982754687417596148574799 128974132031126394222862199)
      ·
        refine ⟨193461198046689591334293299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128974132031126394222862199 193461198046689591334293299)
        ·
          refine ⟨290191797070034387001439949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193461198046689591334293299 290191797070034387001439949)
          ·
            refine ⟨108821923901262895125539981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290191797070034387001439949 108821923901262895125539981)
            ·
              refine ⟨40808221462973585672077493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108821923901262895125539981 40808221462973585672077493)
              ·
                refine ⟨3825770762153773656757265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40808221462973585672077493 3825770762153773656757265)
                ·
                  refine ⟨2869328071615330242567949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825770762153773656757265 2869328071615330242567949)
                  ·
                    refine ⟨1075998026855748840962981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869328071615330242567949 1075998026855748840962981)
                    ·
                      rfl

theorem cell22_3143248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_3143248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143248 prefixEnd_3143248 := by exact prefixLift 3143248
  have htrace : WordTrace (prefixWord ++ tailWord_3143248) baseStart_3143248 baseEnd_3143248 := by
    simpa [prefixWord, tailWord_3143248, baseEnd_3143248] using wordTrace_append hprefix tailTrace_3143248
  have hstable : (prefixWord ++ tailWord_3143248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143248).length < 2 ^ (prefixWord ++ tailWord_3143248).sum := by decide
  have hdescent : baseEnd_3143248 < baseStart_3143248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143278 : List Nat := [4, 1, 2, 2, 3, 1, 9]
def baseStart_3143278 : Nat := 118140960795 + 3143278 * 2 ^ 59
def prefixEnd_3143278 : Nat := 4983230072969 + 3 ^ 40 * 3143278 * 2
def baseEnd_3143278 : Nat := 39852159128475509730107

theorem tailTrace_3143278 : CollatzResearch.WordTrace tailWord_3143278 prefixEnd_3143278 39852159128475509730107 := by
  unfold tailWord_3143278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330595888306013748544811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76429844737632073325572325 14330595888306013748544811)
  ·
    refine ⟨21495893832459020622817217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14330595888306013748544811 21495893832459020622817217)
    ·
      refine ⟨16121920374344265467112913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21495893832459020622817217 16121920374344265467112913)
      ·
        refine ⟨12091440280758199100334685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16121920374344265467112913 12091440280758199100334685)
        ·
          refine ⟨4534290105284324662625507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12091440280758199100334685 4534290105284324662625507)
          ·
            refine ⟨6801435157926486993938261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534290105284324662625507 6801435157926486993938261)
            ·
              refine ⟨39852159128475509730107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6801435157926486993938261 39852159128475509730107)
              ·
                rfl

theorem cell22_3143278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 9].length) (baseStart_3143278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143278 prefixEnd_3143278 := by exact prefixLift 3143278
  have htrace : WordTrace (prefixWord ++ tailWord_3143278) baseStart_3143278 baseEnd_3143278 := by
    simpa [prefixWord, tailWord_3143278, baseEnd_3143278] using wordTrace_append hprefix tailTrace_3143278
  have hstable : (prefixWord ++ tailWord_3143278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143278).length < 2 ^ (prefixWord ++ tailWord_3143278).sum := by decide
  have hdescent : baseEnd_3143278 < baseStart_3143278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143282 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_3143282 : Nat := 118140960795 + 3143282 * 2 ^ 59
def prefixEnd_3143282 : Nat := 4983230072969 + 3 ^ 40 * 3143282 * 2
def baseEnd_3143282 : Nat := 1076009665750584085612877

theorem tailTrace_3143282 : CollatzResearch.WordTrace tailWord_3143282 prefixEnd_3143282 1076009665750584085612877 := by
  unfold tailWord_3143282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28661228249608404667876025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76429941998955745781002733 28661228249608404667876025)
  ·
    refine ⟨21495921187206303500907019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28661228249608404667876025 21495921187206303500907019)
    ·
      refine ⟨32243881780809455251360529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21495921187206303500907019 32243881780809455251360529)
      ·
        refine ⟨24182911335607091438520397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32243881780809455251360529 24182911335607091438520397)
        ·
          refine ⟨9068591750852659289445149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24182911335607091438520397 9068591750852659289445149)
          ·
            refine ⟨3400721906569747233541931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9068591750852659289445149 3400721906569747233541931)
            ·
              refine ⟨5101082859854620850312897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400721906569747233541931 5101082859854620850312897)
              ·
                refine ⟨3825812144890965637734673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5101082859854620850312897 3825812144890965637734673)
                ·
                  refine ⟨2869359108668224228301005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825812144890965637734673 2869359108668224228301005)
                  ·
                    refine ⟨1076009665750584085612877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869359108668224228301005 1076009665750584085612877)
                    ·
                      rfl

theorem cell22_3143282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_3143282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143282 prefixEnd_3143282 := by exact prefixLift 3143282
  have htrace : WordTrace (prefixWord ++ tailWord_3143282) baseStart_3143282 baseEnd_3143282 := by
    simpa [prefixWord, tailWord_3143282, baseEnd_3143282] using wordTrace_append hprefix tailTrace_3143282
  have hstable : (prefixWord ++ tailWord_3143282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143282).length < 2 ^ (prefixWord ++ tailWord_3143282).sum := by decide
  have hdescent : baseEnd_3143282 < baseStart_3143282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143310 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_3143310 : Nat := 118140960795 + 3143310 * 2 ^ 59
def prefixEnd_3143310 : Nat := 4983230072969 + 3 ^ 40 * 3143310 * 2
def baseEnd_3143310 : Nat := 1076019250722801345912791

theorem tailTrace_3143310 : CollatzResearch.WordTrace tailWord_3143310 prefixEnd_3143310 1076019250722801345912791 := by
  unfold tailWord_3143310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330741780291522431690423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76430622828221452969015589 14330741780291522431690423)
  ·
    refine ⟨21496112670437283647535635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14330741780291522431690423 21496112670437283647535635)
    ·
      refine ⟨32244169005655925471303453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21496112670437283647535635 32244169005655925471303453)
      ·
        refine ⟨12091563377120972051738795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32244169005655925471303453 12091563377120972051738795)
        ·
          refine ⟨18137345065681458077608193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12091563377120972051738795 18137345065681458077608193)
          ·
            refine ⟨13603008799261093558206145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18137345065681458077608193 13603008799261093558206145)
            ·
              refine ⟨10202256599445820168654609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13603008799261093558206145 10202256599445820168654609)
              ·
                refine ⟨7651692449584365126490957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10202256599445820168654609 7651692449584365126490957)
                ·
                  refine ⟨2869384668594136922434109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7651692449584365126490957 2869384668594136922434109)
                  ·
                    refine ⟨1076019250722801345912791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869384668594136922434109 1076019250722801345912791)
                    ·
                      rfl

theorem cell22_3143310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_3143310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143310 prefixEnd_3143310 := by exact prefixLift 3143310
  have htrace : WordTrace (prefixWord ++ tailWord_3143310) baseStart_3143310 baseEnd_3143310 := by
    simpa [prefixWord, tailWord_3143310, baseEnd_3143310] using wordTrace_append hprefix tailTrace_3143310
  have hstable : (prefixWord ++ tailWord_3143310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143310).length < 2 ^ (prefixWord ++ tailWord_3143310).sum := by decide
  have hdescent : baseEnd_3143310 < baseStart_3143310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143321 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_3143321 : Nat := 118140960795 + 3143321 * 2 ^ 59
def prefixEnd_3143321 : Nat := 4983230072969 + 3 ^ 40 * 3143321 * 2
def baseEnd_3143321 : Nat := 1076023016247600983887757

theorem tailTrace_3143321 : CollatzResearch.WordTrace tailWord_3143321 prefixEnd_3143321 1076023016247600983887757 := by
  unfold tailWord_3143321
  simp only [CollatzResearch.WordTrace]
  refine ⟨114646335445292328332173817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76430890296861552221449211 114646335445292328332173817)
  ·
    refine ⟨85984751583969246249130363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114646335445292328332173817 85984751583969246249130363)
    ·
      refine ⟨128977127375953869373695545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85984751583969246249130363 128977127375953869373695545)
      ·
        refine ⟨96732845531965402030271659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128977127375953869373695545 96732845531965402030271659)
        ·
          refine ⟨145099268297948103045407489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96732845531965402030271659 145099268297948103045407489)
          ·
            refine ⟨108824451223461077284055617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145099268297948103045407489 108824451223461077284055617)
            ·
              refine ⟨81618338417595807963041713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108824451223461077284055617 81618338417595807963041713)
              ·
                refine ⟨61213753813196855972281285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81618338417595807963041713 61213753813196855972281285)
                ·
                  refine ⟨11477578839974410494802741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61213753813196855972281285 11477578839974410494802741)
                  ·
                    refine ⟨1076023016247600983887757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11477578839974410494802741 1076023016247600983887757)
                    ·
                      rfl

theorem cell22_3143321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_3143321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143321 prefixEnd_3143321 := by exact prefixLift 3143321
  have htrace : WordTrace (prefixWord ++ tailWord_3143321) baseStart_3143321 baseEnd_3143321 := by
    simpa [prefixWord, tailWord_3143321, baseEnd_3143321] using wordTrace_append hprefix tailTrace_3143321
  have hstable : (prefixWord ++ tailWord_3143321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143321).length < 2 ^ (prefixWord ++ tailWord_3143321).sum := by decide
  have hdescent : baseEnd_3143321 < baseStart_3143321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143370 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_3143370 : Nat := 118140960795 + 3143370 * 2 ^ 59
def prefixEnd_3143370 : Nat := 4983230072969 + 3 ^ 40 * 3143370 * 2
def baseEnd_3143370 : Nat := 1076039789948981189412607

theorem tailTrace_3143370 : CollatzResearch.WordTrace tailWord_3143370 prefixEnd_3143370 1076039789948981189412607 := by
  unfold tailWord_3143370
  simp only [CollatzResearch.WordTrace]
  refine ⟨28662030655528702425176891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76432081748076539800471709 28662030655528702425176891)
  ·
    refine ⟨42993045983293053637765337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28662030655528702425176891 42993045983293053637765337)
    ·
      refine ⟨32244784487469790228324003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42993045983293053637765337 32244784487469790228324003)
      ·
        refine ⟨48367176731204685342486005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32244784487469790228324003 48367176731204685342486005)
        ·
          refine ⟨4534422818550439250858063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48367176731204685342486005 4534422818550439250858063)
          ·
            refine ⟨6801634227825658876287095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534422818550439250858063 6801634227825658876287095)
            ·
              refine ⟨10202451341738488314430643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6801634227825658876287095 10202451341738488314430643)
              ·
                refine ⟨15303677012607732471645965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10202451341738488314430643 15303677012607732471645965)
                ·
                  refine ⟨5738878879727899676867237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15303677012607732471645965 5738878879727899676867237)
                  ·
                    refine ⟨1076039789948981189412607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5738878879727899676867237 1076039789948981189412607)
                    ·
                      rfl

theorem cell22_3143370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_3143370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143370 prefixEnd_3143370 := by exact prefixLift 3143370
  have htrace : WordTrace (prefixWord ++ tailWord_3143370) baseStart_3143370 baseEnd_3143370 := by
    simpa [prefixWord, tailWord_3143370, baseEnd_3143370] using wordTrace_append hprefix tailTrace_3143370
  have hstable : (prefixWord ++ tailWord_3143370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143370).length < 2 ^ (prefixWord ++ tailWord_3143370).sum := by decide
  have hdescent : baseEnd_3143370 < baseStart_3143370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143383 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3143383 : Nat := 118140960795 + 3143383 * 2 ^ 59
def prefixEnd_3143383 : Nat := 4983230072969 + 3 ^ 40 * 3143383 * 2
def baseEnd_3143383 : Nat := 1076044240114653488837567

theorem tailTrace_3143383 : CollatzResearch.WordTrace tailWord_3143383 prefixEnd_3143383 1076044240114653488837567 := by
  unfold tailWord_3143383
  simp only [CollatzResearch.WordTrace]
  refine ⟨114648596771067712920930803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76432397847378475280620535 114648596771067712920930803)
  ·
    refine ⟨171972895156601569381396205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114648596771067712920930803 171972895156601569381396205)
    ·
      refine ⟨64489835683725588518023577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171972895156601569381396205 64489835683725588518023577)
      ·
        refine ⟨48367376762794191388517683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64489835683725588518023577 48367376762794191388517683)
        ·
          refine ⟨72551065144191287082776525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48367376762794191388517683 72551065144191287082776525)
          ·
            refine ⟨27206649429071732656041197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72551065144191287082776525 27206649429071732656041197)
            ·
              refine ⟨10202493535901899746015449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27206649429071732656041197 10202493535901899746015449)
              ·
                refine ⟨7651870151926424809511587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10202493535901899746015449 7651870151926424809511587)
                ·
                  refine ⟨11477805227889637214267381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7651870151926424809511587 11477805227889637214267381)
                  ·
                    refine ⟨1076044240114653488837567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11477805227889637214267381 1076044240114653488837567)
                    ·
                      rfl

theorem cell22_3143383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3143383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143383 prefixEnd_3143383 := by exact prefixLift 3143383
  have htrace : WordTrace (prefixWord ++ tailWord_3143383) baseStart_3143383 baseEnd_3143383 := by
    simpa [prefixWord, tailWord_3143383, baseEnd_3143383] using wordTrace_append hprefix tailTrace_3143383
  have hstable : (prefixWord ++ tailWord_3143383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143383).length < 2 ^ (prefixWord ++ tailWord_3143383).sum := by decide
  have hdescent : baseEnd_3143383 < baseStart_3143383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143402 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_3143402 : Nat := 118140960795 + 3143402 * 2 ^ 59
def prefixEnd_3143402 : Nat := 4983230072969 + 3 ^ 40 * 3143402 * 2
def baseEnd_3143402 : Nat := 358683581400981257537503

theorem tailTrace_3143402 : CollatzResearch.WordTrace tailWord_3143402 prefixEnd_3143402 358683581400981257537503 := by
  unfold tailWord_3143402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28662322439499719791468115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76432859838665919443914973 28662322439499719791468115)
  ·
    refine ⟨42993483659249579687202173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28662322439499719791468115 42993483659249579687202173)
    ·
      refine ⟨16122556372218592382700815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42993483659249579687202173 16122556372218592382700815)
      ·
        refine ⟨24183834558327888574051223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16122556372218592382700815 24183834558327888574051223)
        ·
          refine ⟨36275751837491832861076835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24183834558327888574051223 36275751837491832861076835)
          ·
            refine ⟨54413627756237749291615253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36275751837491832861076835 54413627756237749291615253)
            ·
              refine ⟨2550638801073644498044465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54413627756237749291615253 2550638801073644498044465)
              ·
                refine ⟨1912979100805233373533349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550638801073644498044465 1912979100805233373533349)
                ·
                  refine ⟨358683581400981257537503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912979100805233373533349 358683581400981257537503)
                  ·
                    rfl

theorem cell22_3143402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_3143402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143402 prefixEnd_3143402 := by exact prefixLift 3143402
  have htrace : WordTrace (prefixWord ++ tailWord_3143402) baseStart_3143402 baseEnd_3143402 := by
    simpa [prefixWord, tailWord_3143402, baseEnd_3143402] using wordTrace_append hprefix tailTrace_3143402
  have hstable : (prefixWord ++ tailWord_3143402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143402).length < 2 ^ (prefixWord ++ tailWord_3143402).sum := by decide
  have hdescent : baseEnd_3143402 < baseStart_3143402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143520 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_3143520 : Nat := 118140960795 + 3143520 * 2 ^ 59
def prefixEnd_3143520 : Nat := 4983230072969 + 3 ^ 40 * 3143520 * 2
def baseEnd_3143520 : Nat := 358697046004810266054049

theorem tailTrace_3143520 : CollatzResearch.WordTrace tailWord_3143520 prefixEnd_3143520 358697046004810266054049 := by
  unfold tailWord_3143520
  simp only [CollatzResearch.WordTrace]
  refine ⟨57326796785785692659334007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76435729047714256879112009 57326796785785692659334007)
  ·
    refine ⟨85990195178678538989001011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57326796785785692659334007 85990195178678538989001011)
    ·
      refine ⟨128985292768017808483501517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85990195178678538989001011 128985292768017808483501517)
      ·
        refine ⟨48369484788006678181313069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128985292768017808483501517 48369484788006678181313069)
        ·
          refine ⟨18138556795502504317992401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48369484788006678181313069 18138556795502504317992401)
          ·
            refine ⟨13603917596626878238494301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18138556795502504317992401 13603917596626878238494301)
            ·
              refine ⟨5101469098735079339435363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13603917596626878238494301 5101469098735079339435363)
              ·
                refine ⟨7652203648102619009153045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101469098735079339435363 7652203648102619009153045)
                ·
                  refine ⟨358697046004810266054049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7652203648102619009153045 358697046004810266054049)
                  ·
                    rfl

theorem cell22_3143520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_3143520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143520 prefixEnd_3143520 := by exact prefixLift 3143520
  have htrace : WordTrace (prefixWord ++ tailWord_3143520) baseStart_3143520 baseEnd_3143520 := by
    simpa [prefixWord, tailWord_3143520, baseEnd_3143520] using wordTrace_append hprefix tailTrace_3143520
  have hstable : (prefixWord ++ tailWord_3143520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143520).length < 2 ^ (prefixWord ++ tailWord_3143520).sum := by decide
  have hdescent : baseEnd_3143520 < baseStart_3143520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143704 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_3143704 : Nat := 118140960795 + 3143704 * 2 ^ 59
def prefixEnd_3143704 : Nat := 4983230072969 + 3 ^ 40 * 3143704 * 2
def baseEnd_3143704 : Nat := 1076154124974715651561583

theorem tailTrace_3143704 : CollatzResearch.WordTrace tailWord_3143704 prefixEnd_3143704 1076154124974715651561583 := by
  unfold tailWord_3143704
  simp only [CollatzResearch.WordTrace]
  refine ⟨57330152301452392371683083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76440203068603189828910777 57330152301452392371683083)
  ·
    refine ⟨85995228452178588557524625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57330152301452392371683083 85995228452178588557524625)
    ·
      refine ⟨64496421339133941418143469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85995228452178588557524625 64496421339133941418143469)
      ·
        refine ⟨24186158002175228031803801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64496421339133941418143469 24186158002175228031803801)
        ·
          refine ⟨18139618501631421023852851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24186158002175228031803801 18139618501631421023852851)
          ·
            refine ⟨27209427752447131535779277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18139618501631421023852851 27209427752447131535779277)
            ·
              refine ⟨10203535407167674325917229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27209427752447131535779277 10203535407167674325917229)
              ·
                refine ⟨3826325777687877872218961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10203535407167674325917229 3826325777687877872218961)
                ·
                  refine ⟨2869744333265908404164221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826325777687877872218961 2869744333265908404164221)
                  ·
                    refine ⟨1076154124974715651561583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869744333265908404164221 1076154124974715651561583)
                    ·
                      rfl

theorem cell22_3143704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_3143704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143704 prefixEnd_3143704 := by exact prefixLift 3143704
  have htrace : WordTrace (prefixWord ++ tailWord_3143704) baseStart_3143704 baseEnd_3143704 := by
    simpa [prefixWord, tailWord_3143704, baseEnd_3143704] using wordTrace_append hprefix tailTrace_3143704
  have hstable : (prefixWord ++ tailWord_3143704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143704).length < 2 ^ (prefixWord ++ tailWord_3143704).sum := by decide
  have hdescent : baseEnd_3143704 < baseStart_3143704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143826 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3143826 : Nat := 118140960795 + 3143826 * 2 ^ 59
def prefixEnd_3143826 : Nat := 4983230072969 + 3 ^ 40 * 3143826 * 2
def baseEnd_3143826 : Nat := 1076195888067948000011209

theorem tailTrace_3143826 : CollatzResearch.WordTrace tailWord_3143826 prefixEnd_3143826 1076195888067948000011209 := by
  unfold tailWord_3143826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28666188577115699894826833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76443169538975199719538221 28666188577115699894826833)
  ·
    refine ⟨21499641432836774921120125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28666188577115699894826833 21499641432836774921120125)
    ·
      refine ⟨8062365537313790595420047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21499641432836774921120125 8062365537313790595420047)
      ·
        refine ⟨12093548305970685893130071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8062365537313790595420047 12093548305970685893130071)
        ·
          refine ⟨18140322458956028839695107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12093548305970685893130071 18140322458956028839695107)
          ·
            refine ⟨27210483688434043259542661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18140322458956028839695107 27210483688434043259542661)
            ·
              refine ⟨5101965691581383111164249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27210483688434043259542661 5101965691581383111164249)
              ·
                refine ⟨3826474268686037333373187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5101965691581383111164249 3826474268686037333373187)
                ·
                  refine ⟨5739711403029056000059781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826474268686037333373187 5739711403029056000059781)
                  ·
                    refine ⟨1076195888067948000011209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739711403029056000059781 1076195888067948000011209)
                    ·
                      rfl

theorem cell22_3143826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3143826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143826 prefixEnd_3143826 := by exact prefixLift 3143826
  have htrace : WordTrace (prefixWord ++ tailWord_3143826) baseStart_3143826 baseEnd_3143826 := by
    simpa [prefixWord, tailWord_3143826, baseEnd_3143826] using wordTrace_append hprefix tailTrace_3143826
  have hstable : (prefixWord ++ tailWord_3143826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143826).length < 2 ^ (prefixWord ++ tailWord_3143826).sum := by decide
  have hdescent : baseEnd_3143826 < baseStart_3143826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143841 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 4]
def baseStart_3143841 : Nat := 118140960795 + 3143841 * 2 ^ 59
def prefixEnd_3143841 : Nat := 4983230072969 + 3 ^ 40 * 3143841 * 2
def baseEnd_3143841 : Nat := 358733674291497653628721

theorem tailTrace_3143841 : CollatzResearch.WordTrace tailWord_3143841 prefixEnd_3143841 358733674291497653628721 := by
  unfold tailWord_3143841
  simp only [CollatzResearch.WordTrace]
  refine ⟨114665301403408457141103377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76443534268938971427402251 114665301403408457141103377)
  ·
    refine ⟨85998976052556342855827533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114665301403408457141103377 85998976052556342855827533)
    ·
      refine ⟨32249616019708628570935325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85998976052556342855827533 32249616019708628570935325)
      ·
        refine ⟨12093606007390735714100747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32249616019708628570935325 12093606007390735714100747)
        ·
          refine ⟨18140409011086103571151121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12093606007390735714100747 18140409011086103571151121)
          ·
            refine ⟨13605306758314577678363341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18140409011086103571151121 13605306758314577678363341)
            ·
              refine ⟨5101990034367966629386253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13605306758314577678363341 5101990034367966629386253)
              ·
                refine ⟨1913246262887987486019845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5101990034367966629386253 1913246262887987486019845)
                ·
                  refine ⟨358733674291497653628721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913246262887987486019845 358733674291497653628721)
                  ·
                    rfl

theorem cell22_3143841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_3143841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143841 prefixEnd_3143841 := by exact prefixLift 3143841
  have htrace : WordTrace (prefixWord ++ tailWord_3143841) baseStart_3143841 baseEnd_3143841 := by
    simpa [prefixWord, tailWord_3143841, baseEnd_3143841] using wordTrace_append hprefix tailTrace_3143841
  have hstable : (prefixWord ++ tailWord_3143841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143841).length < 2 ^ (prefixWord ++ tailWord_3143841).sum := by decide
  have hdescent : baseEnd_3143841 < baseStart_3143841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143897 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 9]
def baseStart_3143897 : Nat := 118140960795 + 3143897 * 2 ^ 59
def prefixEnd_3143897 : Nat := 4983230072969 + 3 ^ 40 * 3143897 * 2
def baseEnd_3143897 : Nat := 358740064272975827161997

theorem tailTrace_3143897 : CollatzResearch.WordTrace tailWord_3143897 prefixEnd_3143897 358740064272975827161997 := by
  unfold tailWord_3143897
  simp only [CollatzResearch.WordTrace]
  refine ⟨114667343891205578705141945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76444895927470385803427963 114667343891205578705141945)
  ·
    refine ⟨86000507918404184028856459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114667343891205578705141945 86000507918404184028856459)
    ·
      refine ⟨129000761877606276043284689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86000507918404184028856459 129000761877606276043284689)
      ·
        refine ⟨96750571408204707032463517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129000761877606276043284689 96750571408204707032463517)
        ·
          refine ⟨36281464278076765137173819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96750571408204707032463517 36281464278076765137173819)
          ·
            refine ⟨54422196417115147705760729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36281464278076765137173819 54422196417115147705760729)
            ·
              refine ⟨40816647312836360779320547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54422196417115147705760729 40816647312836360779320547)
              ·
                refine ⟨61224970969254541168980821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40816647312836360779320547 61224970969254541168980821)
                ·
                  refine ⟨358740064272975827161997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61224970969254541168980821 358740064272975827161997)
                  ·
                    rfl

theorem cell22_3143897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_3143897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143897 prefixEnd_3143897 := by exact prefixLift 3143897
  have htrace : WordTrace (prefixWord ++ tailWord_3143897) baseStart_3143897 baseEnd_3143897 := by
    simpa [prefixWord, tailWord_3143897, baseEnd_3143897] using wordTrace_append hprefix tailTrace_3143897
  have hstable : (prefixWord ++ tailWord_3143897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143897).length < 2 ^ (prefixWord ++ tailWord_3143897).sum := by decide
  have hdescent : baseEnd_3143897 < baseStart_3143897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143927 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3143927 : Nat := 118140960795 + 3143927 * 2 ^ 59
def prefixEnd_3143927 : Nat := 4983230072969 + 3 ^ 40 * 3143927 * 2
def baseEnd_3143927 : Nat := 1076230462432017403235899

theorem tailTrace_3143927 : CollatzResearch.WordTrace tailWord_3143927 prefixEnd_3143927 1076230462432017403235899 := by
  unfold tailWord_3143927
  simp only [CollatzResearch.WordTrace]
  refine ⟨114668438081096893828734035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76445625387397929219156023 114668438081096893828734035)
  ·
    refine ⟨172002657121645340743101053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114668438081096893828734035 172002657121645340743101053)
    ·
      refine ⟨64500996420617002778662895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172002657121645340743101053 64500996420617002778662895)
      ·
        refine ⟨96751494630925504167994343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64500996420617002778662895 96751494630925504167994343)
        ·
          refine ⟨145127241946388256251991515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96751494630925504167994343 145127241946388256251991515)
          ·
            refine ⟨217690862919582384377987273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145127241946388256251991515 217690862919582384377987273)
            ·
              refine ⟨163268147189686788283490455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217690862919582384377987273 163268147189686788283490455)
              ·
                refine ⟨244902220784530182425235683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163268147189686788283490455 244902220784530182425235683)
                ·
                  refine ⟨367353331176795273637853525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244902220784530182425235683 367353331176795273637853525)
                  ·
                    refine ⟨1076230462432017403235899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 367353331176795273637853525 1076230462432017403235899)
                    ·
                      rfl

theorem cell22_3143927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3143927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143927 prefixEnd_3143927 := by exact prefixLift 3143927
  have htrace : WordTrace (prefixWord ++ tailWord_3143927) baseStart_3143927 baseEnd_3143927 := by
    simpa [prefixWord, tailWord_3143927, baseEnd_3143927] using wordTrace_append hprefix tailTrace_3143927
  have hstable : (prefixWord ++ tailWord_3143927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143927).length < 2 ^ (prefixWord ++ tailWord_3143927).sum := by decide
  have hdescent : baseEnd_3143927 < baseStart_3143927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143965 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 5]
def baseStart_3143965 : Nat := 118140960795 + 3143965 * 2 ^ 59
def prefixEnd_3143965 : Nat := 4983230072969 + 3 ^ 40 * 3143965 * 2
def baseEnd_3143965 : Nat := 358747823536199323595261

theorem tailTrace_3143965 : CollatzResearch.WordTrace tailWord_3143965 prefixEnd_3143965 358747823536199323595261 := by
  unfold tailWord_3143965
  simp only [CollatzResearch.WordTrace]
  refine ⟨114669824054959226318617349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76446549369972817545744899 114669824054959226318617349)
  ·
    refine ⟨21500592010304854934740753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114669824054959226318617349 21500592010304854934740753)
    ·
      refine ⟨16125444007728641201055565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21500592010304854934740753 16125444007728641201055565)
      ·
        refine ⟨6047041502898240450395837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16125444007728641201055565 6047041502898240450395837)
        ·
          refine ⟨2267640563586840168898439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6047041502898240450395837 2267640563586840168898439)
          ·
            refine ⟨3401460845380260253347659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267640563586840168898439 3401460845380260253347659)
            ·
              refine ⟨5102191268070390380021489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401460845380260253347659 5102191268070390380021489)
              ·
                refine ⟨3826643451052792785016117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5102191268070390380021489 3826643451052792785016117)
                ·
                  refine ⟨358747823536199323595261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3826643451052792785016117 358747823536199323595261)
                  ·
                    rfl

theorem cell22_3143965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_3143965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143965 prefixEnd_3143965 := by exact prefixLift 3143965
  have htrace : WordTrace (prefixWord ++ tailWord_3143965) baseStart_3143965 baseEnd_3143965 := by
    simpa [prefixWord, tailWord_3143965, baseEnd_3143965] using wordTrace_append hprefix tailTrace_3143965
  have hstable : (prefixWord ++ tailWord_3143965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143965).length < 2 ^ (prefixWord ++ tailWord_3143965).sum := by decide
  have hdescent : baseEnd_3143965 < baseStart_3143965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143989 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3143989 : Nat := 118140960795 + 3143989 * 2 ^ 59
def prefixEnd_3143989 : Nat := 4983230072969 + 3 ^ 40 * 3143989 * 2
def baseEnd_3143989 : Nat := 1076251686299069908185709

theorem tailTrace_3143989 : CollatzResearch.WordTrace tailWord_3143989 prefixEnd_3143989 1076251686299069908185709 := by
  unfold tailWord_3143989
  simp only [CollatzResearch.WordTrace]
  refine ⟨114670699406872278417491021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76447132937914852278327347 114670699406872278417491021)
  ·
    refine ⟨43001512277577104406559133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114670699406872278417491021 43001512277577104406559133)
    ·
      refine ⟨16125567104091414152459675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43001512277577104406559133 16125567104091414152459675)
      ·
        refine ⟨24188350656137121228689513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125567104091414152459675 24188350656137121228689513)
        ·
          refine ⟨18141262992102840921517135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24188350656137121228689513 18141262992102840921517135)
          ·
            refine ⟨27211894488154261382275703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18141262992102840921517135 27211894488154261382275703)
            ·
              refine ⟨40817841732231392073413555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27211894488154261382275703 40817841732231392073413555)
              ·
                refine ⟨61226762598347088110120333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40817841732231392073413555 61226762598347088110120333)
                ·
                  refine ⟨22960035974380158041295125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61226762598347088110120333 22960035974380158041295125)
                  ·
                    refine ⟨1076251686299069908185709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22960035974380158041295125 1076251686299069908185709)
                    ·
                      rfl

theorem cell22_3143989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3143989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143989 prefixEnd_3143989 := by exact prefixLift 3143989
  have htrace : WordTrace (prefixWord ++ tailWord_3143989) baseStart_3143989 baseEnd_3143989 := by
    simpa [prefixWord, tailWord_3143989, baseEnd_3143989] using wordTrace_append hprefix tailTrace_3143989
  have hstable : (prefixWord ++ tailWord_3143989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143989).length < 2 ^ (prefixWord ++ tailWord_3143989).sum := by decide
  have hdescent : baseEnd_3143989 < baseStart_3143989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3143991 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 2, 3]
def baseStart_3143991 : Nat := 118140960795 + 3143991 * 2 ^ 59
def prefixEnd_3143991 : Nat := 4983230072969 + 3 ^ 40 * 3143991 * 2
def baseEnd_3143991 : Nat := 1076252370939942569635703

theorem tailTrace_3143991 : CollatzResearch.WordTrace tailWord_3143991 prefixEnd_3143991 1076252370939942569635703 := by
  unfold tailWord_3143991
  simp only [CollatzResearch.WordTrace]
  refine ⟨114670772352865032759063827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76447181568576688506042551 114670772352865032759063827)
  ·
    refine ⟨172006158529297549138595741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114670772352865032759063827 172006158529297549138595741)
    ·
      refine ⟨64502309448486580926973403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172006158529297549138595741 64502309448486580926973403)
      ·
        refine ⟨96753464172729871390460105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64502309448486580926973403 96753464172729871390460105)
        ·
          refine ⟨72565098129547403542845079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96753464172729871390460105 72565098129547403542845079)
          ·
            refine ⟨108847647194321105314267619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72565098129547403542845079 108847647194321105314267619)
            ·
              refine ⟨163271470791481657971401429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108847647194321105314267619 163271470791481657971401429)
              ·
                refine ⟨3826675096675351358704721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 163271470791481657971401429 3826675096675351358704721)
                ·
                  refine ⟨2870006322506513519028541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826675096675351358704721 2870006322506513519028541)
                  ·
                    refine ⟨1076252370939942569635703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870006322506513519028541 1076252370939942569635703)
                    ·
                      rfl

theorem cell22_3143991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_3143991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3143991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3143991 prefixEnd_3143991 := by exact prefixLift 3143991
  have htrace : WordTrace (prefixWord ++ tailWord_3143991) baseStart_3143991 baseEnd_3143991 := by
    simpa [prefixWord, tailWord_3143991, baseEnd_3143991] using wordTrace_append hprefix tailTrace_3143991
  have hstable : (prefixWord ++ tailWord_3143991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3143991).length < 2 ^ (prefixWord ++ tailWord_3143991).sum := by decide
  have hdescent : baseEnd_3143991 < baseStart_3143991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3143991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144021 : List Nat := [1, 3, 2, 2, 4, 2, 8]
def baseStart_3144021 : Nat := 118140960795 + 3144021 * 2 ^ 59
def prefixEnd_3144021 : Nat := 4983230072969 + 3 ^ 40 * 3144021 * 2
def baseEnd_3144021 : Nat := 39861579279741944125393

theorem tailTrace_3144021 : CollatzResearch.WordTrace tailWord_3144021 prefixEnd_3144021 39861579279741944125393 := by
  unfold tailWord_3144021
  simp only [CollatzResearch.WordTrace]
  refine ⟨114671866542756347882655917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76447911028504231921770611 114671866542756347882655917)
  ·
    refine ⟨43001949953533630455995969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114671866542756347882655917 43001949953533630455995969)
    ·
      refine ⟨32251462465150222841996977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43001949953533630455995969 32251462465150222841996977)
      ·
        refine ⟨24188596848862667131497733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32251462465150222841996977 24188596848862667131497733)
        ·
          refine ⟨4535361909161750087155825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24188596848862667131497733 4535361909161750087155825)
          ·
            refine ⟨3401521431871312565366869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4535361909161750087155825 3401521431871312565366869)
            ·
              refine ⟨39861579279741944125393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3401521431871312565366869 39861579279741944125393)
              ·
                rfl

theorem cell22_3144021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 8].length) (baseStart_3144021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144021 prefixEnd_3144021 := by exact prefixLift 3144021
  have htrace : WordTrace (prefixWord ++ tailWord_3144021) baseStart_3144021 baseEnd_3144021 := by
    simpa [prefixWord, tailWord_3144021, baseEnd_3144021] using wordTrace_append hprefix tailTrace_3144021
  have hstable : (prefixWord ++ tailWord_3144021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144021).length < 2 ^ (prefixWord ++ tailWord_3144021).sum := by decide
  have hdescent : baseEnd_3144021 < baseStart_3144021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144042 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_3144042 : Nat := 118140960795 + 3144042 * 2 ^ 59
def prefixEnd_3144042 : Nat := 4983230072969 + 3 ^ 40 * 3144042 * 2
def baseEnd_3144042 : Nat := 1076269829282195436610547

theorem tailTrace_3144042 : CollatzResearch.WordTrace tailWord_3144042 prefixEnd_3144042 1076269829282195436610547 := by
  unfold tailWord_3144042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28668158118920067117292595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76448421650453512312780253 28668158118920067117292595)
  ·
    refine ⟨43002237178380100675938893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28668158118920067117292595 43002237178380100675938893)
    ·
      refine ⟨16125838941892537753477085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43002237178380100675938893 16125838941892537753477085)
      ·
        refine ⟨6047189603209701657553907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16125838941892537753477085 6047189603209701657553907)
        ·
          refine ⟨9070784404814552486330861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047189603209701657553907 9070784404814552486330861)
          ·
            refine ⟨3401544151805457182374073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9070784404814552486330861 3401544151805457182374073)
            ·
              refine ⟨2551158113854092886780555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3401544151805457182374073 2551158113854092886780555)
              ·
                refine ⟨3826737170781139330170833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551158113854092886780555 3826737170781139330170833)
                ·
                  refine ⟨2870052878085854497628125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826737170781139330170833 2870052878085854497628125)
                  ·
                    refine ⟨1076269829282195436610547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870052878085854497628125 1076269829282195436610547)
                    ·
                      rfl

theorem cell22_3144042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_3144042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144042 prefixEnd_3144042 := by exact prefixLift 3144042
  have htrace : WordTrace (prefixWord ++ tailWord_3144042) baseStart_3144042 baseEnd_3144042 := by
    simpa [prefixWord, tailWord_3144042, baseEnd_3144042] using wordTrace_append hprefix tailTrace_3144042
  have hstable : (prefixWord ++ tailWord_3144042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144042).length < 2 ^ (prefixWord ++ tailWord_3144042).sum := by decide
  have hdescent : baseEnd_3144042 < baseStart_3144042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144064 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_3144064 : Nat := 118140960795 + 3144064 * 2 ^ 59
def prefixEnd_3144064 : Nat := 4983230072969 + 3 ^ 40 * 3144064 * 2
def baseEnd_3144064 : Nat := 1076277360331794712560479

theorem tailTrace_3144064 : CollatzResearch.WordTrace tailWord_3144064 prefixEnd_3144064 1076277360331794712560479 := by
  unfold tailWord_3144064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57336717440800283113235623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76448956587733710817647497 57336717440800283113235623)
  ·
    refine ⟨86005076161200424669853435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57336717440800283113235623 86005076161200424669853435)
    ·
      refine ⟨129007614241800637004780153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86005076161200424669853435 129007614241800637004780153)
      ·
        refine ⟨96755710681350477753585115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129007614241800637004780153 96755710681350477753585115)
        ·
          refine ⟨145133566022025716630377673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96755710681350477753585115 145133566022025716630377673)
          ·
            refine ⟨108850174516519287472783255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145133566022025716630377673 108850174516519287472783255)
            ·
              refine ⟨163275261774778931209174883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108850174516519287472783255 163275261774778931209174883)
              ·
                refine ⟨244912892662168396813762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163275261774778931209174883 244912892662168396813762325)
                ·
                  refine ⟨11480291843539143600645109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244912892662168396813762325 11480291843539143600645109)
                  ·
                    refine ⟨1076277360331794712560479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11480291843539143600645109 1076277360331794712560479)
                    ·
                      rfl

theorem cell22_3144064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_3144064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144064 prefixEnd_3144064 := by exact prefixLift 3144064
  have htrace : WordTrace (prefixWord ++ tailWord_3144064) baseStart_3144064 baseEnd_3144064 := by
    simpa [prefixWord, tailWord_3144064, baseEnd_3144064] using wordTrace_append hprefix tailTrace_3144064
  have hstable : (prefixWord ++ tailWord_3144064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144064).length < 2 ^ (prefixWord ++ tailWord_3144064).sum := by decide
  have hdescent : baseEnd_3144064 < baseStart_3144064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144096 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_3144096 : Nat := 118140960795 + 3144096 * 2 ^ 59
def prefixEnd_3144096 : Nat := 4983230072969 + 3 ^ 40 * 3144096 * 2
def baseEnd_3144096 : Nat := 1076288314585757295760381

theorem tailTrace_3144096 : CollatzResearch.WordTrace tailWord_3144096 prefixEnd_3144096 1076288314585757295760381 := by
  unfold tailWord_3144096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57337301008742317845818071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76449734678323090461090761 57337301008742317845818071)
  ·
    refine ⟨86005951513113476768727107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57337301008742317845818071 86005951513113476768727107)
    ·
      refine ⟨129008927269670215153090661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86005951513113476768727107 129008927269670215153090661)
      ·
        refine ⟨24189173863063165341204499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129008927269670215153090661 24189173863063165341204499)
        ·
          refine ⟨36283760794594748011806749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24189173863063165341204499 36283760794594748011806749)
          ·
            refine ⟨13606410297973030504427531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36283760794594748011806749 13606410297973030504427531)
            ·
              refine ⟨20409615446959545756641297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13606410297973030504427531 20409615446959545756641297)
              ·
                refine ⟨15307211585219659317480973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20409615446959545756641297 15307211585219659317480973)
                ·
                  refine ⟨5740204344457372244055365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15307211585219659317480973 5740204344457372244055365)
                  ·
                    refine ⟨1076288314585757295760381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5740204344457372244055365 1076288314585757295760381)
                    ·
                      rfl

theorem cell22_3144096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_3144096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144096 prefixEnd_3144096 := by exact prefixLift 3144096
  have htrace : WordTrace (prefixWord ++ tailWord_3144096) baseStart_3144096 baseEnd_3144096 := by
    simpa [prefixWord, tailWord_3144096, baseEnd_3144096] using wordTrace_append hprefix tailTrace_3144096
  have hstable : (prefixWord ++ tailWord_3144096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144096).length < 2 ^ (prefixWord ++ tailWord_3144096).sum := by decide
  have hdescent : baseEnd_3144096 < baseStart_3144096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144160 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 2, 3]
def baseStart_3144160 : Nat := 118140960795 + 3144160 * 2 ^ 59
def prefixEnd_3144160 : Nat := 4983230072969 + 3 ^ 40 * 3144160 * 2
def baseEnd_3144160 : Nat := 1076310223093682462160185

theorem tailTrace_3144160 : CollatzResearch.WordTrace tailWord_3144160 prefixEnd_3144160 1076310223093682462160185 := by
  unfold tailWord_3144160
  simp only [CollatzResearch.WordTrace]
  refine ⟨57338468144626387310982967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76451290859501849747977289 57338468144626387310982967)
  ·
    refine ⟨86007702216939580966474451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57338468144626387310982967 86007702216939580966474451)
    ·
      refine ⟨129011553325409371449711677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86007702216939580966474451 129011553325409371449711677)
      ·
        refine ⟨48379332497028514293641879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129011553325409371449711677 48379332497028514293641879)
        ·
          refine ⟨72568998745542771440462819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48379332497028514293641879 72568998745542771440462819)
          ·
            refine ⟨108853498118314157160694229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72568998745542771440462819 108853498118314157160694229)
            ·
              refine ⟨2551253862147988058453771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 108853498118314157160694229 2551253862147988058453771)
              ·
                refine ⟨3826880793221982087680657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551253862147988058453771 3826880793221982087680657)
                ·
                  refine ⟨2870160594916486565760493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826880793221982087680657 2870160594916486565760493)
                  ·
                    refine ⟨1076310223093682462160185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870160594916486565760493 1076310223093682462160185)
                    ·
                      rfl

theorem cell22_3144160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_3144160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144160 prefixEnd_3144160 := by exact prefixLift 3144160
  have htrace : WordTrace (prefixWord ++ tailWord_3144160) baseStart_3144160 baseEnd_3144160 := by
    simpa [prefixWord, tailWord_3144160, baseEnd_3144160] using wordTrace_append hprefix tailTrace_3144160
  have hstable : (prefixWord ++ tailWord_3144160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144160).length < 2 ^ (prefixWord ++ tailWord_3144160).sum := by decide
  have hdescent : baseEnd_3144160 < baseStart_3144160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144173 : List Nat := [1, 5, 1, 3, 1, 2, 1, 8]
def baseStart_3144173 : Nat := 118140960795 + 3144173 * 2 ^ 59
def prefixEnd_3144173 : Nat := 4983230072969 + 3 ^ 40 * 3144173 * 2
def baseEnd_3144173 : Nat := 119590519251039417953905

theorem tailTrace_3144173 : CollatzResearch.WordTrace tailWord_3144173 prefixEnd_3144173 119590519251039417953905 := by
  unfold tailWord_3144173
  simp only [CollatzResearch.WordTrace]
  refine ⟨114677410438205677842189173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76451606958803785228126115 114677410438205677842189173)
  ·
    refine ⟨10751007228581782297705235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114677410438205677842189173 10751007228581782297705235)
    ·
      refine ⟨16126510842872673446557853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10751007228581782297705235 16126510842872673446557853)
      ·
        refine ⟨6047441566077252542459195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16126510842872673446557853 6047441566077252542459195)
        ·
          refine ⟨9071162349115878813688793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047441566077252542459195 9071162349115878813688793)
          ·
            refine ⟨6803371761836909110266595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9071162349115878813688793 6803371761836909110266595)
            ·
              refine ⟨10205057642755363665399893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803371761836909110266595 10205057642755363665399893)
              ·
                refine ⟨119590519251039417953905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10205057642755363665399893 119590519251039417953905)
                ·
                  rfl

theorem cell22_3144173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 8].length) (baseStart_3144173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144173 prefixEnd_3144173 := by exact prefixLift 3144173
  have htrace : WordTrace (prefixWord ++ tailWord_3144173) baseStart_3144173 baseEnd_3144173 := by
    simpa [prefixWord, tailWord_3144173, baseEnd_3144173] using wordTrace_append hprefix tailTrace_3144173
  have hstable : (prefixWord ++ tailWord_3144173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144173).length < 2 ^ (prefixWord ++ tailWord_3144173).sum := by decide
  have hdescent : baseEnd_3144173 < baseStart_3144173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144428 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_3144428 : Nat := 118140960795 + 3144428 * 2 ^ 59
def prefixEnd_3144428 : Nat := 4983230072969 + 3 ^ 40 * 3144428 * 2
def baseEnd_3144428 : Nat := 1076401964970619096459363

theorem tailTrace_3144428 : CollatzResearch.WordTrace tailWord_3144428 prefixEnd_3144428 1076401964970619096459363 := by
  unfold tailWord_3144428
  simp only [CollatzResearch.WordTrace]
  refine ⟨57343355526140928196360969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76457807368187904261814625 57343355526140928196360969)
  ·
    refine ⟨43007516644605696147270727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57343355526140928196360969 43007516644605696147270727)
    ·
      refine ⟨64511274966908544220906091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43007516644605696147270727 64511274966908544220906091)
      ·
        refine ⟨96766912450362816331359137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64511274966908544220906091 96766912450362816331359137)
        ·
          refine ⟨72575184337772112248519353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96766912450362816331359137 72575184337772112248519353)
          ·
            refine ⟨54431388253329084186389515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72575184337772112248519353 54431388253329084186389515)
            ·
              refine ⟨81647082379993626279584273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54431388253329084186389515 81647082379993626279584273)
              ·
                refine ⟨61235311784995219709688205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81647082379993626279584273 61235311784995219709688205)
                ·
                  refine ⟨22963241919373207391133077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61235311784995219709688205 22963241919373207391133077)
                  ·
                    refine ⟨1076401964970619096459363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22963241919373207391133077 1076401964970619096459363)
                    ·
                      rfl

theorem cell22_3144428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_3144428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144428 prefixEnd_3144428 := by exact prefixLift 3144428
  have htrace : WordTrace (prefixWord ++ tailWord_3144428) baseStart_3144428 baseEnd_3144428 := by
    simpa [prefixWord, tailWord_3144428, baseEnd_3144428] using wordTrace_append hprefix tailTrace_3144428
  have hstable : (prefixWord ++ tailWord_3144428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144428).length < 2 ^ (prefixWord ++ tailWord_3144428).sum := by decide
  have hdescent : baseEnd_3144428 < baseStart_3144428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144466 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3144466 : Nat := 118140960795 + 3144466 * 2 ^ 59
def prefixEnd_3144466 : Nat := 4983230072969 + 3 ^ 40 * 3144466 * 2
def baseEnd_3144466 : Nat := 358804991049066554669749

theorem tailTrace_3144466 : CollatzResearch.WordTrace tailWord_3144466 prefixEnd_3144466 358804991049066554669749 := by
  unfold tailWord_3144466
  simp only [CollatzResearch.WordTrace]
  refine ⟨28672024256536047220651313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76458731350762792588403501 28672024256536047220651313)
  ·
    refine ⟨21504018192402035415488485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28672024256536047220651313 21504018192402035415488485)
    ·
      refine ⟨4032003411075381640404091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21504018192402035415488485 4032003411075381640404091)
      ·
        refine ⟨6048005116613072460606137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032003411075381640404091 6048005116613072460606137)
        ·
          refine ⟨4536003837459804345454603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6048005116613072460606137 4536003837459804345454603)
          ·
            refine ⟨6804005756189706518181905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536003837459804345454603 6804005756189706518181905)
            ·
              refine ⟨5103004317142279888636429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6804005756189706518181905 5103004317142279888636429)
              ·
                refine ⟨1913626618928354958238661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5103004317142279888636429 1913626618928354958238661)
                ·
                  refine ⟨358804991049066554669749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913626618928354958238661 358804991049066554669749)
                  ·
                    rfl

theorem cell22_3144466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3144466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144466 prefixEnd_3144466 := by exact prefixLift 3144466
  have htrace : WordTrace (prefixWord ++ tailWord_3144466) baseStart_3144466 baseEnd_3144466 := by
    simpa [prefixWord, tailWord_3144466, baseEnd_3144466] using wordTrace_append hprefix tailTrace_3144466
  have hstable : (prefixWord ++ tailWord_3144466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144466).length < 2 ^ (prefixWord ++ tailWord_3144466).sum := by decide
  have hdescent : baseEnd_3144466 < baseStart_3144466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144473 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_3144473 : Nat := 118140960795 + 3144473 * 2 ^ 59
def prefixEnd_3144473 : Nat := 4983230072969 + 3 ^ 40 * 3144473 * 2
def baseEnd_3144473 : Nat := 1076417369390253979084225

theorem tailTrace_3144473 : CollatzResearch.WordTrace tailWord_3144473 prefixEnd_3144473 1076417369390253979084225 := by
  unfold tailWord_3144473
  simp only [CollatzResearch.WordTrace]
  refine ⟨114688352337118829078110073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76458901558079219385406715 114688352337118829078110073)
  ·
    refine ⟨86016264252839121808582555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114688352337118829078110073 86016264252839121808582555)
    ·
      refine ⟨129024396379258682712873833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86016264252839121808582555 129024396379258682712873833)
      ·
        refine ⟨96768297284444012034655375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129024396379258682712873833 96768297284444012034655375)
        ·
          refine ⟨145152445926666018051983063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96768297284444012034655375 145152445926666018051983063)
          ·
            refine ⟨217728668889999027077974595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145152445926666018051983063 217728668889999027077974595)
            ·
              refine ⟨326593003334998540616961893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217728668889999027077974595 326593003334998540616961893)
              ·
                refine ⟨61236188125312226365680355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326593003334998540616961893 61236188125312226365680355)
                ·
                  refine ⟨91854282187968339548520533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61236188125312226365680355 91854282187968339548520533)
                  ·
                    refine ⟨1076417369390253979084225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91854282187968339548520533 1076417369390253979084225)
                    ·
                      rfl

theorem cell22_3144473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_3144473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144473 prefixEnd_3144473 := by exact prefixLift 3144473
  have htrace : WordTrace (prefixWord ++ tailWord_3144473) baseStart_3144473 baseEnd_3144473 := by
    simpa [prefixWord, tailWord_3144473, baseEnd_3144473] using wordTrace_append hprefix tailTrace_3144473
  have hstable : (prefixWord ++ tailWord_3144473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144473).length < 2 ^ (prefixWord ++ tailWord_3144473).sum := by decide
  have hdescent : baseEnd_3144473 < baseStart_3144473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144477 : List Nat := [1, 4, 2, 4, 1, 1, 9]
def baseStart_3144477 : Nat := 118140960795 + 3144477 * 2 ^ 59
def prefixEnd_3144477 : Nat := 4983230072969 + 3 ^ 40 * 3144477 * 2
def baseEnd_3144477 : Nat := 39867360691555529703119

theorem tailTrace_3144477 : CollatzResearch.WordTrace tailWord_3144477 prefixEnd_3144477 39867360691555529703119 := by
  unfold tailWord_3144477
  simp only [CollatzResearch.WordTrace]
  refine ⟨114688498229104337761255685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76458998819402891840837123 114688498229104337761255685)
  ·
    refine ⟨21504093417957063330235441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114688498229104337761255685 21504093417957063330235441)
    ·
      refine ⟨16128070063467797497676581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21504093417957063330235441 16128070063467797497676581)
      ·
        refine ⟨3024013136900212030814359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16128070063467797497676581 3024013136900212030814359)
        ·
          refine ⟨4536019705350318046221539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024013136900212030814359 4536019705350318046221539)
          ·
            refine ⟨6804029558025477069332309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536019705350318046221539 6804029558025477069332309)
            ·
              refine ⟨39867360691555529703119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6804029558025477069332309 39867360691555529703119)
              ·
                rfl

theorem cell22_3144477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 9].length) (baseStart_3144477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144477 prefixEnd_3144477 := by exact prefixLift 3144477
  have htrace : WordTrace (prefixWord ++ tailWord_3144477) baseStart_3144477 baseEnd_3144477 := by
    simpa [prefixWord, tailWord_3144477, baseEnd_3144477] using wordTrace_append hprefix tailTrace_3144477
  have hstable : (prefixWord ++ tailWord_3144477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144477).length < 2 ^ (prefixWord ++ tailWord_3144477).sum := by decide
  have hdescent : baseEnd_3144477 < baseStart_3144477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144492 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_3144492 : Nat := 118140960795 + 3144492 * 2 ^ 59
def prefixEnd_3144492 : Nat := 4983230072969 + 3 ^ 40 * 3144492 * 2
def baseEnd_3144492 : Nat := 1076423873478544262859167

theorem tailTrace_3144492 : CollatzResearch.WordTrace tailWord_3144492 prefixEnd_3144492 1076423873478544262859167 := by
  unfold tailWord_3144492
  simp only [CollatzResearch.WordTrace]
  refine ⟨57344522662024997661525865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76459363549366663548701153 57344522662024997661525865)
  ·
    refine ⟨43008391996518748246144399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57344522662024997661525865 43008391996518748246144399)
    ·
      refine ⟨64512587994778122369216599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43008391996518748246144399 64512587994778122369216599)
      ·
        refine ⟨96768881992167183553824899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64512587994778122369216599 96768881992167183553824899)
        ·
          refine ⟨145153322988250775330737349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96768881992167183553824899 145153322988250775330737349)
          ·
            refine ⟨27216248060297020374513253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145153322988250775330737349 27216248060297020374513253)
            ·
              refine ⟨5103046511305691320221235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27216248060297020374513253 5103046511305691320221235)
              ·
                refine ⟨7654569766958536980331853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103046511305691320221235 7654569766958536980331853)
                ·
                  refine ⟨2870463662609451367624445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7654569766958536980331853 2870463662609451367624445)
                  ·
                    refine ⟨1076423873478544262859167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870463662609451367624445 1076423873478544262859167)
                    ·
                      rfl

theorem cell22_3144492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_3144492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144492 prefixEnd_3144492 := by exact prefixLift 3144492
  have htrace : WordTrace (prefixWord ++ tailWord_3144492) baseStart_3144492 baseEnd_3144492 := by
    simpa [prefixWord, tailWord_3144492, baseEnd_3144492] using wordTrace_append hprefix tailTrace_3144492
  have hstable : (prefixWord ++ tailWord_3144492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144492).length < 2 ^ (prefixWord ++ tailWord_3144492).sum := by decide
  have hdescent : baseEnd_3144492 < baseStart_3144492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144569 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_3144569 : Nat := 118140960795 + 3144569 * 2 ^ 59
def prefixEnd_3144569 : Nat := 4983230072969 + 3 ^ 40 * 3144569 * 2
def baseEnd_3144569 : Nat := 1076450232152141728683931

theorem tailTrace_3144569 : CollatzResearch.WordTrace tailWord_3144569 prefixEnd_3144569 1076450232152141728683931 := by
  unfold tailWord_3144569
  simp only [CollatzResearch.WordTrace]
  refine ⟨114691853744771037473604761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76461235829847358315736507 114691853744771037473604761)
  ·
    refine ⟨86018890308578278105203571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114691853744771037473604761 86018890308578278105203571)
    ·
      refine ⟨129028335462867417157805357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86018890308578278105203571 129028335462867417157805357)
      ·
        refine ⟨48385625798575281434177009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129028335462867417157805357 48385625798575281434177009)
        ·
          refine ⟨36289219348931461075632757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48385625798575281434177009 36289219348931461075632757)
          ·
            refine ⟨3402114313962324475840571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36289219348931461075632757 3402114313962324475840571)
            ·
              refine ⟨5103171470943486713760857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402114313962324475840571 5103171470943486713760857)
              ·
                refine ⟨3827378603207615035320643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5103171470943486713760857 3827378603207615035320643)
                ·
                  refine ⟨5741067904811422552980965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827378603207615035320643 5741067904811422552980965)
                  ·
                    refine ⟨1076450232152141728683931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741067904811422552980965 1076450232152141728683931)
                    ·
                      rfl

theorem cell22_3144569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_3144569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144569 prefixEnd_3144569 := by exact prefixLift 3144569
  have htrace : WordTrace (prefixWord ++ tailWord_3144569) baseStart_3144569 baseEnd_3144569 := by
    simpa [prefixWord, tailWord_3144569, baseEnd_3144569] using wordTrace_append hprefix tailTrace_3144569
  have hstable : (prefixWord ++ tailWord_3144569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144569).length < 2 ^ (prefixWord ++ tailWord_3144569).sum := by decide
  have hdescent : baseEnd_3144569 < baseStart_3144569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144586 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_3144586 : Nat := 118140960795 + 3144586 * 2 ^ 59
def prefixEnd_3144586 : Nat := 4983230072969 + 3 ^ 40 * 3144586 * 2
def baseEnd_3144586 : Nat := 1076456051599559351008879

theorem tailTrace_3144586 : CollatzResearch.WordTrace tailWord_3144586 prefixEnd_3144586 1076456051599559351008879 := by
  unfold tailWord_3144586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28673118446427362344243403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76461649190472966251315741 28673118446427362344243403)
  ·
    refine ⟨43009677669641043516365105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28673118446427362344243403 43009677669641043516365105)
    ·
      refine ⟨32257258252230782637273829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43009677669641043516365105 32257258252230782637273829)
      ·
        refine ⟨6048235922293271744488843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32257258252230782637273829 6048235922293271744488843)
        ·
          refine ⟨9072353883439907616733265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048235922293271744488843 9072353883439907616733265)
          ·
            refine ⟨6804265412579930712549949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9072353883439907616733265 6804265412579930712549949)
            ·
              refine ⟨2551599529717474017206231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6804265412579930712549949 2551599529717474017206231)
              ·
                refine ⟨3827399294576211025809347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551599529717474017206231 3827399294576211025809347)
                ·
                  refine ⟨5741098941864316538714021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827399294576211025809347 5741098941864316538714021)
                  ·
                    refine ⟨1076456051599559351008879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741098941864316538714021 1076456051599559351008879)
                    ·
                      rfl

theorem cell22_3144586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_3144586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144586 prefixEnd_3144586 := by exact prefixLift 3144586
  have htrace : WordTrace (prefixWord ++ tailWord_3144586) baseStart_3144586 baseEnd_3144586 := by
    simpa [prefixWord, tailWord_3144586, baseEnd_3144586] using wordTrace_append hprefix tailTrace_3144586
  have hstable : (prefixWord ++ tailWord_3144586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144586).length < 2 ^ (prefixWord ++ tailWord_3144586).sum := by decide
  have hdescent : baseEnd_3144586 < baseStart_3144586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144597 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3144597 : Nat := 118140960795 + 3144597 * 2 ^ 59
def prefixEnd_3144597 : Nat := 4983230072969 + 3 ^ 40 * 3144597 * 2
def baseEnd_3144597 : Nat := 1076459817124358988983845

theorem tailTrace_3144597 : CollatzResearch.WordTrace tailWord_3144597 prefixEnd_3144597 1076459817124358988983845 := by
  unfold tailWord_3144597
  simp only [CollatzResearch.WordTrace]
  refine ⟨114692874988669598255624045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76461916659113065503749363 114692874988669598255624045)
  ·
    refine ⟨43009828120751099345859017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114692874988669598255624045 43009828120751099345859017)
    ·
      refine ⟨32257371090563324509394263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43009828120751099345859017 32257371090563324509394263)
      ·
        refine ⟨48386056635844986764091395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32257371090563324509394263 48386056635844986764091395)
        ·
          refine ⟨72579084953767480146137093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48386056635844986764091395 72579084953767480146137093)
          ·
            refine ⟨13608578428831402527400705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72579084953767480146137093 13608578428831402527400705)
            ·
              refine ⟨10206433821623551895550529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13608578428831402527400705 10206433821623551895550529)
              ·
                refine ⟨7654825366217663921662897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10206433821623551895550529 7654825366217663921662897)
                ·
                  refine ⟨5741119024663247941247173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7654825366217663921662897 5741119024663247941247173)
                  ·
                    refine ⟨1076459817124358988983845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741119024663247941247173 1076459817124358988983845)
                    ·
                      rfl

theorem cell22_3144597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3144597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144597 prefixEnd_3144597 := by exact prefixLift 3144597
  have htrace : WordTrace (prefixWord ++ tailWord_3144597) baseStart_3144597 baseEnd_3144597 := by
    simpa [prefixWord, tailWord_3144597, baseEnd_3144597] using wordTrace_append hprefix tailTrace_3144597
  have hstable : (prefixWord ++ tailWord_3144597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144597).length < 2 ^ (prefixWord ++ tailWord_3144597).sum := by decide
  have hdescent : baseEnd_3144597 < baseStart_3144597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144599 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 2, 3]
def baseStart_3144599 : Nat := 118140960795 + 3144599 * 2 ^ 59
def prefixEnd_3144599 : Nat := 4983230072969 + 3 ^ 40 * 3144599 * 2
def baseEnd_3144599 : Nat := 1076460501765231650433839

theorem tailTrace_3144599 : CollatzResearch.WordTrace tailWord_3144599 prefixEnd_3144599 1076460501765231650433839 := by
  unfold tailWord_3144599
  simp only [CollatzResearch.WordTrace]
  refine ⟨114692947934662352597196851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76461965289774901731464567 114692947934662352597196851)
  ·
    refine ⟨172039421901993528895795277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114692947934662352597196851 172039421901993528895795277)
    ·
      refine ⟨64514783213247573335923229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172039421901993528895795277 64514783213247573335923229)
      ·
        refine ⟨24193043704967840000971211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64514783213247573335923229 24193043704967840000971211)
        ·
          refine ⟨36289565557451760001456817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24193043704967840000971211 36289565557451760001456817)
          ·
            refine ⟨27217174168088820001092613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36289565557451760001456817 27217174168088820001092613)
            ·
              refine ⟨5103220156516653750204865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27217174168088820001092613 5103220156516653750204865)
              ·
                refine ⟨3827415117387490312653649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5103220156516653750204865 3827415117387490312653649)
                ·
                  refine ⟨2870561338040617734490237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3827415117387490312653649 2870561338040617734490237)
                  ·
                    refine ⟨1076460501765231650433839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870561338040617734490237 1076460501765231650433839)
                    ·
                      rfl

theorem cell22_3144599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_3144599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144599 prefixEnd_3144599 := by exact prefixLift 3144599
  have htrace : WordTrace (prefixWord ++ tailWord_3144599) baseStart_3144599 baseEnd_3144599 := by
    simpa [prefixWord, tailWord_3144599, baseEnd_3144599] using wordTrace_append hprefix tailTrace_3144599
  have hstable : (prefixWord ++ tailWord_3144599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144599).length < 2 ^ (prefixWord ++ tailWord_3144599).sum := by decide
  have hdescent : baseEnd_3144599 < baseStart_3144599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144661 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_3144661 : Nat := 118140960795 + 3144661 * 2 ^ 59
def prefixEnd_3144661 : Nat := 4983230072969 + 3 ^ 40 * 3144661 * 2
def baseEnd_3144661 : Nat := 1076481725632284155383649

theorem tailTrace_3144661 : CollatzResearch.WordTrace tailWord_3144661 prefixEnd_3144661 1076481725632284155383649 := by
  unfold tailWord_3144661
  simp only [CollatzResearch.WordTrace]
  refine ⟨114695209260437737185953837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76463472840291824790635891 114695209260437737185953837)
  ·
    refine ⟨43010703472664151444732689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114695209260437737185953837 43010703472664151444732689)
    ·
      refine ⟨32258027604498113583549517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43010703472664151444732689 32258027604498113583549517)
      ·
        refine ⟨12096760351686792593831069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32258027604498113583549517 12096760351686792593831069)
        ·
          refine ⟨4536285131882547222686651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12096760351686792593831069 4536285131882547222686651)
          ·
            refine ⟨6804427697823820834029977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536285131882547222686651 6804427697823820834029977)
            ·
              refine ⟨5103320773367865625522483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6804427697823820834029977 5103320773367865625522483)
              ·
                refine ⟨7654981160051798438283725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103320773367865625522483 7654981160051798438283725)
                ·
                  refine ⟨2870617935019424414356397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7654981160051798438283725 2870617935019424414356397)
                  ·
                    refine ⟨1076481725632284155383649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870617935019424414356397 1076481725632284155383649)
                    ·
                      rfl

theorem cell22_3144661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_3144661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144661 prefixEnd_3144661 := by exact prefixLift 3144661
  have htrace : WordTrace (prefixWord ++ tailWord_3144661) baseStart_3144661 baseEnd_3144661 := by
    simpa [prefixWord, tailWord_3144661, baseEnd_3144661] using wordTrace_append hprefix tailTrace_3144661
  have hstable : (prefixWord ++ tailWord_3144661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144661).length < 2 ^ (prefixWord ++ tailWord_3144661).sum := by decide
  have hdescent : baseEnd_3144661 < baseStart_3144661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144766 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3144766 : Nat := 118140960795 + 3144766 * 2 ^ 59
def prefixEnd_3144766 : Nat := 4983230072969 + 3 ^ 40 * 3144766 * 2
def baseEnd_3144766 : Nat := 1076517669278098881508327

theorem tailTrace_3144766 : CollatzResearch.WordTrace tailWord_3144766 prefixEnd_3144766 1076517669278098881508327 := by
  unfold tailWord_3144766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337379865632167514815769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76466025950038226745684101 14337379865632167514815769)
  ·
    refine ⟨10753034899224125636111827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14337379865632167514815769 10753034899224125636111827)
    ·
      refine ⟨16129552348836188454167741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10753034899224125636111827 16129552348836188454167741)
      ·
        refine ⟨6048582130813570670312903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16129552348836188454167741 6048582130813570670312903)
        ·
          refine ⟨9072873196220356005469355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048582130813570670312903 9072873196220356005469355)
          ·
            refine ⟨13609309794330534008204033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9072873196220356005469355 13609309794330534008204033)
            ·
              refine ⟨10206982345747900506153025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13609309794330534008204033 10206982345747900506153025)
              ·
                refine ⟨7655236759310925379614769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10206982345747900506153025 7655236759310925379614769)
                ·
                  refine ⟨5741427569483194034711077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655236759310925379614769 5741427569483194034711077)
                  ·
                    refine ⟨1076517669278098881508327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741427569483194034711077 1076517669278098881508327)
                    ·
                      rfl

theorem cell22_3144766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3144766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144766 prefixEnd_3144766 := by exact prefixLift 3144766
  have htrace : WordTrace (prefixWord ++ tailWord_3144766) baseStart_3144766 baseEnd_3144766 := by
    simpa [prefixWord, tailWord_3144766, baseEnd_3144766] using wordTrace_append hprefix tailTrace_3144766
  have hstable : (prefixWord ++ tailWord_3144766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144766).length < 2 ^ (prefixWord ++ tailWord_3144766).sum := by decide
  have hdescent : baseEnd_3144766 < baseStart_3144766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144781 : List Nat := [1, 6, 1, 1, 1, 4, 1, 7]
def baseStart_3144781 : Nat := 118140960795 + 3144781 * 2 ^ 59
def prefixEnd_3144781 : Nat := 4983230072969 + 3 ^ 40 * 3144781 * 2
def baseEnd_3144781 : Nat := 119613644898293760264809

theorem tailTrace_3144781 : CollatzResearch.WordTrace tailWord_3144781 prefixEnd_3144781 119613644898293760264809 := by
  unfold tailWord_3144781
  simp only [CollatzResearch.WordTrace]
  refine ⟨114699586020002997680322197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76466390680001998453548131 114699586020002997680322197)
  ·
    refine ⟨5376543094687640516265103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114699586020002997680322197 5376543094687640516265103)
    ·
      refine ⟨8064814642031460774397655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376543094687640516265103 8064814642031460774397655)
      ·
        refine ⟨12097221963047191161596483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8064814642031460774397655 12097221963047191161596483)
        ·
          refine ⟨18145832944570786742394725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097221963047191161596483 18145832944570786742394725)
          ·
            refine ⟨3402343677107022514199011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18145832944570786742394725 3402343677107022514199011)
            ·
              refine ⟨5103515515660533771298517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402343677107022514199011 5103515515660533771298517)
              ·
                refine ⟨119613644898293760264809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5103515515660533771298517 119613644898293760264809)
                ·
                  rfl

theorem cell22_3144781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 7].length) (baseStart_3144781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144781 prefixEnd_3144781 := by exact prefixLift 3144781
  have htrace : WordTrace (prefixWord ++ tailWord_3144781) baseStart_3144781 baseEnd_3144781 := by
    simpa [prefixWord, tailWord_3144781, baseEnd_3144781] using wordTrace_append hprefix tailTrace_3144781
  have hstable : (prefixWord ++ tailWord_3144781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144781).length < 2 ^ (prefixWord ++ tailWord_3144781).sum := by decide
  have hdescent : baseEnd_3144781 < baseStart_3144781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144796 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3144796 : Nat := 118140960795 + 3144796 * 2 ^ 59
def prefixEnd_3144796 : Nat := 4983230072969 + 3 ^ 40 * 3144796 * 2
def baseEnd_3144796 : Nat := 1076527938891188803258235

theorem tailTrace_3144796 : CollatzResearch.WordTrace tailWord_3144796 prefixEnd_3144796 1076527938891188803258235 := by
  unfold tailWord_3144796
  simp only [CollatzResearch.WordTrace]
  refine ⟨57350066557474327621059121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76466755409965770161412161 57350066557474327621059121)
  ·
    refine ⟨43012549918105745715794341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57350066557474327621059121 43012549918105745715794341)
    ·
      refine ⟨8064853109644827321711439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43012549918105745715794341 8064853109644827321711439)
      ·
        refine ⟨12097279664467240982567159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8064853109644827321711439 12097279664467240982567159)
        ·
          refine ⟨18145919496700861473850739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097279664467240982567159 18145919496700861473850739)
          ·
            refine ⟨27218879245051292210776109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18145919496700861473850739 27218879245051292210776109)
            ·
              refine ⟨10207079716894234579041041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27218879245051292210776109 10207079716894234579041041)
              ·
                refine ⟨7655309787670675934280781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10207079716894234579041041 7655309787670675934280781)
                ·
                  refine ⟨2870741170376503475355293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7655309787670675934280781 2870741170376503475355293)
                  ·
                    refine ⟨1076527938891188803258235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870741170376503475355293 1076527938891188803258235)
                    ·
                      rfl

theorem cell22_3144796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3144796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144796 prefixEnd_3144796 := by exact prefixLift 3144796
  have htrace : WordTrace (prefixWord ++ tailWord_3144796) baseStart_3144796 baseEnd_3144796 := by
    simpa [prefixWord, tailWord_3144796, baseEnd_3144796] using wordTrace_append hprefix tailTrace_3144796
  have hstable : (prefixWord ++ tailWord_3144796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144796).length < 2 ^ (prefixWord ++ tailWord_3144796).sum := by decide
  have hdescent : baseEnd_3144796 < baseStart_3144796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144813 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3144813 : Nat := 118140960795 + 3144813 * 2 ^ 59
def prefixEnd_3144813 : Nat := 4983230072969 + 3 ^ 40 * 3144813 * 2
def baseEnd_3144813 : Nat := 1076533758338606425583183

theorem tailTrace_3144813 : CollatzResearch.WordTrace tailWord_3144813 prefixEnd_3144813 1076533758338606425583183 := by
  unfold tailWord_3144813
  simp only [CollatzResearch.WordTrace]
  refine ⟨114700753155887067145487093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76467168770591378096991395 114700753155887067145487093)
  ·
    refine ⟨10753195608364412544889415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114700753155887067145487093 10753195608364412544889415)
    ·
      refine ⟨16129793412546618817334123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10753195608364412544889415 16129793412546618817334123)
      ·
        refine ⟨24194690118819928226001185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16129793412546618817334123 24194690118819928226001185)
        ·
          refine ⟨18146017589114946169500889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24194690118819928226001185 18146017589114946169500889)
          ·
            refine ⟨13609513191836209627125667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18146017589114946169500889 13609513191836209627125667)
            ·
              refine ⟨20414269787754314440688501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13609513191836209627125667 20414269787754314440688501)
              ·
                refine ⟨1913837792601966978814547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20414269787754314440688501 1913837792601966978814547)
                ·
                  refine ⟨2870756688902950468221821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913837792601966978814547 2870756688902950468221821)
                  ·
                    refine ⟨1076533758338606425583183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870756688902950468221821 1076533758338606425583183)
                    ·
                      rfl

theorem cell22_3144813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3144813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144813 prefixEnd_3144813 := by exact prefixLift 3144813
  have htrace : WordTrace (prefixWord ++ tailWord_3144813) baseStart_3144813 baseEnd_3144813 := by
    simpa [prefixWord, tailWord_3144813, baseEnd_3144813] using wordTrace_append hprefix tailTrace_3144813
  have hstable : (prefixWord ++ tailWord_3144813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144813).length < 2 ^ (prefixWord ++ tailWord_3144813).sum := by decide
  have hdescent : baseEnd_3144813 < baseStart_3144813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144856 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_3144856 : Nat := 118140960795 + 3144856 * 2 ^ 59
def prefixEnd_3144856 : Nat := 4983230072969 + 3 ^ 40 * 3144856 * 2
def baseEnd_3144856 : Nat := 1076548478117368646758051

theorem tailTrace_3144856 : CollatzResearch.WordTrace tailWord_3144856 prefixEnd_3144856 1076548478117368646758051 := by
  unfold tailWord_3144856
  simp only [CollatzResearch.WordTrace]
  refine ⟨57351160747365642744651211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76468214329820856992868281 57351160747365642744651211)
  ·
    refine ⟨86026741121048464116976817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57351160747365642744651211 86026741121048464116976817)
    ·
      refine ⟨64520055840786348087732613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86026741121048464116976817 64520055840786348087732613)
      ·
        refine ⟨12097510470147440266449865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64520055840786348087732613 12097510470147440266449865)
        ·
          refine ⟨9073132852610580199837399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12097510470147440266449865 9073132852610580199837399)
          ·
            refine ⟨13609699278915870299756099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9073132852610580199837399 13609699278915870299756099)
            ·
              refine ⟨20414548918373805449634149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13609699278915870299756099 20414548918373805449634149)
              ·
                refine ⟨3827727922195088521806403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20414548918373805449634149 3827727922195088521806403)
                ·
                  refine ⟨5741591883292632782709605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827727922195088521806403 5741591883292632782709605)
                  ·
                    refine ⟨1076548478117368646758051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741591883292632782709605 1076548478117368646758051)
                    ·
                      rfl

theorem cell22_3144856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_3144856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144856 prefixEnd_3144856 := by exact prefixLift 3144856
  have htrace : WordTrace (prefixWord ++ tailWord_3144856) baseStart_3144856 baseEnd_3144856 := by
    simpa [prefixWord, tailWord_3144856, baseEnd_3144856] using wordTrace_append hprefix tailTrace_3144856
  have hstable : (prefixWord ++ tailWord_3144856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144856).length < 2 ^ (prefixWord ++ tailWord_3144856).sum := by decide
  have hdescent : baseEnd_3144856 < baseStart_3144856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144959 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_3144959 : Nat := 118140960795 + 3144959 * 2 ^ 59
def prefixEnd_3144959 : Nat := 4983230072969 + 3 ^ 40 * 3144959 * 2
def baseEnd_3144959 : Nat := 1076583737122310711432735

theorem tailTrace_3144959 : CollatzResearch.WordTrace tailWord_3144959 prefixEnd_3144959 1076583737122310711432735 := by
  unfold tailWord_3144959
  simp only [CollatzResearch.WordTrace]
  refine ⟨114706078213358134080301931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76470718808905422720201287 114706078213358134080301931)
  ·
    refine ⟨172059117320037201120452897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114706078213358134080301931 172059117320037201120452897)
    ·
      refine ⟨129044337990027900840339673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172059117320037201120452897 129044337990027900840339673)
      ·
        refine ⟨96783253492520925630254755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129044337990027900840339673 96783253492520925630254755)
        ·
          refine ⟨145174880238781388445382133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96783253492520925630254755 145174880238781388445382133)
          ·
            refine ⟨13610145022385755166754575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145174880238781388445382133 13610145022385755166754575)
            ·
              refine ⟨20415217533578632750131863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13610145022385755166754575 20415217533578632750131863)
              ·
                refine ⟨30622826300367949125197795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20415217533578632750131863 30622826300367949125197795)
                ·
                  refine ⟨45934239450551923687796693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30622826300367949125197795 45934239450551923687796693)
                  ·
                    refine ⟨1076583737122310711432735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45934239450551923687796693 1076583737122310711432735)
                    ·
                      rfl

theorem cell22_3144959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_3144959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144959 prefixEnd_3144959 := by exact prefixLift 3144959
  have htrace : WordTrace (prefixWord ++ tailWord_3144959) baseStart_3144959 baseEnd_3144959 := by
    simpa [prefixWord, tailWord_3144959, baseEnd_3144959] using wordTrace_append hprefix tailTrace_3144959
  have hstable : (prefixWord ++ tailWord_3144959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144959).length < 2 ^ (prefixWord ++ tailWord_3144959).sum := by decide
  have hdescent : baseEnd_3144959 < baseStart_3144959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3144961 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 5]
def baseStart_3144961 : Nat := 118140960795 + 3144961 * 2 ^ 59
def prefixEnd_3144961 : Nat := 4983230072969 + 3 ^ 40 * 3144961 * 2
def baseEnd_3144961 : Nat := 358861473921061124294243

theorem tailTrace_3144961 : CollatzResearch.WordTrace tailWord_3144961 prefixEnd_3144961 358861473921061124294243 := by
  unfold tailWord_3144961
  simp only [CollatzResearch.WordTrace]
  refine ⟨114706151159350888421874737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76470767439567258947916491 114706151159350888421874737)
  ·
    refine ⟨86029613369513166316406053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114706151159350888421874737 86029613369513166316406053)
    ·
      refine ⟨16130552506783718684326135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86029613369513166316406053 16130552506783718684326135)
      ·
        refine ⟨24195828760175578026489203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16130552506783718684326135 24195828760175578026489203)
        ·
          refine ⟨36293743140263367039733805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24195828760175578026489203 36293743140263367039733805)
          ·
            refine ⟨13610153677598762639900177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36293743140263367039733805 13610153677598762639900177)
            ·
              refine ⟨10207615258199071979925133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13610153677598762639900177 10207615258199071979925133)
              ·
                refine ⟨3827855721824651992471925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10207615258199071979925133 3827855721824651992471925)
                ·
                  refine ⟨358861473921061124294243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827855721824651992471925 358861473921061124294243)
                  ·
                    rfl

theorem cell22_3144961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_3144961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3144961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3144961 prefixEnd_3144961 := by exact prefixLift 3144961
  have htrace : WordTrace (prefixWord ++ tailWord_3144961) baseStart_3144961 baseEnd_3144961 := by
    simpa [prefixWord, tailWord_3144961, baseEnd_3144961] using wordTrace_append hprefix tailTrace_3144961
  have hstable : (prefixWord ++ tailWord_3144961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3144961).length < 2 ^ (prefixWord ++ tailWord_3144961).sum := by decide
  have hdescent : baseEnd_3144961 < baseStart_3144961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3144961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145025 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3145025 : Nat := 118140960795 + 3145025 * 2 ^ 59
def prefixEnd_3145025 : Nat := 4983230072969 + 3 ^ 40 * 3145025 * 2
def baseEnd_3145025 : Nat := 1076606330271108539282533

theorem tailTrace_3145025 : CollatzResearch.WordTrace tailWord_3145025 prefixEnd_3145025 1076606330271108539282533 := by
  unfold tailWord_3145025
  simp only [CollatzResearch.WordTrace]
  refine ⟨114708485431119027352204529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76472323620746018234803019 114708485431119027352204529)
  ·
    refine ⟨86031364073339270514153397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114708485431119027352204529 86031364073339270514153397)
    ·
      refine ⟨8065440381875556610701881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86031364073339270514153397 8065440381875556610701881)
      ·
        refine ⟨6049080286406667458026411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8065440381875556610701881 6049080286406667458026411)
        ·
          refine ⟨9073620429610001187039617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049080286406667458026411 9073620429610001187039617)
          ·
            refine ⟨6805215322207500890279713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9073620429610001187039617 6805215322207500890279713)
            ·
              refine ⟨5103911491655625667709785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6805215322207500890279713 5103911491655625667709785)
              ·
                refine ⟨3827933618741719250782339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5103911491655625667709785 3827933618741719250782339)
                ·
                  refine ⟨5741900428112578876173509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827933618741719250782339 5741900428112578876173509)
                  ·
                    refine ⟨1076606330271108539282533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741900428112578876173509 1076606330271108539282533)
                    ·
                      rfl

theorem cell22_3145025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3145025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145025 prefixEnd_3145025 := by exact prefixLift 3145025
  have htrace : WordTrace (prefixWord ++ tailWord_3145025) baseStart_3145025 baseEnd_3145025 := by
    simpa [prefixWord, tailWord_3145025, baseEnd_3145025] using wordTrace_append hprefix tailTrace_3145025
  have hstable : (prefixWord ++ tailWord_3145025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145025).length < 2 ^ (prefixWord ++ tailWord_3145025).sum := by decide
  have hdescent : baseEnd_3145025 < baseStart_3145025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145036 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_3145036 : Nat := 118140960795 + 3145036 * 2 ^ 59
def prefixEnd_3145036 : Nat := 4983230072969 + 3 ^ 40 * 3145036 * 2
def baseEnd_3145036 : Nat := 1076610095795908177257499

theorem tailTrace_3145036 : CollatzResearch.WordTrace tailWord_3145036 prefixEnd_3145036 1076610095795908177257499 := by
  unfold tailWord_3145036
  simp only [CollatzResearch.WordTrace]
  refine ⟨57354443317039588115427481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76472591089386117487236641 57354443317039588115427481)
  ·
    refine ⟨43015832487779691086570611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57354443317039588115427481 43015832487779691086570611)
    ·
      refine ⟨64523748731669536629855917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43015832487779691086570611 64523748731669536629855917)
      ·
        refine ⟨24196405774376076236195969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64523748731669536629855917 24196405774376076236195969)
        ·
          refine ⟨18147304330782057177146977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24196405774376076236195969 18147304330782057177146977)
          ·
            refine ⟨13610478248086542882860233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18147304330782057177146977 13610478248086542882860233)
            ·
              refine ⟨10207858686064907162145175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13610478248086542882860233 10207858686064907162145175)
              ·
                refine ⟨15311788029097360743217763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10207858686064907162145175 15311788029097360743217763)
                ·
                  refine ⟨22967682043646041114826645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15311788029097360743217763 22967682043646041114826645)
                  ·
                    refine ⟨1076610095795908177257499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22967682043646041114826645 1076610095795908177257499)
                    ·
                      rfl

theorem cell22_3145036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_3145036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145036 prefixEnd_3145036 := by exact prefixLift 3145036
  have htrace : WordTrace (prefixWord ++ tailWord_3145036) baseStart_3145036 baseEnd_3145036 := by
    simpa [prefixWord, tailWord_3145036, baseEnd_3145036] using wordTrace_append hprefix tailTrace_3145036
  have hstable : (prefixWord ++ tailWord_3145036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145036).length < 2 ^ (prefixWord ++ tailWord_3145036).sum := by decide
  have hdescent : baseEnd_3145036 < baseStart_3145036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145100 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_3145100 : Nat := 118140960795 + 3145100 * 2 ^ 59
def prefixEnd_3145100 : Nat := 4983230072969 + 3 ^ 40 * 3145100 * 2
def baseEnd_3145100 : Nat := 1076632004303833343657303

theorem tailTrace_3145100 : CollatzResearch.WordTrace tailWord_3145100 prefixEnd_3145100 1076632004303833343657303 := by
  unfold tailWord_3145100
  simp only [CollatzResearch.WordTrace]
  refine ⟨57355610452923657580592377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76474147270564876774123169 57355610452923657580592377)
  ·
    refine ⟨43016707839692743185444283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57355610452923657580592377 43016707839692743185444283)
    ·
      refine ⟨64525061759539114778166425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43016707839692743185444283 64525061759539114778166425)
      ·
        refine ⟨48393796319654336083624819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64525061759539114778166425 48393796319654336083624819)
        ·
          refine ⟨72590694479481504125437229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48393796319654336083624819 72590694479481504125437229)
          ·
            refine ⟨27221510429805564047038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72590694479481504125437229 27221510429805564047038961)
            ·
              refine ⟨20416132822354173035279221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27221510429805564047038961 20416132822354173035279221)
              ·
                refine ⟨1914012452095703722057427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20416132822354173035279221 1914012452095703722057427)
                ·
                  refine ⟨2871018678143555583086141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914012452095703722057427 2871018678143555583086141)
                  ·
                    refine ⟨1076632004303833343657303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871018678143555583086141 1076632004303833343657303)
                    ·
                      rfl

theorem cell22_3145100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_3145100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145100 prefixEnd_3145100 := by exact prefixLift 3145100
  have htrace : WordTrace (prefixWord ++ tailWord_3145100) baseStart_3145100 baseEnd_3145100 := by
    simpa [prefixWord, tailWord_3145100, baseEnd_3145100] using wordTrace_append hprefix tailTrace_3145100
  have hstable : (prefixWord ++ tailWord_3145100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145100).length < 2 ^ (prefixWord ++ tailWord_3145100).sum := by decide
  have hdescent : baseEnd_3145100 < baseStart_3145100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145111 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3145111 : Nat := 118140960795 + 3145111 * 2 ^ 59
def prefixEnd_3145111 : Nat := 4983230072969 + 3 ^ 40 * 3145111 * 2
def baseEnd_3145111 : Nat := 1076635769828632981632269

theorem tailTrace_3145111 : CollatzResearch.WordTrace tailWord_3145111 prefixEnd_3145111 1076635769828632981632269 := by
  unfold tailWord_3145111
  simp only [CollatzResearch.WordTrace]
  refine ⟨114711622108807464039835187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76474414739204976026556791 114711622108807464039835187)
  ·
    refine ⟨172067433163211196059752781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114711622108807464039835187 172067433163211196059752781)
    ·
      refine ⟨64525287436204198522407293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172067433163211196059752781 64525287436204198522407293)
      ·
        refine ⟨24196982788576574445902735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64525287436204198522407293 24196982788576574445902735)
        ·
          refine ⟨36295474182864861668854103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24196982788576574445902735 36295474182864861668854103)
          ·
            refine ⟨54443211274297292503281155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36295474182864861668854103 54443211274297292503281155)
            ·
              refine ⟨81664816911445938754921733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54443211274297292503281155 81664816911445938754921733)
              ·
                refine ⟨15312153170896113516547825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81664816911445938754921733 15312153170896113516547825)
                ·
                  refine ⟨11484114878172085137410869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15312153170896113516547825 11484114878172085137410869)
                  ·
                    refine ⟨1076635769828632981632269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11484114878172085137410869 1076635769828632981632269)
                    ·
                      rfl

theorem cell22_3145111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3145111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145111 prefixEnd_3145111 := by exact prefixLift 3145111
  have htrace : WordTrace (prefixWord ++ tailWord_3145111) baseStart_3145111 baseEnd_3145111 := by
    simpa [prefixWord, tailWord_3145111, baseEnd_3145111] using wordTrace_append hprefix tailTrace_3145111
  have hstable : (prefixWord ++ tailWord_3145111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145111).length < 2 ^ (prefixWord ++ tailWord_3145111).sum := by decide
  have hdescent : baseEnd_3145111 < baseStart_3145111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145113 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 5]
def baseStart_3145113 : Nat := 118140960795 + 3145113 * 2 ^ 59
def prefixEnd_3145113 : Nat := 4983230072969 + 3 ^ 40 * 3145113 * 2
def baseEnd_3145113 : Nat := 358878818156501881027421

theorem tailTrace_3145113 : CollatzResearch.WordTrace tailWord_3145113 prefixEnd_3145113 358878818156501881027421 := by
  unfold tailWord_3145113
  simp only [CollatzResearch.WordTrace]
  refine ⟨114711695054800218381407993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76474463369866812254271995 114711695054800218381407993)
  ·
    refine ⟨86033771291100163786055995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114711695054800218381407993 86033771291100163786055995)
    ·
      refine ⟨129050656936650245679083993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86033771291100163786055995 129050656936650245679083993)
      ·
        refine ⟨96787992702487684259312995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129050656936650245679083993 96787992702487684259312995)
        ·
          refine ⟨145181989053731526388969493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96787992702487684259312995 145181989053731526388969493)
          ·
            refine ⟨6805405736893665299482945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145181989053731526388969493 6805405736893665299482945)
            ·
              refine ⟨5104054302670248974612209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6805405736893665299482945 5104054302670248974612209)
              ·
                refine ⟨3828040727002686730959157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104054302670248974612209 3828040727002686730959157)
                ·
                  refine ⟨358878818156501881027421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3828040727002686730959157 358878818156501881027421)
                  ·
                    rfl

theorem cell22_3145113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_3145113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145113 prefixEnd_3145113 := by exact prefixLift 3145113
  have htrace : WordTrace (prefixWord ++ tailWord_3145113) baseStart_3145113 baseEnd_3145113 := by
    simpa [prefixWord, tailWord_3145113, baseEnd_3145113] using wordTrace_append hprefix tailTrace_3145113
  have hstable : (prefixWord ++ tailWord_3145113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145113).length < 2 ^ (prefixWord ++ tailWord_3145113).sum := by decide
  have hdescent : baseEnd_3145113 < baseStart_3145113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145117 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_3145117 : Nat := 118140960795 + 3145117 * 2 ^ 59
def prefixEnd_3145117 : Nat := 4983230072969 + 3 ^ 40 * 3145117 * 2
def baseEnd_3145117 : Nat := 1076637823751250965982251

theorem tailTrace_3145117 : CollatzResearch.WordTrace tailWord_3145117 prefixEnd_3145117 1076637823751250965982251 := by
  unfold tailWord_3145117
  simp only [CollatzResearch.WordTrace]
  refine ⟨114711840946785727064553605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76474560631190484709702403 114711840946785727064553605)
  ·
    refine ⟨21508470177522323824603801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114711840946785727064553605 21508470177522323824603801)
    ·
      refine ⟨16131352633141742868452851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21508470177522323824603801 16131352633141742868452851)
      ·
        refine ⟨24197028949712614302679277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16131352633141742868452851 24197028949712614302679277)
        ·
          refine ⟨9073885856142230363504729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24197028949712614302679277 9073885856142230363504729)
          ·
            refine ⟨6805414392106672772628547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9073885856142230363504729 6805414392106672772628547)
            ·
              refine ⟨10208121588160009158942821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6805414392106672772628547 10208121588160009158942821)
              ·
                refine ⟨1914022797780001717301779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10208121588160009158942821 1914022797780001717301779)
                ·
                  refine ⟨2871034196670002575952669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914022797780001717301779 2871034196670002575952669)
                  ·
                    refine ⟨1076637823751250965982251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871034196670002575952669 1076637823751250965982251)
                    ·
                      rfl

theorem cell22_3145117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_3145117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145117 prefixEnd_3145117 := by exact prefixLift 3145117
  have htrace : WordTrace (prefixWord ++ tailWord_3145117) baseStart_3145117 baseEnd_3145117 := by
    simpa [prefixWord, tailWord_3145117, baseEnd_3145117] using wordTrace_append hprefix tailTrace_3145117
  have hstable : (prefixWord ++ tailWord_3145117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145117).length < 2 ^ (prefixWord ++ tailWord_3145117).sum := by decide
  have hdescent : baseEnd_3145117 < baseStart_3145117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145143 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3145143 : Nat := 118140960795 + 3145143 * 2 ^ 59
def prefixEnd_3145143 : Nat := 4983230072969 + 3 ^ 40 * 3145143 * 2
def baseEnd_3145143 : Nat := 1076646724082595564832171

theorem tailTrace_3145143 : CollatzResearch.WordTrace tailWord_3145143 prefixEnd_3145143 1076646724082595564832171 := by
  unfold tailWord_3145143
  simp only [CollatzResearch.WordTrace]
  refine ⟨114712789244691533505000083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76475192829794355670000055 114712789244691533505000083)
  ·
    refine ⟨172069183867037300257500125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114712789244691533505000083 172069183867037300257500125)
    ·
      refine ⟨64525943950138987596562547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172069183867037300257500125 64525943950138987596562547)
      ·
        refine ⟨96788915925208481394843821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64525943950138987596562547 96788915925208481394843821)
        ·
          refine ⟨36295843471953180523066433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96788915925208481394843821 36295843471953180523066433)
          ·
            refine ⟨27221882603964885392299825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36295843471953180523066433 27221882603964885392299825)
            ·
              refine ⟨20416411952973664044224869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27221882603964885392299825 20416411952973664044224869)
              ·
                refine ⟨3828077241182562008292163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20416411952973664044224869 3828077241182562008292163)
                ·
                  refine ⟨5742115861773843012438245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828077241182562008292163 5742115861773843012438245)
                  ·
                    refine ⟨1076646724082595564832171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5742115861773843012438245 1076646724082595564832171)
                    ·
                      rfl

theorem cell22_3145143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3145143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145143 prefixEnd_3145143 := by exact prefixLift 3145143
  have htrace : WordTrace (prefixWord ++ tailWord_3145143) baseStart_3145143 baseEnd_3145143 := by
    simpa [prefixWord, tailWord_3145143, baseEnd_3145143] using wordTrace_append hprefix tailTrace_3145143
  have hstable : (prefixWord ++ tailWord_3145143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145143).length < 2 ^ (prefixWord ++ tailWord_3145143).sum := by decide
  have hdescent : baseEnd_3145143 < baseStart_3145143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145205 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3145205 : Nat := 118140960795 + 3145205 * 2 ^ 59
def prefixEnd_3145205 : Nat := 4983230072969 + 3 ^ 40 * 3145205 * 2
def baseEnd_3145205 : Nat := 1076667947949648069781981

theorem tailTrace_3145205 : CollatzResearch.WordTrace tailWord_3145205 prefixEnd_3145205 1076667947949648069781981 := by
  unfold tailWord_3145205
  simp only [CollatzResearch.WordTrace]
  refine ⟨114715050570466918093757069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76476700380311278729171379 114715050570466918093757069)
  ·
    refine ⟨43018143963925094285158901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114715050570466918093757069 43018143963925094285158901)
    ·
      refine ⟨4032950996617977589233647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43018143963925094285158901 4032950996617977589233647)
      ·
        refine ⟨6049426494926966383850471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032950996617977589233647 6049426494926966383850471)
        ·
          refine ⟨9074139742390449575775707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049426494926966383850471 9074139742390449575775707)
          ·
            refine ⟨13611209613585674363663561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074139742390449575775707 13611209613585674363663561)
            ·
              refine ⟨10208407210189255772747671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13611209613585674363663561 10208407210189255772747671)
              ·
                refine ⟨15312610815283883659121507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10208407210189255772747671 15312610815283883659121507)
                ·
                  refine ⟨22968916222925825488682261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15312610815283883659121507 22968916222925825488682261)
                  ·
                    refine ⟨1076667947949648069781981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22968916222925825488682261 1076667947949648069781981)
                    ·
                      rfl

theorem cell22_3145205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3145205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145205 prefixEnd_3145205 := by exact prefixLift 3145205
  have htrace : WordTrace (prefixWord ++ tailWord_3145205) baseStart_3145205 baseEnd_3145205 := by
    simpa [prefixWord, tailWord_3145205, baseEnd_3145205] using wordTrace_append hprefix tailTrace_3145205
  have hstable : (prefixWord ++ tailWord_3145205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145205).length < 2 ^ (prefixWord ++ tailWord_3145205).sum := by decide
  have hdescent : baseEnd_3145205 < baseStart_3145205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145220 : List Nat := [2, 3, 2, 3, 2, 2, 8]
def baseStart_3145220 : Nat := 118140960795 + 3145220 * 2 ^ 59
def prefixEnd_3145220 : Nat := 4983230072969 + 3 ^ 40 * 3145220 * 2
def baseEnd_3145220 : Nat := 39876780842821964098405

theorem tailTrace_3145220 : CollatzResearch.WordTrace tailWord_3145220 prefixEnd_3145220 39876780842821964098405 := by
  unfold tailWord_3145220
  simp only [CollatzResearch.WordTrace]
  refine ⟨57357798832706287827776557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76477065110275050437035409 57357798832706287827776557)
  ·
    refine ⟨21509174562264857935416209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57357798832706287827776557 21509174562264857935416209)
    ·
      refine ⟨16131880921698643451562157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21509174562264857935416209 16131880921698643451562157)
      ·
        refine ⟨6049455345636991294335809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16131880921698643451562157 6049455345636991294335809)
        ·
          refine ⟨4537091509227743470751857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6049455345636991294335809 4537091509227743470751857)
          ·
            refine ⟨3402818631920807603063893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4537091509227743470751857 3402818631920807603063893)
            ·
              refine ⟨39876780842821964098405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3402818631920807603063893 39876780842821964098405)
              ·
                rfl

theorem cell22_3145220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 8].length) (baseStart_3145220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145220 prefixEnd_3145220 := by exact prefixLift 3145220
  have htrace : WordTrace (prefixWord ++ tailWord_3145220) baseStart_3145220 baseEnd_3145220 := by
    simpa [prefixWord, tailWord_3145220, baseEnd_3145220] using wordTrace_append hprefix tailTrace_3145220
  have hstable : (prefixWord ++ tailWord_3145220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145220).length < 2 ^ (prefixWord ++ tailWord_3145220).sum := by decide
  have hdescent : baseEnd_3145220 < baseStart_3145220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145231 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 11]
def baseStart_3145231 : Nat := 118140960795 + 3145231 * 2 ^ 59
def prefixEnd_3145231 : Nat := 4983230072969 + 3 ^ 40 * 3145231 * 2
def baseEnd_3145231 : Nat := 358892282760330889543967

theorem tailTrace_3145231 : CollatzResearch.WordTrace tailWord_3145231 prefixEnd_3145231 358892282760330889543967 := by
  unfold tailWord_3145231
  simp only [CollatzResearch.WordTrace]
  refine ⟨114715998868372724534203547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76477332578915149689469031 114715998868372724534203547)
  ·
    refine ⟨172073998302559086801305321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114715998868372724534203547 172073998302559086801305321)
    ·
      refine ⟨129055498726919315100978991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172073998302559086801305321 129055498726919315100978991)
      ·
        refine ⟨193583248090378972651468487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129055498726919315100978991 193583248090378972651468487)
        ·
          refine ⟨290374872135568458977202731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193583248090378972651468487 290374872135568458977202731)
          ·
            refine ⟨435562308203352688465804097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290374872135568458977202731 435562308203352688465804097)
            ·
              refine ⟨326671731152514516349353073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435562308203352688465804097 326671731152514516349353073)
              ·
                refine ⟨245003798364385887262014805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326671731152514516349353073 245003798364385887262014805)
                ·
                  refine ⟨358892282760330889543967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 245003798364385887262014805 358892282760330889543967)
                  ·
                    rfl

theorem cell22_3145231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_3145231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145231 prefixEnd_3145231 := by exact prefixLift 3145231
  have htrace : WordTrace (prefixWord ++ tailWord_3145231) baseStart_3145231 baseEnd_3145231 := by
    simpa [prefixWord, tailWord_3145231, baseEnd_3145231] using wordTrace_append hprefix tailTrace_3145231
  have hstable : (prefixWord ++ tailWord_3145231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145231).length < 2 ^ (prefixWord ++ tailWord_3145231).sum := by decide
  have hdescent : baseEnd_3145231 < baseStart_3145231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145235 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 3, 3]
def baseStart_3145235 : Nat := 118140960795 + 3145235 * 2 ^ 59
def prefixEnd_3145235 : Nat := 4983230072969 + 3 ^ 40 * 3145235 * 2
def baseEnd_3145235 : Nat := 1076678217562737991531889

theorem tailTrace_3145235 : CollatzResearch.WordTrace tailWord_3145235 prefixEnd_3145235 1076678217562737991531889 := by
  unfold tailWord_3145235
  simp only [CollatzResearch.WordTrace]
  refine ⟨114716144760358233217349159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76477429840238822144899439 114716144760358233217349159)
  ·
    refine ⟨172074217140537349826023739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114716144760358233217349159 172074217140537349826023739)
    ·
      refine ⟨258111325710806024739035609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172074217140537349826023739 258111325710806024739035609)
      ·
        refine ⟨193583494283104518554276707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258111325710806024739035609 193583494283104518554276707)
        ·
          refine ⟨290375241424656777831415061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193583494283104518554276707 290375241424656777831415061)
          ·
            refine ⟨13611339441780786460847581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290375241424656777831415061 13611339441780786460847581)
            ·
              refine ⟨5104252290667794922817843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13611339441780786460847581 5104252290667794922817843)
              ·
                refine ⟨7656378436001692384226765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104252290667794922817843 7656378436001692384226765)
                ·
                  refine ⟨2871141913500634644085037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7656378436001692384226765 2871141913500634644085037)
                  ·
                    refine ⟨1076678217562737991531889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871141913500634644085037 1076678217562737991531889)
                    ·
                      rfl

theorem cell22_3145235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 3].length) (baseStart_3145235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145235 prefixEnd_3145235 := by exact prefixLift 3145235
  have htrace : WordTrace (prefixWord ++ tailWord_3145235) baseStart_3145235 baseEnd_3145235 := by
    simpa [prefixWord, tailWord_3145235, baseEnd_3145235] using wordTrace_append hprefix tailTrace_3145235
  have hstable : (prefixWord ++ tailWord_3145235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145235).length < 2 ^ (prefixWord ++ tailWord_3145235).sum := by decide
  have hdescent : baseEnd_3145235 < baseStart_3145235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145378 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3145378 : Nat := 118140960795 + 3145378 * 2 ^ 59
def prefixEnd_3145378 : Nat := 4983230072969 + 3 ^ 40 * 3145378 * 2
def baseEnd_3145378 : Nat := 358909056461711095068817

theorem tailTrace_3145378 : CollatzResearch.WordTrace tailWord_3145378 prefixEnd_3145378 358909056461711095068817 := by
  unfold tailWord_3145378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28680340099710042159951197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76480906932560112426536525 28680340099710042159951197)
  ·
    refine ⟨10755127537391265809981699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28680340099710042159951197 10755127537391265809981699)
    ·
      refine ⟨16132691306086898714972549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10755127537391265809981699 16132691306086898714972549)
      ·
        refine ⟨3024879619891293509057353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16132691306086898714972549 3024879619891293509057353)
        ·
          refine ⟨2268659714918470131793015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024879619891293509057353 2268659714918470131793015)
          ·
            refine ⟨3402989572377705197689523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268659714918470131793015 3402989572377705197689523)
            ·
              refine ⟨5104484358566557796534285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402989572377705197689523 5104484358566557796534285)
              ·
                refine ⟨1914181634462459173700357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5104484358566557796534285 1914181634462459173700357)
                ·
                  refine ⟨358909056461711095068817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914181634462459173700357 358909056461711095068817)
                  ·
                    rfl

theorem cell22_3145378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3145378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145378 prefixEnd_3145378 := by exact prefixLift 3145378
  have htrace : WordTrace (prefixWord ++ tailWord_3145378) baseStart_3145378 baseEnd_3145378 := by
    simpa [prefixWord, tailWord_3145378, baseEnd_3145378] using wordTrace_append hprefix tailTrace_3145378
  have hstable : (prefixWord ++ tailWord_3145378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145378).length < 2 ^ (prefixWord ++ tailWord_3145378).sum := by decide
  have hdescent : baseEnd_3145378 < baseStart_3145378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145404 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_3145404 : Nat := 118140960795 + 3145404 * 2 ^ 59
def prefixEnd_3145404 : Nat := 4983230072969 + 3 ^ 40 * 3145404 * 2
def baseEnd_3145404 : Nat := 1076736069716477884056371

theorem tailTrace_3145404 : CollatzResearch.WordTrace tailWord_3145404 prefixEnd_3145404 1076736069716477884056371 := by
  unfold tailWord_3145404
  simp only [CollatzResearch.WordTrace]
  refine ⟨57361154348372987540125633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76481539131163983386834177 57361154348372987540125633)
  ·
    refine ⟨43020865761279740655094225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57361154348372987540125633 43020865761279740655094225)
    ·
      refine ⟨32265649320959805491320669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43020865761279740655094225 32265649320959805491320669)
      ·
        refine ⟨12099618495359927059245251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32265649320959805491320669 12099618495359927059245251)
        ·
          refine ⟨18149427743039890588867877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099618495359927059245251 18149427743039890588867877)
          ·
            refine ⟨3403017701819979485412727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18149427743039890588867877 3403017701819979485412727)
            ·
              refine ⟨5104526552729969228119091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403017701819979485412727 5104526552729969228119091)
              ·
                refine ⟨7656789829094953842178637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104526552729969228119091 7656789829094953842178637)
                ·
                  refine ⟨2871296185910607690816989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7656789829094953842178637 2871296185910607690816989)
                  ·
                    refine ⟨1076736069716477884056371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871296185910607690816989 1076736069716477884056371)
                    ·
                      rfl

theorem cell22_3145404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_3145404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145404 prefixEnd_3145404 := by exact prefixLift 3145404
  have htrace : WordTrace (prefixWord ++ tailWord_3145404) baseStart_3145404 baseEnd_3145404 := by
    simpa [prefixWord, tailWord_3145404, baseEnd_3145404] using wordTrace_append hprefix tailTrace_3145404
  have hstable : (prefixWord ++ tailWord_3145404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145404).length < 2 ^ (prefixWord ++ tailWord_3145404).sum := by decide
  have hdescent : baseEnd_3145404 < baseStart_3145404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145475 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 4, 4]
def baseStart_3145475 : Nat := 118140960795 + 3145475 * 2 ^ 59
def prefixEnd_3145475 : Nat := 4983230072969 + 3 ^ 40 * 3145475 * 2
def baseEnd_3145475 : Nat := 1076760374467457365531153

theorem tailTrace_3145475 : CollatzResearch.WordTrace tailWord_3145475 prefixEnd_3145475 1076760374467457365531153 := by
  unfold tailWord_3145475
  simp only [CollatzResearch.WordTrace]
  refine ⟨114724898279488754206085879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76483265519659169470723919 114724898279488754206085879)
  ·
    refine ⟨172087347419233131309128819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114724898279488754206085879 172087347419233131309128819)
    ·
      refine ⟨258131021128849696963693229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172087347419233131309128819 258131021128849696963693229)
      ·
        refine ⟨96799132923318636361384961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258131021128849696963693229 96799132923318636361384961)
        ·
          refine ⟨72599349692488977271038721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96799132923318636361384961 72599349692488977271038721)
          ·
            refine ⟨54449512269366732953279041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72599349692488977271038721 54449512269366732953279041)
            ·
              refine ⟨40837134202025049714959281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54449512269366732953279041 40837134202025049714959281)
              ·
                refine ⟨30627850651518787286219461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40837134202025049714959281 30627850651518787286219461)
                ·
                  refine ⟨5742721997159772616166149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30627850651518787286219461 5742721997159772616166149)
                  ·
                    refine ⟨1076760374467457365531153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5742721997159772616166149 1076760374467457365531153)
                    ·
                      rfl

theorem cell22_3145475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_3145475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145475 prefixEnd_3145475 := by exact prefixLift 3145475
  have htrace : WordTrace (prefixWord ++ tailWord_3145475) baseStart_3145475 baseEnd_3145475 := by
    simpa [prefixWord, tailWord_3145475, baseEnd_3145475] using wordTrace_append hprefix tailTrace_3145475
  have hstable : (prefixWord ++ tailWord_3145475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145475).length < 2 ^ (prefixWord ++ tailWord_3145475).sum := by decide
  have hdescent : baseEnd_3145475 < baseStart_3145475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145631 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 4]
def baseStart_3145631 : Nat := 118140960795 + 3145631 * 2 ^ 59
def prefixEnd_3145631 : Nat := 4983230072969 + 3 ^ 40 * 3145631 * 2
def baseEnd_3145631 : Nat := 358937925485174986210225

theorem tailTrace_3145631 : CollatzResearch.WordTrace tailWord_3145631 prefixEnd_3145631 358937925485174986210225 := by
  unfold tailWord_3145631
  simp only [CollatzResearch.WordTrace]
  refine ⟨114730588066923592848764747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76487058711282395232509831 114730588066923592848764747)
  ·
    refine ⟨172095882100385389273147121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114730588066923592848764747 172095882100385389273147121)
    ·
      refine ⟨129071911575289041954860341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172095882100385389273147121 129071911575289041954860341)
      ·
        refine ⟨12100491710183347683268157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129071911575289041954860341 12100491710183347683268157)
        ·
          refine ⟨4537684391318755381225559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12100491710183347683268157 4537684391318755381225559)
          ·
            refine ⟨6806526586978133071838339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537684391318755381225559 6806526586978133071838339)
            ·
              refine ⟨10209789880467199607757509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806526586978133071838339 10209789880467199607757509)
              ·
                refine ⟨1914335602587599926454533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10209789880467199607757509 1914335602587599926454533)
                ·
                  refine ⟨358937925485174986210225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914335602587599926454533 358937925485174986210225)
                  ·
                    rfl

theorem cell22_3145631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 4].length) (baseStart_3145631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145631 prefixEnd_3145631 := by exact prefixLift 3145631
  have htrace : WordTrace (prefixWord ++ tailWord_3145631) baseStart_3145631 baseEnd_3145631 := by
    simpa [prefixWord, tailWord_3145631, baseEnd_3145631] using wordTrace_append hprefix tailTrace_3145631
  have hstable : (prefixWord ++ tailWord_3145631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145631).length < 2 ^ (prefixWord ++ tailWord_3145631).sum := by decide
  have hdescent : baseEnd_3145631 < baseStart_3145631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145661 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_3145661 : Nat := 118140960795 + 3145661 * 2 ^ 59
def prefixEnd_3145661 : Nat := 4983230072969 + 3 ^ 40 * 3145661 * 2
def baseEnd_3145661 : Nat := 1076824046068614880380583

theorem tailTrace_3145661 : CollatzResearch.WordTrace tailWord_3145661 prefixEnd_3145661 1076824046068614880380583 := by
  unfold tailWord_3145661
  simp only [CollatzResearch.WordTrace]
  refine ⟨114731682256814907972356837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76487788171209938648237891 114731682256814907972356837)
  ·
    refine ⟨21512190423152795244816907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114731682256814907972356837 21512190423152795244816907)
    ·
      refine ⟨32268285634729192867225361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21512190423152795244816907 32268285634729192867225361)
      ·
        refine ⟨24201214226046894650419021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32268285634729192867225361 24201214226046894650419021)
        ·
          refine ⟨9075455334767585493907133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24201214226046894650419021 9075455334767585493907133)
          ·
            refine ⟨3403295750537844560215175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9075455334767585493907133 3403295750537844560215175)
            ·
              refine ⟨5104943625806766840322763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403295750537844560215175 5104943625806766840322763)
              ·
                refine ⟨7657415438710150260484145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104943625806766840322763 7657415438710150260484145)
                ·
                  refine ⟨5743061579032612695363109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657415438710150260484145 5743061579032612695363109)
                  ·
                    refine ⟨1076824046068614880380583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743061579032612695363109 1076824046068614880380583)
                    ·
                      rfl

theorem cell22_3145661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_3145661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145661 prefixEnd_3145661 := by exact prefixLift 3145661
  have htrace : WordTrace (prefixWord ++ tailWord_3145661) baseStart_3145661 baseEnd_3145661 := by
    simpa [prefixWord, tailWord_3145661, baseEnd_3145661] using wordTrace_append hprefix tailTrace_3145661
  have hstable : (prefixWord ++ tailWord_3145661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145661).length < 2 ^ (prefixWord ++ tailWord_3145661).sum := by decide
  have hdescent : baseEnd_3145661 < baseStart_3145661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145687 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 7]
def baseStart_3145687 : Nat := 118140960795 + 3145687 * 2 ^ 59
def prefixEnd_3145687 : Nat := 4983230072969 + 3 ^ 40 * 3145687 * 2
def baseEnd_3145687 : Nat := 358944315466653159743501

theorem tailTrace_3145687 : CollatzResearch.WordTrace tailWord_3145687 prefixEnd_3145687 358944315466653159743501 := by
  unfold tailWord_3145687
  simp only [CollatzResearch.WordTrace]
  refine ⟨114732630554720714412803315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76488420369813809608535543 114732630554720714412803315)
  ·
    refine ⟨172098945832081071619204973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114732630554720714412803315 172098945832081071619204973)
    ·
      refine ⟨64537104687030401857201865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172098945832081071619204973 64537104687030401857201865)
      ·
        refine ⟨48402828515272801392901399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64537104687030401857201865 48402828515272801392901399)
        ·
          refine ⟨72604242772909202089352099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48402828515272801392901399 72604242772909202089352099)
          ·
            refine ⟨108906364159363803134028149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72604242772909202089352099 108906364159363803134028149)
            ·
              refine ⟨10209971639940356543815139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108906364159363803134028149 10209971639940356543815139)
              ·
                refine ⟨15314957459910534815722709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209971639940356543815139 15314957459910534815722709)
                ·
                  refine ⟨358944315466653159743501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15314957459910534815722709 358944315466653159743501)
                  ·
                    rfl

theorem cell22_3145687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 7].length) (baseStart_3145687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145687 prefixEnd_3145687 := by exact prefixLift 3145687
  have htrace : WordTrace (prefixWord ++ tailWord_3145687) baseStart_3145687 baseEnd_3145687 := by
    simpa [prefixWord, tailWord_3145687, baseEnd_3145687] using wordTrace_append hprefix tailTrace_3145687
  have hstable : (prefixWord ++ tailWord_3145687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145687).length < 2 ^ (prefixWord ++ tailWord_3145687).sum := by decide
  have hdescent : baseEnd_3145687 < baseStart_3145687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145768 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3145768 : Nat := 118140960795 + 3145768 * 2 ^ 59
def prefixEnd_3145768 : Nat := 4983230072969 + 3 ^ 40 * 3145768 * 2
def baseEnd_3145768 : Nat := 1076860674355302267955255

theorem tailTrace_3145768 : CollatzResearch.WordTrace tailWord_3145768 prefixEnd_3145768 1076860674355302267955255 := by
  unfold tailWord_3145768
  simp only [CollatzResearch.WordTrace]
  refine ⟨57367792433713632623250979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76490389911618176831001305 57367792433713632623250979)
  ·
    refine ⟨86051688650570448934876469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57367792433713632623250979 86051688650570448934876469)
    ·
      refine ⟨8067345810990979587644669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86051688650570448934876469 8067345810990979587644669)
      ·
        refine ⟨3025254679121617345366751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8067345810990979587644669 3025254679121617345366751)
        ·
          refine ⟨4537882018682426018050127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025254679121617345366751 4537882018682426018050127)
          ·
            refine ⟨6806823028023639027075191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537882018682426018050127 6806823028023639027075191)
            ·
              refine ⟨10210234542035458540612787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806823028023639027075191 10210234542035458540612787)
              ·
                refine ⟨15315351813053187810919181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210234542035458540612787 15315351813053187810919181)
                ·
                  refine ⟨5743256929894945429094693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15315351813053187810919181 5743256929894945429094693)
                  ·
                    refine ⟨1076860674355302267955255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743256929894945429094693 1076860674355302267955255)
                    ·
                      rfl

theorem cell22_3145768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3145768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145768 prefixEnd_3145768 := by exact prefixLift 3145768
  have htrace : WordTrace (prefixWord ++ tailWord_3145768) baseStart_3145768 baseEnd_3145768 := by
    simpa [prefixWord, tailWord_3145768, baseEnd_3145768] using wordTrace_append hprefix tailTrace_3145768
  have hstable : (prefixWord ++ tailWord_3145768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145768).length < 2 ^ (prefixWord ++ tailWord_3145768).sum := by decide
  have hdescent : baseEnd_3145768 < baseStart_3145768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145779 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 2, 4]
def baseStart_3145779 : Nat := 118140960795 + 3145779 * 2 ^ 59
def prefixEnd_3145779 : Nat := 4983230072969 + 3 ^ 40 * 3145779 * 2
def baseEnd_3145779 : Nat := 1076864439880101905930221

theorem tailTrace_3145779 : CollatzResearch.WordTrace tailWord_3145779 prefixEnd_3145779 1076864439880101905930221 := by
  unfold tailWord_3145779
  simp only [CollatzResearch.WordTrace]
  refine ⟨114735986070387414125152391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76490657380258276083434927 114735986070387414125152391)
  ·
    refine ⟨172103979105581121187728587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114735986070387414125152391 172103979105581121187728587)
    ·
      refine ⟨258155968658371681781592881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172103979105581121187728587 258155968658371681781592881)
      ·
        refine ⟨193616976493778761336194661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258155968658371681781592881 193616976493778761336194661)
        ·
          refine ⟨36303183092583517750536499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193616976493778761336194661 36303183092583517750536499)
          ·
            refine ⟨54454774638875276625804749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36303183092583517750536499 54454774638875276625804749)
            ·
              refine ⟨20420540489578228734676781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54454774638875276625804749 20420540489578228734676781)
              ·
                refine ⟨7657702683591835775503793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20420540489578228734676781 7657702683591835775503793)
                ·
                  refine ⟨5743277012693876831627845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657702683591835775503793 5743277012693876831627845)
                  ·
                    refine ⟨1076864439880101905930221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743277012693876831627845 1076864439880101905930221)
                    ·
                      rfl

theorem cell22_3145779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_3145779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145779 prefixEnd_3145779 := by exact prefixLift 3145779
  have htrace : WordTrace (prefixWord ++ tailWord_3145779) baseStart_3145779 baseEnd_3145779 := by
    simpa [prefixWord, tailWord_3145779, baseEnd_3145779] using wordTrace_append hprefix tailTrace_3145779
  have hstable : (prefixWord ++ tailWord_3145779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145779).length < 2 ^ (prefixWord ++ tailWord_3145779).sum := by decide
  have hdescent : baseEnd_3145779 < baseStart_3145779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145961 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_3145961 : Nat := 118140960795 + 3145961 * 2 ^ 59
def prefixEnd_3145961 : Nat := 4983230072969 + 3 ^ 40 * 3145961 * 2
def baseEnd_3145961 : Nat := 1076926742199514097879663

theorem tailTrace_3145961 : CollatzResearch.WordTrace tailWord_3145961 prefixEnd_3145961 1076926742199514097879663 := by
  unfold tailWord_3145961
  simp only [CollatzResearch.WordTrace]
  refine ⟨114742624155728059208277737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76495082770485372805518491 114742624155728059208277737)
  ·
    refine ⟨86056968116796044406208303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114742624155728059208277737 86056968116796044406208303)
    ·
      refine ⟨129085452175194066609312455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86056968116796044406208303 129085452175194066609312455)
      ·
        refine ⟨193628178262791099913968683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129085452175194066609312455 193628178262791099913968683)
        ·
          refine ⟨290442267394186649870953025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193628178262791099913968683 290442267394186649870953025)
          ·
            refine ⟨217831700545639987403214769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290442267394186649870953025 217831700545639987403214769)
            ·
              refine ⟨163373775409229990552411077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217831700545639987403214769 163373775409229990552411077)
              ·
                refine ⟨30632582889230623228577077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163373775409229990552411077 30632582889230623228577077)
                ·
                  refine ⟨2871804645865370927679101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30632582889230623228577077 2871804645865370927679101)
                  ·
                    refine ⟨1076926742199514097879663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871804645865370927679101 1076926742199514097879663)
                    ·
                      rfl

theorem cell22_3145961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_3145961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3145961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3145961 prefixEnd_3145961 := by exact prefixLift 3145961
  have htrace : WordTrace (prefixWord ++ tailWord_3145961) baseStart_3145961 baseEnd_3145961 := by
    simpa [prefixWord, tailWord_3145961, baseEnd_3145961] using wordTrace_append hprefix tailTrace_3145961
  have hstable : (prefixWord ++ tailWord_3145961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145961).length < 2 ^ (prefixWord ++ tailWord_3145961).sum := by decide
  have hdescent : baseEnd_3145961 < baseStart_3145961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146083 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 2, 4]
def baseStart_3146083 : Nat := 118140960795 + 3146083 * 2 ^ 59
def prefixEnd_3146083 : Nat := 4983230072969 + 3 ^ 40 * 3146083 * 2
def baseEnd_3146083 : Nat := 1076968505292746446329289

theorem tailTrace_3146083 : CollatzResearch.WordTrace tailWord_3146083 prefixEnd_3146083 1076968505292746446329289 := by
  unfold tailWord_3146083
  simp only [CollatzResearch.WordTrace]
  refine ⟨114747073861286074044218903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76498049240857382696145935 114747073861286074044218903)
  ·
    refine ⟨172120610791929111066328355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114747073861286074044218903 172120610791929111066328355)
    ·
      refine ⟨258180916187893666599492533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172120610791929111066328355 258180916187893666599492533)
      ·
        refine ⟨24204460892615031243702425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258180916187893666599492533 24204460892615031243702425)
        ·
          refine ⟨18153345669461273432776819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24204460892615031243702425 18153345669461273432776819)
          ·
            refine ⟨27230018504191910149165229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18153345669461273432776819 27230018504191910149165229)
            ·
              refine ⟨10211256939071966305936961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27230018504191910149165229 10211256939071966305936961)
              ·
                refine ⟨7658442704303974729452721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10211256939071966305936961 7658442704303974729452721)
                ·
                  refine ⟨5743832028227981047089541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7658442704303974729452721 5743832028227981047089541)
                  ·
                    refine ⟨1076968505292746446329289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743832028227981047089541 1076968505292746446329289)
                    ·
                      rfl

theorem cell22_3146083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_3146083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146083 prefixEnd_3146083 := by exact prefixLift 3146083
  have htrace : WordTrace (prefixWord ++ tailWord_3146083) baseStart_3146083 baseEnd_3146083 := by
    simpa [prefixWord, tailWord_3146083, baseEnd_3146083] using wordTrace_append hprefix tailTrace_3146083
  have hstable : (prefixWord ++ tailWord_3146083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146083).length < 2 ^ (prefixWord ++ tailWord_3146083).sum := by decide
  have hdescent : baseEnd_3146083 < baseStart_3146083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146087 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 4]
def baseStart_3146087 : Nat := 118140960795 + 3146087 * 2 ^ 59
def prefixEnd_3146087 : Nat := 4983230072969 + 3 ^ 40 * 3146087 * 2
def baseEnd_3146087 : Nat := 358989958191497256409759

theorem tailTrace_3146087 : CollatzResearch.WordTrace tailWord_3146087 prefixEnd_3146087 358989958191497256409759 := by
  unfold tailWord_3146087
  simp only [CollatzResearch.WordTrace]
  refine ⟨114747219753271582727364515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76498146502181055151576343 114747219753271582727364515)
  ·
    refine ⟨172120829629907374091046773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114747219753271582727364515 172120829629907374091046773)
    ·
      refine ⟨16136327777803816321035635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172120829629907374091046773 16136327777803816321035635)
      ·
        refine ⟨24204491666705724481553453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16136327777803816321035635 24204491666705724481553453)
        ·
          refine ⟨9076684375014646680582545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24204491666705724481553453 9076684375014646680582545)
          ·
            refine ⟨6807513281260985010436909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9076684375014646680582545 6807513281260985010436909)
            ·
              refine ⟨2552817480472869378913841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6807513281260985010436909 2552817480472869378913841)
              ·
                refine ⟨1914613110354652034185381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552817480472869378913841 1914613110354652034185381)
                ·
                  refine ⟨358989958191497256409759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914613110354652034185381 358989958191497256409759)
                  ·
                    rfl

theorem cell22_3146087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 4].length) (baseStart_3146087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146087 prefixEnd_3146087 := by exact prefixLift 3146087
  have htrace : WordTrace (prefixWord ++ tailWord_3146087) baseStart_3146087 baseEnd_3146087 := by
    simpa [prefixWord, tailWord_3146087, baseEnd_3146087] using wordTrace_append hprefix tailTrace_3146087
  have hstable : (prefixWord ++ tailWord_3146087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146087).length < 2 ^ (prefixWord ++ tailWord_3146087).sum := by decide
  have hdescent : baseEnd_3146087 < baseStart_3146087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146098 : List Nat := [3, 2, 1, 2, 1, 4, 2, 7]
def baseStart_3146098 : Nat := 118140960795 + 3146098 * 2 ^ 59
def prefixEnd_3146098 : Nat := 4983230072969 + 3 ^ 40 * 3146098 * 2
def baseEnd_3146098 : Nat := 119663737788810156356027

theorem tailTrace_3146098 : CollatzResearch.WordTrace tailWord_3146098 prefixEnd_3146098 119663737788810156356027 := by
  unfold tailWord_3146098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28686905239057932901503737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76498413970821154404009965 28686905239057932901503737)
  ·
    refine ⟨21515178929293449676127803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28686905239057932901503737 21515178929293449676127803)
    ·
      refine ⟨32272768393940174514191705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21515178929293449676127803 32272768393940174514191705)
      ·
        refine ⟨24204576295455130885643779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32272768393940174514191705 24204576295455130885643779)
        ·
          refine ⟨36306864443182696328465669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24204576295455130885643779 36306864443182696328465669)
          ·
            refine ⟨6807537083096755561587313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36306864443182696328465669 6807537083096755561587313)
            ·
              refine ⟨5105652812322566671190485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807537083096755561587313 5105652812322566671190485)
              ·
                refine ⟨119663737788810156356027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5105652812322566671190485 119663737788810156356027)
                ·
                  rfl

theorem cell22_3146098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_3146098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146098 prefixEnd_3146098 := by exact prefixLift 3146098
  have htrace : WordTrace (prefixWord ++ tailWord_3146098) baseStart_3146098 baseEnd_3146098 := by
    simpa [prefixWord, tailWord_3146098, baseEnd_3146098] using wordTrace_append hprefix tailTrace_3146098
  have hstable : (prefixWord ++ tailWord_3146098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146098).length < 2 ^ (prefixWord ++ tailWord_3146098).sum := by decide
  have hdescent : baseEnd_3146098 < baseStart_3146098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146111 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_3146111 : Nat := 118140960795 + 3146111 * 2 ^ 59
def prefixEnd_3146111 : Nat := 4983230072969 + 3 ^ 40 * 3146111 * 2
def baseEnd_3146111 : Nat := 1076978090264963706629203

theorem tailTrace_3146111 : CollatzResearch.WordTrace tailWord_3146111 prefixEnd_3146111 1076978090264963706629203 := by
  unfold tailWord_3146111
  simp only [CollatzResearch.WordTrace]
  refine ⟨114748095105184634826238187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76498730070123089884158791 114748095105184634826238187)
  ·
    refine ⟨172122142657776952239357281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114748095105184634826238187 172122142657776952239357281)
    ·
      refine ⟨129091606993332714179517961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172122142657776952239357281 129091606993332714179517961)
      ·
        refine ⟨96818705244999535634638471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129091606993332714179517961 96818705244999535634638471)
        ·
          refine ⟨145228057867499303451957707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96818705244999535634638471 145228057867499303451957707)
          ·
            refine ⟨217842086801248955177936561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145228057867499303451957707 217842086801248955177936561)
            ·
              refine ⟨163381565100936716383452421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217842086801248955177936561 163381565100936716383452421)
              ·
                refine ⟨30634043456425634321897329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163381565100936716383452421 30634043456425634321897329)
                ·
                  refine ⟨22975532592319225741422997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30634043456425634321897329 22975532592319225741422997)
                  ·
                    refine ⟨1076978090264963706629203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22975532592319225741422997 1076978090264963706629203)
                    ·
                      rfl

theorem cell22_3146111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_3146111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146111 prefixEnd_3146111 := by exact prefixLift 3146111
  have htrace : WordTrace (prefixWord ++ tailWord_3146111) baseStart_3146111 baseEnd_3146111 := by
    simpa [prefixWord, tailWord_3146111, baseEnd_3146111] using wordTrace_append hprefix tailTrace_3146111
  have hstable : (prefixWord ++ tailWord_3146111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146111).length < 2 ^ (prefixWord ++ tailWord_3146111).sum := by decide
  have hdescent : baseEnd_3146111 < baseStart_3146111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146147 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 1, 3]
def baseStart_3146147 : Nat := 118140960795 + 3146147 * 2 ^ 59
def prefixEnd_3146147 : Nat := 4983230072969 + 3 ^ 40 * 3146147 * 2
def baseEnd_3146147 : Nat := 1076990413800671612729093

theorem tailTrace_3146147 : CollatzResearch.WordTrace tailWord_3146147 prefixEnd_3146147 1076990413800671612729093 := by
  unfold tailWord_3146147
  simp only [CollatzResearch.WordTrace]
  refine ⟨114749408133054212974548695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76499605422036141983032463 114749408133054212974548695)
  ·
    refine ⟨172124112199581319461823043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114749408133054212974548695 172124112199581319461823043)
    ·
      refine ⟨258186168299371979192734565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172124112199581319461823043 258186168299371979192734565)
      ·
        refine ⟨48409906556132246098637731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258186168299371979192734565 48409906556132246098637731)
        ·
          refine ⟨72614859834198369147956597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48409906556132246098637731 72614859834198369147956597)
          ·
            refine ⟨6807643109456097107620931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72614859834198369147956597 6807643109456097107620931)
            ·
              refine ⟨10211464664184145661431397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807643109456097107620931 10211464664184145661431397)
              ·
                refine ⟨1914649624534527311518387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10211464664184145661431397 1914649624534527311518387)
                ·
                  refine ⟨2871974436801790967277581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914649624534527311518387 2871974436801790967277581)
                  ·
                    refine ⟨1076990413800671612729093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871974436801790967277581 1076990413800671612729093)
                    ·
                      rfl

theorem cell22_3146147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 3].length) (baseStart_3146147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146147 prefixEnd_3146147 := by exact prefixLift 3146147
  have htrace : WordTrace (prefixWord ++ tailWord_3146147) baseStart_3146147 baseEnd_3146147 := by
    simpa [prefixWord, tailWord_3146147, baseEnd_3146147] using wordTrace_append hprefix tailTrace_3146147
  have hstable : (prefixWord ++ tailWord_3146147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146147).length < 2 ^ (prefixWord ++ tailWord_3146147).sum := by decide
  have hdescent : baseEnd_3146147 < baseStart_3146147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146194 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3146194 : Nat := 118140960795 + 3146194 * 2 ^ 59
def prefixEnd_3146194 : Nat := 4983230072969 + 3 ^ 40 * 3146194 * 2
def baseEnd_3146194 : Nat := 359002167620393052267983

theorem tailTrace_3146194 : CollatzResearch.WordTrace tailWord_3146194 prefixEnd_3146194 359002167620393052267983 := by
  unfold tailWord_3146194
  simp only [CollatzResearch.WordTrace]
  refine ⟨28687780590970985000377409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76500748242589293334339757 28687780590970985000377409)
  ·
    refine ⟨21515835443228238750283057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28687780590970985000377409 21515835443228238750283057)
    ·
      refine ⟨16136876582421179062712293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21515835443228238750283057 16136876582421179062712293)
      ·
        refine ⟨3025664359203971074258555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16136876582421179062712293 3025664359203971074258555)
        ·
          refine ⟨4538496538805956611387833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025664359203971074258555 4538496538805956611387833)
          ·
            refine ⟨3403872404104467458540875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4538496538805956611387833 3403872404104467458540875)
            ·
              refine ⟨5105808606156701187811313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403872404104467458540875 5105808606156701187811313)
              ·
                refine ⟨3829356454617525890858485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105808606156701187811313 3829356454617525890858485)
                ·
                  refine ⟨359002167620393052267983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3829356454617525890858485 359002167620393052267983)
                  ·
                    rfl

theorem cell22_3146194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3146194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146194 prefixEnd_3146194 := by exact prefixLift 3146194
  have htrace : WordTrace (prefixWord ++ tailWord_3146194) baseStart_3146194 baseEnd_3146194 := by
    simpa [prefixWord, tailWord_3146194, baseEnd_3146194] using wordTrace_append hprefix tailTrace_3146194
  have hstable : (prefixWord ++ tailWord_3146194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146194).length < 2 ^ (prefixWord ++ tailWord_3146194).sum := by decide
  have hdescent : baseEnd_3146194 < baseStart_3146194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146205 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 6]
def baseStart_3146205 : Nat := 118140960795 + 3146205 * 2 ^ 59
def prefixEnd_3146205 : Nat := 4983230072969 + 3 ^ 40 * 3146205 * 2
def baseEnd_3146205 : Nat := 359003422795326264926305

theorem tailTrace_3146205 : CollatzResearch.WordTrace tailWord_3146205 prefixEnd_3146205 359003422795326264926305 := by
  unfold tailWord_3146205
  simp only [CollatzResearch.WordTrace]
  refine ⟨114751523566844088880160069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76501015711229392586773379 114751523566844088880160069)
  ·
    refine ⟨21515910668783266665030013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114751523566844088880160069 21515910668783266665030013)
    ·
      refine ⟨8068466500793724999386255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21515910668783266665030013 8068466500793724999386255)
      ·
        refine ⟨12102699751190587499079383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8068466500793724999386255 12102699751190587499079383)
        ·
          refine ⟨18154049626785881248619075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12102699751190587499079383 18154049626785881248619075)
          ·
            refine ⟨27231074440178821872928613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18154049626785881248619075 27231074440178821872928613)
            ·
              refine ⟨5105826457533529101174115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27231074440178821872928613 5105826457533529101174115)
              ·
                refine ⟨7658739686300293651761173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105826457533529101174115 7658739686300293651761173)
                ·
                  refine ⟨359003422795326264926305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7658739686300293651761173 359003422795326264926305)
                  ·
                    rfl

theorem cell22_3146205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_3146205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146205 prefixEnd_3146205 := by exact prefixLift 3146205
  have htrace : WordTrace (prefixWord ++ tailWord_3146205) baseStart_3146205 baseEnd_3146205 := by
    simpa [prefixWord, tailWord_3146205, baseEnd_3146205] using wordTrace_append hprefix tailTrace_3146205
  have hstable : (prefixWord ++ tailWord_3146205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146205).length < 2 ^ (prefixWord ++ tailWord_3146205).sum := by decide
  have hdescent : baseEnd_3146205 < baseStart_3146205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146325 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3146325 : Nat := 118140960795 + 3146325 * 2 ^ 59
def prefixEnd_3146325 : Nat := 4983230072969 + 3 ^ 40 * 3146325 * 2
def baseEnd_3146325 : Nat := 1077051346838338481778547

theorem tailTrace_3146325 : CollatzResearch.WordTrace tailWord_3146325 prefixEnd_3146325 1077051346838338481778547 := by
  unfold tailWord_3146325
  simp only [CollatzResearch.WordTrace]
  refine ⟨114755900326409349374528429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76503933550939566249685619 114755900326409349374528429)
  ·
    refine ⟨43033462622403506015448161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114755900326409349374528429 43033462622403506015448161)
    ·
      refine ⟨32275096966802629511586121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43033462622403506015448161 32275096966802629511586121)
      ·
        refine ⟨24206322725101972133689591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32275096966802629511586121 24206322725101972133689591)
        ·
          refine ⟨36309484087652958200534387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24206322725101972133689591 36309484087652958200534387)
          ·
            refine ⟨54464226131479437300801581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36309484087652958200534387 54464226131479437300801581)
            ·
              refine ⟨20424084799304788987800593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54464226131479437300801581 20424084799304788987800593)
              ·
                refine ⟨15318063599478591740850445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20424084799304788987800593 15318063599478591740850445)
                ·
                  refine ⟨5744273849804471902818917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15318063599478591740850445 5744273849804471902818917)
                  ·
                    refine ⟨1077051346838338481778547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744273849804471902818917 1077051346838338481778547)
                    ·
                      rfl

theorem cell22_3146325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3146325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146325 prefixEnd_3146325 := by exact prefixLift 3146325
  have htrace : WordTrace (prefixWord ++ tailWord_3146325) baseStart_3146325 baseEnd_3146325 := by
    simpa [prefixWord, tailWord_3146325, baseEnd_3146325] using wordTrace_append hprefix tailTrace_3146325
  have hstable : (prefixWord ++ tailWord_3146325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146325).length < 2 ^ (prefixWord ++ tailWord_3146325).sum := by decide
  have hdescent : baseEnd_3146325 < baseStart_3146325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146340 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_3146340 : Nat := 118140960795 + 3146340 * 2 ^ 59
def prefixEnd_3146340 : Nat := 4983230072969 + 3 ^ 40 * 3146340 * 2
def baseEnd_3146340 : Nat := 359018827214961147551167

theorem tailTrace_3146340 : CollatzResearch.WordTrace tailWord_3146340 prefixEnd_3146340 359018827214961147551167 := by
  unfold tailWord_3146340
  simp only [CollatzResearch.WordTrace]
  refine ⟨57378223710677503468162237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76504298280903337957549649 57378223710677503468162237)
  ·
    refine ⟨21516833891504063800560839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57378223710677503468162237 21516833891504063800560839)
    ·
      refine ⟨32275250837256095700841259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21516833891504063800560839 32275250837256095700841259)
      ·
        refine ⟨48412876255884143551261889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32275250837256095700841259 48412876255884143551261889)
        ·
          refine ⟨36309657191913107663446417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48412876255884143551261889 36309657191913107663446417)
          ·
            refine ⟨27232242893934830747584813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36309657191913107663446417 27232242893934830747584813)
            ·
              refine ⟨10212091085225561530344305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27232242893934830747584813 10212091085225561530344305)
              ·
                refine ⟨7659068313919171147758229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212091085225561530344305 7659068313919171147758229)
                ·
                  refine ⟨359018827214961147551167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7659068313919171147758229 359018827214961147551167)
                  ·
                    rfl

theorem cell22_3146340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_3146340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146340 prefixEnd_3146340 := by exact prefixLift 3146340
  have htrace : WordTrace (prefixWord ++ tailWord_3146340) baseStart_3146340 baseEnd_3146340 := by
    simpa [prefixWord, tailWord_3146340, baseEnd_3146340] using wordTrace_append hprefix tailTrace_3146340
  have hstable : (prefixWord ++ tailWord_3146340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146340).length < 2 ^ (prefixWord ++ tailWord_3146340).sum := by decide
  have hdescent : baseEnd_3146340 < baseStart_3146340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146494 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3146494 : Nat := 118140960795 + 3146494 * 2 ^ 59
def prefixEnd_3146494 : Nat := 4983230072969 + 3 ^ 40 * 3146494 * 2
def baseEnd_3146494 : Nat := 1077109198992078374303029

theorem tailTrace_3146494 : CollatzResearch.WordTrace tailWord_3146494 prefixEnd_3146494 1077109198992078374303029 := by
  unfold tailWord_3146494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345258032849636404678817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76508042841864727491620357 14345258032849636404678817)
  ·
    refine ⟨10758943524637227303509113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14345258032849636404678817 10758943524637227303509113)
    ·
      refine ⟨8069207643477920477631835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10758943524637227303509113 8069207643477920477631835)
      ·
        refine ⟨12103811465216880716447753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069207643477920477631835 12103811465216880716447753)
        ·
          refine ⟨9077858598912660537335815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12103811465216880716447753 9077858598912660537335815)
          ·
            refine ⟨13616787898368990806003723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9077858598912660537335815 13616787898368990806003723)
            ·
              refine ⟨20425181847553486209005585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13616787898368990806003723 20425181847553486209005585)
              ·
                refine ⟨15318886385665114656754189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20425181847553486209005585 15318886385665114656754189)
                ·
                  refine ⟨5744582394624417996282821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15318886385665114656754189 5744582394624417996282821)
                  ·
                    refine ⟨1077109198992078374303029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744582394624417996282821 1077109198992078374303029)
                    ·
                      rfl

theorem cell22_3146494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3146494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146494 prefixEnd_3146494 := by exact prefixLift 3146494
  have htrace : WordTrace (prefixWord ++ tailWord_3146494) baseStart_3146494 baseEnd_3146494 := by
    simpa [prefixWord, tailWord_3146494, baseEnd_3146494] using wordTrace_append hprefix tailTrace_3146494
  have hstable : (prefixWord ++ tailWord_3146494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146494).length < 2 ^ (prefixWord ++ tailWord_3146494).sum := by decide
  have hdescent : baseEnd_3146494 < baseStart_3146494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146507 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 6, 3]
def baseStart_3146507 : Nat := 118140960795 + 3146507 * 2 ^ 59
def prefixEnd_3146507 : Nat := 4983230072969 + 3 ^ 40 * 3146507 * 2
def baseEnd_3146507 : Nat := 1077113649157750673727989

theorem tailTrace_3146507 : CollatzResearch.WordTrace tailWord_3146507 prefixEnd_3146507 1077113649157750673727989 := by
  unfold tailWord_3146507
  simp only [CollatzResearch.WordTrace]
  refine ⟨114762538411749994457653775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76508358941166662971769183 114762538411749994457653775)
  ·
    refine ⟨172143807617624991686480663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114762538411749994457653775 172143807617624991686480663)
    ·
      refine ⟨258215711426437487529720995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172143807617624991686480663 258215711426437487529720995)
      ·
        refine ⟨387323567139656231294581493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258215711426437487529720995 387323567139656231294581493)
        ·
          refine ⟨36311584419342771683867015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 387323567139656231294581493 36311584419342771683867015)
          ·
            refine ⟨54467376629014157525800523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36311584419342771683867015 54467376629014157525800523)
            ·
              refine ⟨81701064943521236288700785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54467376629014157525800523 81701064943521236288700785)
              ·
                refine ⟨61275798707640927216525589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81701064943521236288700785 61275798707640927216525589)
                ·
                  refine ⟨2872303064420668463274637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61275798707640927216525589 2872303064420668463274637)
                  ·
                    refine ⟨1077113649157750673727989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872303064420668463274637 1077113649157750673727989)
                    ·
                      rfl

theorem cell22_3146507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 3].length) (baseStart_3146507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146507 prefixEnd_3146507 := by exact prefixLift 3146507
  have htrace : WordTrace (prefixWord ++ tailWord_3146507) baseStart_3146507 baseEnd_3146507 := by
    simpa [prefixWord, tailWord_3146507, baseEnd_3146507] using wordTrace_append hprefix tailTrace_3146507
  have hstable : (prefixWord ++ tailWord_3146507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146507).length < 2 ^ (prefixWord ++ tailWord_3146507).sum := by decide
  have hdescent : baseEnd_3146507 < baseStart_3146507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146522 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_3146522 : Nat := 118140960795 + 3146522 * 2 ^ 59
def prefixEnd_3146522 : Nat := 4983230072969 + 3 ^ 40 * 3146522 * 2
def baseEnd_3146522 : Nat := 1077118783964295634602943

theorem tailTrace_3146522 : CollatzResearch.WordTrace tailWord_3146522 prefixEnd_3146522 1077118783964295634602943 := by
  unfold tailWord_3146522
  simp only [CollatzResearch.WordTrace]
  refine ⟨28690771376673913004862455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76508723671130434679633213 28690771376673913004862455)
  ·
    refine ⟨43036157065010869507293683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28690771376673913004862455 43036157065010869507293683)
    ·
      refine ⟨64554235597516304260940525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43036157065010869507293683 64554235597516304260940525)
      ·
        refine ⟨24207838349068614097852697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64554235597516304260940525 24207838349068614097852697)
        ·
          refine ⟨18155878761801460573389523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24207838349068614097852697 18155878761801460573389523)
          ·
            refine ⟨27233818142702190860084285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18155878761801460573389523 27233818142702190860084285)
            ·
              refine ⟨10212681803513321572531607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27233818142702190860084285 10212681803513321572531607)
              ·
                refine ⟨15319022705269982358797411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10212681803513321572531607 15319022705269982358797411)
                ·
                  refine ⟨22978534057904973538196117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15319022705269982358797411 22978534057904973538196117)
                  ·
                    refine ⟨1077118783964295634602943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22978534057904973538196117 1077118783964295634602943)
                    ·
                      rfl

theorem cell22_3146522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_3146522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146522 prefixEnd_3146522 := by exact prefixLift 3146522
  have htrace : WordTrace (prefixWord ++ tailWord_3146522) baseStart_3146522 baseEnd_3146522 := by
    simpa [prefixWord, tailWord_3146522, baseEnd_3146522] using wordTrace_append hprefix tailTrace_3146522
  have hstable : (prefixWord ++ tailWord_3146522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146522).length < 2 ^ (prefixWord ++ tailWord_3146522).sum := by decide
  have hdescent : baseEnd_3146522 < baseStart_3146522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146558 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3146558 : Nat := 118140960795 + 3146558 * 2 ^ 59
def prefixEnd_3146558 : Nat := 4983230072969 + 3 ^ 40 * 3146558 * 2
def baseEnd_3146558 : Nat := 1077131107500003540702833

theorem tailTrace_3146558 : CollatzResearch.WordTrace tailWord_3146558 prefixEnd_3146558 1077131107500003540702833 := by
  unfold tailWord_3146558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345549816820653770970041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76509599023043486778506885 14345549816820653770970041)
  ·
    refine ⟨10759162362615490328227531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14345549816820653770970041 10759162362615490328227531)
    ·
      refine ⟨16138743543923235492341297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759162362615490328227531 16138743543923235492341297)
      ·
        refine ⟨12104057657942426619255973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16138743543923235492341297 12104057657942426619255973)
        ·
          refine ⟨2269510810864204991110495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12104057657942426619255973 2269510810864204991110495)
          ·
            refine ⟨3404266216296307486665743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269510810864204991110495 3404266216296307486665743)
            ·
              refine ⟨5106399324444461229998615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404266216296307486665743 5106399324444461229998615)
              ·
                refine ⟨7659598986666691844997923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106399324444461229998615 7659598986666691844997923)
                ·
                  refine ⟨11489398480000037767496885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659598986666691844997923 11489398480000037767496885)
                  ·
                    refine ⟨1077131107500003540702833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11489398480000037767496885 1077131107500003540702833)
                    ·
                      rfl

theorem cell22_3146558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3146558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146558 prefixEnd_3146558 := by exact prefixLift 3146558
  have htrace : WordTrace (prefixWord ++ tailWord_3146558) baseStart_3146558 baseEnd_3146558 := by
    simpa [prefixWord, tailWord_3146558, baseEnd_3146558] using wordTrace_append hprefix tailTrace_3146558
  have hstable : (prefixWord ++ tailWord_3146558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146558).length < 2 ^ (prefixWord ++ tailWord_3146558).sum := by decide
  have hdescent : baseEnd_3146558 < baseStart_3146558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146569 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_3146569 : Nat := 118140960795 + 3146569 * 2 ^ 59
def prefixEnd_3146569 : Nat := 4983230072969 + 3 ^ 40 * 3146569 * 2
def baseEnd_3146569 : Nat := 1077134873024803178677799

theorem tailTrace_3146569 : CollatzResearch.WordTrace tailWord_3146569 prefixEnd_3146569 1077134873024803178677799 := by
  unfold tailWord_3146569
  simp only [CollatzResearch.WordTrace]
  refine ⟨114764799737525379046410761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76509866491683586030940507 114764799737525379046410761)
  ·
    refine ⟨86073599803144034284808071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114764799737525379046410761 86073599803144034284808071)
    ·
      refine ⟨129110399704716051427212107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86073599803144034284808071 129110399704716051427212107)
      ·
        refine ⟨193665599557074077140818161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129110399704716051427212107 193665599557074077140818161)
        ·
          refine ⟨145249199667805557855613621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193665599557074077140818161 145249199667805557855613621)
          ·
            refine ⟨13617112468856771048963777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145249199667805557855613621 13617112468856771048963777)
            ·
              refine ⟨10212834351642578286722833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13617112468856771048963777 10212834351642578286722833)
              ·
                refine ⟨7659625763731933715042125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212834351642578286722833 7659625763731933715042125)
                ·
                  refine ⟨2872359661399475143140797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7659625763731933715042125 2872359661399475143140797)
                  ·
                    refine ⟨1077134873024803178677799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872359661399475143140797 1077134873024803178677799)
                    ·
                      rfl

theorem cell22_3146569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_3146569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146569 prefixEnd_3146569 := by exact prefixLift 3146569
  have htrace : WordTrace (prefixWord ++ tailWord_3146569) baseStart_3146569 baseEnd_3146569 := by
    simpa [prefixWord, tailWord_3146569, baseEnd_3146569] using wordTrace_append hprefix tailTrace_3146569
  have hstable : (prefixWord ++ tailWord_3146569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146569).length < 2 ^ (prefixWord ++ tailWord_3146569).sum := by decide
  have hdescent : baseEnd_3146569 < baseStart_3146569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146597 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_3146597 : Nat := 118140960795 + 3146597 * 2 ^ 59
def prefixEnd_3146597 : Nat := 4983230072969 + 3 ^ 40 * 3146597 * 2
def baseEnd_3146597 : Nat := 1077144457997020438977713

theorem tailTrace_3146597 : CollatzResearch.WordTrace tailWord_3146597 prefixEnd_3146597 1077144457997020438977713 := by
  unfold tailWord_3146597
  simp only [CollatzResearch.WordTrace]
  refine ⟨114765820981423939828430045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76510547320949293218953363 114765820981423939828430045)
  ·
    refine ⟨43037182868033977435661267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114765820981423939828430045 43037182868033977435661267)
    ·
      refine ⟨64555774302050966153491901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43037182868033977435661267 64555774302050966153491901)
      ·
        refine ⟨24208415363269112307559463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64555774302050966153491901 24208415363269112307559463)
        ·
          refine ⟨36312623044903668461339195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24208415363269112307559463 36312623044903668461339195)
          ·
            refine ⟨54468934567355502692008793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36312623044903668461339195 54468934567355502692008793)
            ·
              refine ⟨40851700925516627019006595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54468934567355502692008793 40851700925516627019006595)
              ·
                refine ⟨61277551388274940528509893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40851700925516627019006595 61277551388274940528509893)
                ·
                  refine ⟨11489540885301551349095605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61277551388274940528509893 11489540885301551349095605)
                  ·
                    refine ⟨1077144457997020438977713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11489540885301551349095605 1077144457997020438977713)
                    ·
                      rfl

theorem cell22_3146597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_3146597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146597 prefixEnd_3146597 := by exact prefixLift 3146597
  have htrace : WordTrace (prefixWord ++ tailWord_3146597) baseStart_3146597 baseEnd_3146597 := by
    simpa [prefixWord, tailWord_3146597, baseEnd_3146597] using wordTrace_append hprefix tailTrace_3146597
  have hstable : (prefixWord ++ tailWord_3146597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146597).length < 2 ^ (prefixWord ++ tailWord_3146597).sum := by decide
  have hdescent : baseEnd_3146597 < baseStart_3146597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146627 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 8]
def baseStart_3146627 : Nat := 118140960795 + 3146627 * 2 ^ 59
def prefixEnd_3146627 : Nat := 4983230072969 + 3 ^ 40 * 3146627 * 2
def baseEnd_3146627 : Nat := 359051575870036786909207

theorem tailTrace_3146627 : CollatzResearch.WordTrace tailWord_3146627 prefixEnd_3146627 359051575870036786909207 := by
  unfold tailWord_3146627
  simp only [CollatzResearch.WordTrace]
  refine ⟨114766915171315254952022135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76511276780876836634681423 114766915171315254952022135)
  ·
    refine ⟨172150372756972882428033203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114766915171315254952022135 172150372756972882428033203)
    ·
      refine ⟨258225559135459323642049805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172150372756972882428033203 258225559135459323642049805)
      ·
        refine ⟨96834584675797246365768677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258225559135459323642049805 96834584675797246365768677)
        ·
          refine ⟨18156484626711983693581627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96834584675797246365768677 18156484626711983693581627)
          ·
            refine ⟨27234726940067975540372441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18156484626711983693581627 27234726940067975540372441)
            ·
              refine ⟨20426045205050981655279331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27234726940067975540372441 20426045205050981655279331)
              ·
                refine ⟨30639067807576472482918997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20426045205050981655279331 30639067807576472482918997)
                ·
                  refine ⟨359051575870036786909207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30639067807576472482918997 359051575870036786909207)
                  ·
                    rfl

theorem cell22_3146627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_3146627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146627 prefixEnd_3146627 := by exact prefixLift 3146627
  have htrace : WordTrace (prefixWord ++ tailWord_3146627) baseStart_3146627 baseEnd_3146627 := by
    simpa [prefixWord, tailWord_3146627, baseEnd_3146627] using wordTrace_append hprefix tailTrace_3146627
  have hstable : (prefixWord ++ tailWord_3146627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146627).length < 2 ^ (prefixWord ++ tailWord_3146627).sum := by decide
  have hdescent : baseEnd_3146627 < baseStart_3146627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146629 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_3146629 : Nat := 118140960795 + 3146629 * 2 ^ 59
def prefixEnd_3146629 : Nat := 4983230072969 + 3 ^ 40 * 3146629 * 2
def baseEnd_3146629 : Nat := 1077155412250983022177615

theorem tailTrace_3146629 : CollatzResearch.WordTrace tailWord_3146629 prefixEnd_3146629 1077155412250983022177615 := by
  unfold tailWord_3146629
  simp only [CollatzResearch.WordTrace]
  refine ⟨114766988117308009293594941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76511325411538672862396627 114766988117308009293594941)
  ·
    refine ⟨43037620543990503485098103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114766988117308009293594941 43037620543990503485098103)
    ·
      refine ⟨64556430815985755227647155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43037620543990503485098103 64556430815985755227647155)
      ·
        refine ⟨96834646223978632841470733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64556430815985755227647155 96834646223978632841470733)
        ·
          refine ⟨36312992333991987315551525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96834646223978632841470733 36312992333991987315551525)
          ·
            refine ⟨6808686062623497621665911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36312992333991987315551525 6808686062623497621665911)
            ·
              refine ⟨10213029093935246432498867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808686062623497621665911 10213029093935246432498867)
              ·
                refine ⟨15319543640902869648748301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10213029093935246432498867 15319543640902869648748301)
                ·
                  refine ⟨5744828865338576118280613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15319543640902869648748301 5744828865338576118280613)
                  ·
                    refine ⟨1077155412250983022177615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744828865338576118280613 1077155412250983022177615)
                    ·
                      rfl

theorem cell22_3146629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_3146629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146629 prefixEnd_3146629 := by exact prefixLift 3146629
  have htrace : WordTrace (prefixWord ++ tailWord_3146629) baseStart_3146629 baseEnd_3146629 := by
    simpa [prefixWord, tailWord_3146629, baseEnd_3146629] using wordTrace_append hprefix tailTrace_3146629
  have hstable : (prefixWord ++ tailWord_3146629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146629).length < 2 ^ (prefixWord ++ tailWord_3146629).sum := by decide
  have hdescent : baseEnd_3146629 < baseStart_3146629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146659 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 4, 3]
def baseStart_3146659 : Nat := 118140960795 + 3146659 * 2 ^ 59
def prefixEnd_3146659 : Nat := 4983230072969 + 3 ^ 40 * 3146659 * 2
def baseEnd_3146659 : Nat := 1077165681864072943927523

theorem tailTrace_3146659 : CollatzResearch.WordTrace tailWord_3146659 prefixEnd_3146659 1077165681864072943927523 := by
  unfold tailWord_3146659
  simp only [CollatzResearch.WordTrace]
  refine ⟨114768082307199324417187031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76512054871466216278124687 114768082307199324417187031)
  ·
    refine ⟨172152123460798986625780547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114768082307199324417187031 172152123460798986625780547)
    ·
      refine ⟨258228185191198479938670821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172152123460798986625780547 258228185191198479938670821)
      ·
        refine ⟨48417784723349714988500779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258228185191198479938670821 48417784723349714988500779)
        ·
          refine ⟨72626677085024572482751169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48417784723349714988500779 72626677085024572482751169)
          ·
            refine ⟨54470007813768429362063377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72626677085024572482751169 54470007813768429362063377)
            ·
              refine ⟨40852505860326322021547533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54470007813768429362063377 40852505860326322021547533)
              ·
                refine ⟨15319689697622370758080325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40852505860326322021547533 15319689697622370758080325)
                ·
                  refine ⟨2872441818304194517140061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15319689697622370758080325 2872441818304194517140061)
                  ·
                    refine ⟨1077165681864072943927523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872441818304194517140061 1077165681864072943927523)
                    ·
                      rfl

theorem cell22_3146659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 3].length) (baseStart_3146659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146659 prefixEnd_3146659 := by exact prefixLift 3146659
  have htrace : WordTrace (prefixWord ++ tailWord_3146659) baseStart_3146659 baseEnd_3146659 := by
    simpa [prefixWord, tailWord_3146659, baseEnd_3146659] using wordTrace_append hprefix tailTrace_3146659
  have hstable : (prefixWord ++ tailWord_3146659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146659).length < 2 ^ (prefixWord ++ tailWord_3146659).sum := by decide
  have hdescent : baseEnd_3146659 < baseStart_3146659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146687 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_3146687 : Nat := 118140960795 + 3146687 * 2 ^ 59
def prefixEnd_3146687 : Nat := 4983230072969 + 3 ^ 40 * 3146687 * 2
def baseEnd_3146687 : Nat := 1077175266836290204227437

theorem tailTrace_3146687 : CollatzResearch.WordTrace tailWord_3146687 prefixEnd_3146687 1077175266836290204227437 := by
  unfold tailWord_3146687
  simp only [CollatzResearch.WordTrace]
  refine ⟨114769103551097885199206315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76512735700731923466137543 114769103551097885199206315)
  ·
    refine ⟨172153655326646827798809473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114769103551097885199206315 172153655326646827798809473)
    ·
      refine ⟨129115241494985120849107105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172153655326646827798809473 129115241494985120849107105)
      ·
        refine ⟨96836431121238840636830329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129115241494985120849107105 96836431121238840636830329)
        ·
          refine ⟨72627323340929130477622747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96836431121238840636830329 72627323340929130477622747)
          ·
            refine ⟨108940985011393695716434121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72627323340929130477622747 108940985011393695716434121)
            ·
              refine ⟨81705738758545271787325591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108940985011393695716434121 81705738758545271787325591)
              ·
                refine ⟨122558608137817907680988387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81705738758545271787325591 122558608137817907680988387)
                ·
                  refine ⟨183837912206726861521482581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122558608137817907680988387 183837912206726861521482581)
                  ·
                    refine ⟨1077175266836290204227437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 183837912206726861521482581 1077175266836290204227437)
                    ·
                      rfl

theorem cell22_3146687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_3146687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146687 prefixEnd_3146687 := by exact prefixLift 3146687
  have htrace : WordTrace (prefixWord ++ tailWord_3146687) baseStart_3146687 baseEnd_3146687 := by
    simpa [prefixWord, tailWord_3146687, baseEnd_3146687] using wordTrace_append hprefix tailTrace_3146687
  have hstable : (prefixWord ++ tailWord_3146687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146687).length < 2 ^ (prefixWord ++ tailWord_3146687).sum := by decide
  have hdescent : baseEnd_3146687 < baseStart_3146687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146704 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_3146704 : Nat := 118140960795 + 3146704 * 2 ^ 59
def prefixEnd_3146704 : Nat := 4983230072969 + 3 ^ 40 * 3146704 * 2
def baseEnd_3146704 : Nat := 1077181086283707826552385

theorem tailTrace_3146704 : CollatzResearch.WordTrace tailWord_3146704 prefixEnd_3146704 1077181086283707826552385 := by
  unfold tailWord_3146704
  simp only [CollatzResearch.WordTrace]
  refine ⟨57384861796018148551287583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76513149061357531401716777 57384861796018148551287583)
  ·
    refine ⟨86077292694027222826931375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57384861796018148551287583 86077292694027222826931375)
    ·
      refine ⟨129115939041040834240397063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86077292694027222826931375 129115939041040834240397063)
      ·
        refine ⟨193673908561561251360595595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129115939041040834240397063 193673908561561251360595595)
        ·
          refine ⟨290510862842341877040893393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193673908561561251360595595 290510862842341877040893393)
          ·
            refine ⟨217883147131756407780670045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290510862842341877040893393 217883147131756407780670045)
            ·
              refine ⟨81706180174408652917751267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217883147131756407780670045 81706180174408652917751267)
              ·
                refine ⟨122559270261612979376626901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81706180174408652917751267 122559270261612979376626901)
                ·
                  refine ⟨2872482896756554204139693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 122559270261612979376626901 2872482896756554204139693)
                  ·
                    refine ⟨1077181086283707826552385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872482896756554204139693 1077181086283707826552385)
                    ·
                      rfl

theorem cell22_3146704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_3146704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146704 prefixEnd_3146704 := by exact prefixLift 3146704
  have htrace : WordTrace (prefixWord ++ tailWord_3146704) baseStart_3146704 baseEnd_3146704 := by
    simpa [prefixWord, tailWord_3146704, baseEnd_3146704] using wordTrace_append hprefix tailTrace_3146704
  have hstable : (prefixWord ++ tailWord_3146704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146704).length < 2 ^ (prefixWord ++ tailWord_3146704).sum := by decide
  have hdescent : baseEnd_3146704 < baseStart_3146704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146710 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3146710 : Nat := 118140960795 + 3146710 * 2 ^ 59
def prefixEnd_3146710 : Nat := 4983230072969 + 3 ^ 40 * 3146710 * 2
def baseEnd_3146710 : Nat := 1077183140206325810902367

theorem tailTrace_3146710 : CollatzResearch.WordTrace tailWord_3146710 prefixEnd_3146710 1077183140206325810902367 := by
  unfold tailWord_3146710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173121401875910007955849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76513294953343040084862389 7173121401875910007955849)
  ·
    refine ⟨5379841051406932505966887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7173121401875910007955849 5379841051406932505966887)
    ·
      refine ⟨8069761577110398758950331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379841051406932505966887 8069761577110398758950331)
      ·
        refine ⟨12104642365665598138425497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069761577110398758950331 12104642365665598138425497)
        ·
          refine ⟨9078481774249198603819123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12104642365665598138425497 9078481774249198603819123)
          ·
            refine ⟨13617722661373797905728685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9078481774249198603819123 13617722661373797905728685)
            ·
              refine ⟨5106645998015174214648257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13617722661373797905728685 5106645998015174214648257)
              ·
                refine ⟨3829984498511380660986193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106645998015174214648257 3829984498511380660986193)
                ·
                  refine ⟨2872488373883535495739645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3829984498511380660986193 2872488373883535495739645)
                  ·
                    refine ⟨1077183140206325810902367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872488373883535495739645 1077183140206325810902367)
                    ·
                      rfl

theorem cell22_3146710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3146710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146710 prefixEnd_3146710 := by exact prefixLift 3146710
  have htrace : WordTrace (prefixWord ++ tailWord_3146710) baseStart_3146710 baseEnd_3146710 := by
    simpa [prefixWord, tailWord_3146710, baseEnd_3146710] using wordTrace_append hprefix tailTrace_3146710
  have hstable : (prefixWord ++ tailWord_3146710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146710).length < 2 ^ (prefixWord ++ tailWord_3146710).sum := by decide
  have hdescent : baseEnd_3146710 < baseStart_3146710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146826 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_3146826 : Nat := 118140960795 + 3146826 * 2 ^ 59
def prefixEnd_3146826 : Nat := 4983230072969 + 3 ^ 40 * 3146826 * 2
def baseEnd_3146826 : Nat := 1077222849376940175002011

theorem tailTrace_3146826 : CollatzResearch.WordTrace tailWord_3146826 prefixEnd_3146826 1077222849376940175002011 := by
  unfold tailWord_3146826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28693543324398577984629083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76516115531729541292344221 28693543324398577984629083)
  ·
    refine ⟨43040314986597866976943625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28693543324398577984629083 43040314986597866976943625)
    ·
      refine ⟨32280236239948400232707719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43040314986597866976943625 32280236239948400232707719)
      ·
        refine ⟨48420354359922600349061579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32280236239948400232707719 48420354359922600349061579)
        ·
          refine ⟨72630531539883900523592369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48420354359922600349061579 72630531539883900523592369)
          ·
            refine ⟨54472898654912925392694277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72630531539883900523592369 54472898654912925392694277)
            ·
              refine ⟨10213668497796173511130177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54472898654912925392694277 10213668497796173511130177)
              ·
                refine ⟨7660251373347130133347633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10213668497796173511130177 7660251373347130133347633)
                ·
                  refine ⟨5745188530010347600010725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7660251373347130133347633 5745188530010347600010725)
                  ·
                    refine ⟨1077222849376940175002011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5745188530010347600010725 1077222849376940175002011)
                    ·
                      rfl

theorem cell22_3146826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_3146826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146826 prefixEnd_3146826 := by exact prefixLift 3146826
  have htrace : WordTrace (prefixWord ++ tailWord_3146826) baseStart_3146826 baseEnd_3146826 := by
    simpa [prefixWord, tailWord_3146826, baseEnd_3146826] using wordTrace_append hprefix tailTrace_3146826
  have hstable : (prefixWord ++ tailWord_3146826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146826).length < 2 ^ (prefixWord ++ tailWord_3146826).sum := by decide
  have hdescent : baseEnd_3146826 < baseStart_3146826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146839 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3146839 : Nat := 118140960795 + 3146839 * 2 ^ 59
def prefixEnd_3146839 : Nat := 4983230072969 + 3 ^ 40 * 3146839 * 2
def baseEnd_3146839 : Nat := 1077227299542612474426971

theorem tailTrace_3146839 : CollatzResearch.WordTrace tailWord_3146839 prefixEnd_3146839 1077227299542612474426971 := by
  unfold tailWord_3146839
  simp only [CollatzResearch.WordTrace]
  refine ⟨114774647446547215158739571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76516431631031476772493047 114774647446547215158739571)
  ·
    refine ⟨172161971169820822738109357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114774647446547215158739571 172161971169820822738109357)
    ·
      refine ⟨64560739188682808526791009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172161971169820822738109357 64560739188682808526791009)
      ·
        refine ⟨48420554391512106395093257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64560739188682808526791009 48420554391512106395093257)
        ·
          refine ⟨36315415793634079796319943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48420554391512106395093257 36315415793634079796319943)
          ·
            refine ⟨54473123690451119694479915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36315415793634079796319943 54473123690451119694479915)
            ·
              refine ⟨81709685535676679541719873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54473123690451119694479915 81709685535676679541719873)
              ·
                refine ⟨61282264151757509656289905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81709685535676679541719873 61282264151757509656289905)
                ·
                  refine ⟨45961698113818132242217429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61282264151757509656289905 45961698113818132242217429)
                  ·
                    refine ⟨1077227299542612474426971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45961698113818132242217429 1077227299542612474426971)
                    ·
                      rfl

theorem cell22_3146839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3146839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146839 prefixEnd_3146839 := by exact prefixLift 3146839
  have htrace : WordTrace (prefixWord ++ tailWord_3146839) baseStart_3146839 baseEnd_3146839 := by
    simpa [prefixWord, tailWord_3146839, baseEnd_3146839] using wordTrace_append hprefix tailTrace_3146839
  have hstable : (prefixWord ++ tailWord_3146839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146839).length < 2 ^ (prefixWord ++ tailWord_3146839).sum := by decide
  have hdescent : baseEnd_3146839 < baseStart_3146839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146845 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3146845 : Nat := 118140960795 + 3146845 * 2 ^ 59
def prefixEnd_3146845 : Nat := 4983230072969 + 3 ^ 40 * 3146845 * 2
def baseEnd_3146845 : Nat := 1077229353465230458776953

theorem tailTrace_3146845 : CollatzResearch.WordTrace tailWord_3146845 prefixEnd_3146845 1077229353465230458776953 := by
  unfold tailWord_3146845
  simp only [CollatzResearch.WordTrace]
  refine ⟨114774866284525478183457989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76516577523016985455638659 114774866284525478183457989)
  ·
    refine ⟨21520287428348527159398373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114774866284525478183457989 21520287428348527159398373)
    ·
      refine ⟨4035053892815348842387195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21520287428348527159398373 4035053892815348842387195)
      ·
        refine ⟨6052580839223023263580793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035053892815348842387195 6052580839223023263580793)
        ·
          refine ⟨4539435629417267447685595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6052580839223023263580793 4539435629417267447685595)
          ·
            refine ⟨6809153444125901171528393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539435629417267447685595 6809153444125901171528393)
            ·
              refine ⟨5106865083094425878646295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6809153444125901171528393 5106865083094425878646295)
              ·
                refine ⟨7660297624641638817969443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106865083094425878646295 7660297624641638817969443)
                ·
                  refine ⟨11490446436962458226954165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660297624641638817969443 11490446436962458226954165)
                  ·
                    refine ⟨1077229353465230458776953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11490446436962458226954165 1077229353465230458776953)
                    ·
                      rfl

theorem cell22_3146845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3146845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146845 prefixEnd_3146845 := by exact prefixLift 3146845
  have htrace : WordTrace (prefixWord ++ tailWord_3146845) baseStart_3146845 baseEnd_3146845 := by
    simpa [prefixWord, tailWord_3146845, baseEnd_3146845] using wordTrace_append hprefix tailTrace_3146845
  have hstable : (prefixWord ++ tailWord_3146845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146845).length < 2 ^ (prefixWord ++ tailWord_3146845).sum := by decide
  have hdescent : baseEnd_3146845 < baseStart_3146845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146858 : List Nat := [3, 1, 3, 2, 2, 2, 3, 6]
def baseStart_3146858 : Nat := 118140960795 + 3146858 * 2 ^ 59
def prefixEnd_3146858 : Nat := 4983230072969 + 3 ^ 40 * 3146858 * 2
def baseEnd_3146858 : Nat := 119692644847878084244657

theorem tailTrace_3146858 : CollatzResearch.WordTrace tailWord_3146858 prefixEnd_3146858 119692644847878084244657 := by
  unfold tailWord_3146858
  simp only [CollatzResearch.WordTrace]
  refine ⟨28693835108369595350920307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76516893622318920935787485 28693835108369595350920307)
  ·
    refine ⟨43040752662554393026380461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28693835108369595350920307 43040752662554393026380461)
    ·
      refine ⟨16140282248457897384892673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43040752662554393026380461 16140282248457897384892673)
      ·
        refine ⟨12105211686343423038669505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16140282248457897384892673 12105211686343423038669505)
        ·
          refine ⟨9078908764757567279002129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12105211686343423038669505 9078908764757567279002129)
          ·
            refine ⟨6809181573568175459251597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9078908764757567279002129 6809181573568175459251597)
            ·
              refine ⟨2553443090088065797219349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6809181573568175459251597 2553443090088065797219349)
              ·
                refine ⟨119692644847878084244657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2553443090088065797219349 119692644847878084244657)
                ·
                  rfl

theorem cell22_3146858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_3146858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146858 prefixEnd_3146858 := by exact prefixLift 3146858
  have htrace : WordTrace (prefixWord ++ tailWord_3146858) baseStart_3146858 baseEnd_3146858 := by
    simpa [prefixWord, tailWord_3146858, baseEnd_3146858] using wordTrace_append hprefix tailTrace_3146858
  have hstable : (prefixWord ++ tailWord_3146858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146858).length < 2 ^ (prefixWord ++ tailWord_3146858).sum := by decide
  have hdescent : baseEnd_3146858 < baseStart_3146858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146890 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_3146890 : Nat := 118140960795 + 3146890 * 2 ^ 59
def prefixEnd_3146890 : Nat := 4983230072969 + 3 ^ 40 * 3146890 * 2
def baseEnd_3146890 : Nat := 1077244757884865341401815

theorem tailTrace_3146890 : CollatzResearch.WordTrace tailWord_3146890 prefixEnd_3146890 1077244757884865341401815 := by
  unfold tailWord_3146890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28694126892340612717211531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76517671712908300579230749 28694126892340612717211531)
  ·
    refine ⟨43041190338510919075817297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28694126892340612717211531 43041190338510919075817297)
    ·
      refine ⟨32280892753883189306862973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43041190338510919075817297 32280892753883189306862973)
      ·
        refine ⟨12105334782706195990073615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32280892753883189306862973 12105334782706195990073615)
        ·
          refine ⟨18158002174059293985110423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12105334782706195990073615 18158002174059293985110423)
          ·
            refine ⟨27237003261088940977665635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18158002174059293985110423 27237003261088940977665635)
            ·
              refine ⟨40855504891633411466498453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27237003261088940977665635 40855504891633411466498453)
              ·
                refine ⟨1915101791795316162492115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40855504891633411466498453 1915101791795316162492115)
                ·
                  refine ⟨2872652687692974243738173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915101791795316162492115 2872652687692974243738173)
                  ·
                    refine ⟨1077244757884865341401815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872652687692974243738173 1077244757884865341401815)
                    ·
                      rfl

theorem cell22_3146890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_3146890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146890 prefixEnd_3146890 := by exact prefixLift 3146890
  have htrace : WordTrace (prefixWord ++ tailWord_3146890) baseStart_3146890 baseEnd_3146890 := by
    simpa [prefixWord, tailWord_3146890, baseEnd_3146890] using wordTrace_append hprefix tailTrace_3146890
  have hstable : (prefixWord ++ tailWord_3146890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146890).length < 2 ^ (prefixWord ++ tailWord_3146890).sum := by decide
  have hdescent : baseEnd_3146890 < baseStart_3146890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146961 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3146961 : Nat := 118140960795 + 3146961 * 2 ^ 59
def prefixEnd_3146961 : Nat := 4983230072969 + 3 ^ 40 * 3146961 * 2
def baseEnd_3146961 : Nat := 1077269062635844822876597

theorem tailTrace_3146961 : CollatzResearch.WordTrace tailWord_3146961 prefixEnd_3146961 1077269062635844822876597 := by
  unfold tailWord_3146961
  simp only [CollatzResearch.WordTrace]
  refine ⟨114779097152105229994680737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76519398101403486663120491 114779097152105229994680737)
  ·
    refine ⟨86084322864078922496010553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114779097152105229994680737 86084322864078922496010553)
    ·
      refine ⟨64563242148059191872007915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86084322864078922496010553 64563242148059191872007915)
      ·
        refine ⟨96844863222088787808011873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64563242148059191872007915 96844863222088787808011873)
        ·
          refine ⟨72633647416566590856008905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96844863222088787808011873 72633647416566590856008905)
          ·
            refine ⟨54475235562424943142006679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72633647416566590856008905 54475235562424943142006679)
            ·
              refine ⟨81712853343637414713010019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54475235562424943142006679 81712853343637414713010019)
              ·
                refine ⟨122569280015456122069515029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81712853343637414713010019 122569280015456122069515029)
                ·
                  refine ⟨5745435000724505722008517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122569280015456122069515029 5745435000724505722008517)
                  ·
                    refine ⟨1077269062635844822876597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5745435000724505722008517 1077269062635844822876597)
                    ·
                      rfl

theorem cell22_3146961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3146961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146961 prefixEnd_3146961 := by exact prefixLift 3146961
  have htrace : WordTrace (prefixWord ++ tailWord_3146961) baseStart_3146961 baseEnd_3146961 := by
    simpa [prefixWord, tailWord_3146961, baseEnd_3146961] using wordTrace_append hprefix tailTrace_3146961
  have hstable : (prefixWord ++ tailWord_3146961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146961).length < 2 ^ (prefixWord ++ tailWord_3146961).sum := by decide
  have hdescent : baseEnd_3146961 < baseStart_3146961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146963 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 2, 3]
def baseStart_3146963 : Nat := 118140960795 + 3146963 * 2 ^ 59
def prefixEnd_3146963 : Nat := 4983230072969 + 3 ^ 40 * 3146963 * 2
def baseEnd_3146963 : Nat := 1077269747276717484326591

theorem tailTrace_3146963 : CollatzResearch.WordTrace tailWord_3146963 prefixEnd_3146963 1077269747276717484326591 := by
  unfold tailWord_3146963
  simp only [CollatzResearch.WordTrace]
  refine ⟨114779170098097984336253543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76519446732065322890835695 114779170098097984336253543)
  ·
    refine ⟨172168755147146976504380315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114779170098097984336253543 172168755147146976504380315)
    ·
      refine ⟨258253132720720464756570473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172168755147146976504380315 258253132720720464756570473)
      ·
        refine ⟨193689849540540348567427855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258253132720720464756570473 193689849540540348567427855)
        ·
          refine ⟨290534774310810522851141783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193689849540540348567427855 290534774310810522851141783)
          ·
            refine ⟨435802161466215784276712675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290534774310810522851141783 435802161466215784276712675)
            ·
              refine ⟨653703242199323676415069013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435802161466215784276712675 653703242199323676415069013)
              ·
                refine ⟨3830292434761662166494545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 653703242199323676415069013 3830292434761662166494545)
                ·
                  refine ⟨2872719326071246624870909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830292434761662166494545 2872719326071246624870909)
                  ·
                    refine ⟨1077269747276717484326591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872719326071246624870909 1077269747276717484326591)
                    ·
                      rfl

theorem cell22_3146963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 3].length) (baseStart_3146963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146963 prefixEnd_3146963 := by exact prefixLift 3146963
  have htrace : WordTrace (prefixWord ++ tailWord_3146963) baseStart_3146963 baseEnd_3146963 := by
    simpa [prefixWord, tailWord_3146963, baseEnd_3146963] using wordTrace_append hprefix tailTrace_3146963
  have hstable : (prefixWord ++ tailWord_3146963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146963).length < 2 ^ (prefixWord ++ tailWord_3146963).sum := by decide
  have hdescent : baseEnd_3146963 < baseStart_3146963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146976 : List Nat := [2, 1, 1, 3, 1, 4, 2, 8]
def baseStart_3146976 : Nat := 118140960795 + 3146976 * 2 ^ 59
def prefixEnd_3146976 : Nat := 4983230072969 + 3 ^ 40 * 3146976 * 2
def baseEnd_3146976 : Nat := 119697133049154420416839

theorem tailTrace_3146976 : CollatzResearch.WordTrace tailWord_3146976 prefixEnd_3146976 119697133049154420416839 := by
  unfold tailWord_3146976
  simp only [CollatzResearch.WordTrace]
  refine ⟨57389822123525443778238391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76519762831367258370984521 57389822123525443778238391)
  ·
    refine ⟨86084733185288165667357587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57389822123525443778238391 86084733185288165667357587)
    ·
      refine ⟨129127099777932248501036381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86084733185288165667357587 129127099777932248501036381)
      ·
        refine ⟨48422662416724593187888643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129127099777932248501036381 48422662416724593187888643)
        ·
          refine ⟨72633993625086889781832965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48422662416724593187888643 72633993625086889781832965)
          ·
            refine ⟨13618873804703791834093681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72633993625086889781832965 13618873804703791834093681)
            ·
              refine ⟨10214155353527843875570261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13618873804703791834093681 10214155353527843875570261)
              ·
                refine ⟨119697133049154420416839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10214155353527843875570261 119697133049154420416839)
                ·
                  rfl

theorem cell22_3146976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_3146976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3146976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3146976 prefixEnd_3146976 := by exact prefixLift 3146976
  have htrace : WordTrace (prefixWord ++ tailWord_3146976) baseStart_3146976 baseEnd_3146976 := by
    simpa [prefixWord, tailWord_3146976, baseEnd_3146976] using wordTrace_append hprefix tailTrace_3146976
  have hstable : (prefixWord ++ tailWord_3146976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146976).length < 2 ^ (prefixWord ++ tailWord_3146976).sum := by decide
  have hdescent : baseEnd_3146976 < baseStart_3146976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147008 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_3147008 : Nat := 118140960795 + 3147008 * 2 ^ 59
def prefixEnd_3147008 : Nat := 4983230072969 + 3 ^ 40 * 3147008 * 2
def baseEnd_3147008 : Nat := 1077285151696352366951453

theorem tailTrace_3147008 : CollatzResearch.WordTrace tailWord_3147008 prefixEnd_3147008 1077285151696352366951453 := by
  unfold tailWord_3147008
  simp only [CollatzResearch.WordTrace]
  refine ⟨57390405691467478510820839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76520540921956638014427785 57390405691467478510820839)
  ·
    refine ⟨86085608537201217766231259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57390405691467478510820839 86085608537201217766231259)
    ·
      refine ⟨129128412805801826649346889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86085608537201217766231259 129128412805801826649346889)
      ·
        refine ⟨96846309604351369987010167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129128412805801826649346889 96846309604351369987010167)
        ·
          refine ⟨145269464406527054980515251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96846309604351369987010167 145269464406527054980515251)
          ·
            refine ⟨217904196609790582470772877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145269464406527054980515251 217904196609790582470772877)
            ·
              refine ⟨81714073728671468426539829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217904196609790582470772877 81714073728671468426539829)
              ·
                refine ⟨7660694412062950164988109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81714073728671468426539829 7660694412062950164988109)
                ·
                  refine ⟨2872760404523606311870541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7660694412062950164988109 2872760404523606311870541)
                  ·
                    refine ⟨1077285151696352366951453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872760404523606311870541 1077285151696352366951453)
                    ·
                      rfl

theorem cell22_3147008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_3147008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147008 prefixEnd_3147008 := by exact prefixLift 3147008
  have htrace : WordTrace (prefixWord ++ tailWord_3147008) baseStart_3147008 baseEnd_3147008 := by
    simpa [prefixWord, tailWord_3147008, baseEnd_3147008] using wordTrace_append hprefix tailTrace_3147008
  have hstable : (prefixWord ++ tailWord_3147008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147008).length < 2 ^ (prefixWord ++ tailWord_3147008).sum := by decide
  have hdescent : baseEnd_3147008 < baseStart_3147008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147098 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_3147098 : Nat := 118140960795 + 3147098 * 2 ^ 59
def prefixEnd_3147098 : Nat := 4983230072969 + 3 ^ 40 * 3147098 * 2
def baseEnd_3147098 : Nat := 1077315960535622132201177

theorem tailTrace_3147098 : CollatzResearch.WordTrace tailWord_3147098 prefixEnd_3147098 1077315960535622132201177 := by
  unfold tailWord_3147098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28696023488152225598104487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76522729301739268261611965 28696023488152225598104487)
  ·
    refine ⟨43044035232228338397156731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28696023488152225598104487 43044035232228338397156731)
    ·
      refine ⟨64566052848342507595735097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43044035232228338397156731 64566052848342507595735097)
      ·
        refine ⟨48424539636256880696801323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64566052848342507595735097 48424539636256880696801323)
        ·
          refine ⟨72636809454385321045201985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48424539636256880696801323 72636809454385321045201985)
          ·
            refine ⟨54477607090788990783901489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72636809454385321045201985 54477607090788990783901489)
            ·
              refine ⟨40858205318091743087926117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54477607090788990783901489 40858205318091743087926117)
              ·
                refine ⟨7660913497142201828986147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40858205318091743087926117 7660913497142201828986147)
                ·
                  refine ⟨11491370245713302743479221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660913497142201828986147 11491370245713302743479221)
                  ·
                    refine ⟨1077315960535622132201177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11491370245713302743479221 1077315960535622132201177)
                    ·
                      rfl

theorem cell22_3147098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_3147098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147098 prefixEnd_3147098 := by exact prefixLift 3147098
  have htrace : WordTrace (prefixWord ++ tailWord_3147098) baseStart_3147098 baseEnd_3147098 := by
    simpa [prefixWord, tailWord_3147098, baseEnd_3147098] using wordTrace_append hprefix tailTrace_3147098
  have hstable : (prefixWord ++ tailWord_3147098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147098).length < 2 ^ (prefixWord ++ tailWord_3147098).sum := by decide
  have hdescent : baseEnd_3147098 < baseStart_3147098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147166 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3147166 : Nat := 118140960795 + 3147166 * 2 ^ 59
def prefixEnd_3147166 : Nat := 4983230072969 + 3 ^ 40 * 3147166 * 2
def baseEnd_3147166 : Nat := 1077339238325292621500969

theorem tailTrace_3147166 : CollatzResearch.WordTrace tailWord_3147166 prefixEnd_3147166 1077339238325292621500969 := by
  unfold tailWord_3147166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348321764545318750736669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76524382744241700003928901 14348321764545318750736669)
  ·
    refine ⟨5380620661704494531526251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14348321764545318750736669 5380620661704494531526251)
    ·
      refine ⟨8070930992556741797289377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5380620661704494531526251 8070930992556741797289377)
      ·
        refine ⟨6053198244417556347967033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8070930992556741797289377 6053198244417556347967033)
        ·
          refine ⟨4539898683313167260975275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6053198244417556347967033 4539898683313167260975275)
          ·
            refine ⟨6809848024969750891462913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539898683313167260975275 6809848024969750891462913)
            ·
              refine ⟨5107386018727313168597185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6809848024969750891462913 5107386018727313168597185)
              ·
                refine ⟨3830539514045484876447889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107386018727313168597185 3830539514045484876447889)
                ·
                  refine ⟨2872904635534113657335917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830539514045484876447889 2872904635534113657335917)
                  ·
                    refine ⟨1077339238325292621500969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872904635534113657335917 1077339238325292621500969)
                    ·
                      rfl

theorem cell22_3147166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3147166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147166 prefixEnd_3147166 := by exact prefixLift 3147166
  have htrace : WordTrace (prefixWord ++ tailWord_3147166) baseStart_3147166 baseEnd_3147166 := by
    simpa [prefixWord, tailWord_3147166, baseEnd_3147166] using wordTrace_append hprefix tailTrace_3147166
  have hstable : (prefixWord ++ tailWord_3147166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147166).length < 2 ^ (prefixWord ++ tailWord_3147166).sum := by decide
  have hdescent : baseEnd_3147166 < baseStart_3147166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147222 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3147222 : Nat := 118140960795 + 3147222 * 2 ^ 59
def prefixEnd_3147222 : Nat := 4983230072969 + 3 ^ 40 * 3147222 * 2
def baseEnd_3147222 : Nat := 1077358408269727142100797

theorem tailTrace_3147222 : CollatzResearch.WordTrace tailWord_3147222 prefixEnd_3147222 1077358408269727142100797 := by
  unfold tailWord_3147222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174288537759979473120745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76525744402773114379954613 7174288537759979473120745)
  ·
    refine ⟨5380716403319984604840559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7174288537759979473120745 5380716403319984604840559)
    ·
      refine ⟨8071074604979976907260839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5380716403319984604840559 8071074604979976907260839)
      ·
        refine ⟨12106611907469965360891259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8071074604979976907260839 12106611907469965360891259)
        ·
          refine ⟨18159917861204948041336889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12106611907469965360891259 18159917861204948041336889)
          ·
            refine ⟨13619938395903711031002667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18159917861204948041336889 13619938395903711031002667)
            ·
              refine ⟨20429907593855566546504001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13619938395903711031002667 20429907593855566546504001)
              ·
                refine ⟨15322430695391674909878001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20429907593855566546504001 15322430695391674909878001)
                ·
                  refine ⟨11491823021543756182408501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15322430695391674909878001 11491823021543756182408501)
                  ·
                    refine ⟨1077358408269727142100797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11491823021543756182408501 1077358408269727142100797)
                    ·
                      rfl

theorem cell22_3147222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3147222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147222 prefixEnd_3147222 := by exact prefixLift 3147222
  have htrace : WordTrace (prefixWord ++ tailWord_3147222) baseStart_3147222 baseEnd_3147222 := by
    simpa [prefixWord, tailWord_3147222, baseEnd_3147222] using wordTrace_append hprefix tailTrace_3147222
  have hstable : (prefixWord ++ tailWord_3147222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147222).length < 2 ^ (prefixWord ++ tailWord_3147222).sum := by decide
  have hdescent : baseEnd_3147222 < baseStart_3147222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147235 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 6]
def baseStart_3147235 : Nat := 118140960795 + 3147235 * 2 ^ 59
def prefixEnd_3147235 : Nat := 4983230072969 + 3 ^ 40 * 3147235 * 2
def baseEnd_3147235 : Nat := 359120952811799813841919

theorem tailTrace_3147235 : CollatzResearch.WordTrace tailWord_3147235 prefixEnd_3147235 359120952811799813841919 := by
  unfold tailWord_3147235
  simp only [CollatzResearch.WordTrace]
  refine ⟨114789090753112574790155159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76526060502075049860103439 114789090753112574790155159)
  ·
    refine ⟨172183636129668862185232739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114789090753112574790155159 172183636129668862185232739)
    ·
      refine ⟨258275454194503293277849109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172183636129668862185232739 258275454194503293277849109)
      ·
        refine ⟨12106661915367341872399177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 258275454194503293277849109 12106661915367341872399177)
        ·
          refine ⟨9079996436525506404299383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12106661915367341872399177 9079996436525506404299383)
          ·
            refine ⟨13619994654788259606449075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079996436525506404299383 13619994654788259606449075)
            ·
              refine ⟨20429991982182389409673613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13619994654788259606449075 20429991982182389409673613)
              ·
                refine ⟨7661246993318396028627605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20429991982182389409673613 7661246993318396028627605)
                ·
                  refine ⟨359120952811799813841919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7661246993318396028627605 359120952811799813841919)
                  ·
                    rfl

theorem cell22_3147235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_3147235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147235 prefixEnd_3147235 := by exact prefixLift 3147235
  have htrace : WordTrace (prefixWord ++ tailWord_3147235) baseStart_3147235 baseEnd_3147235 := by
    simpa [prefixWord, tailWord_3147235, baseEnd_3147235] using wordTrace_append hprefix tailTrace_3147235
  have hstable : (prefixWord ++ tailWord_3147235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147235).length < 2 ^ (prefixWord ++ tailWord_3147235).sum := by decide
  have hdescent : baseEnd_3147235 < baseStart_3147235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147254 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3147254 : Nat := 118140960795 + 3147254 * 2 ^ 59
def prefixEnd_3147254 : Nat := 4983230072969 + 3 ^ 40 * 3147254 * 2
def baseEnd_3147254 : Nat := 1077369362523689725300699

theorem tailTrace_3147254 : CollatzResearch.WordTrace tailWord_3147254 prefixEnd_3147254 1077369362523689725300699 := by
  unfold tailWord_3147254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174361483752733814693551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76526522493362494023397877 7174361483752733814693551)
  ·
    refine ⟨10761542225629100722040327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7174361483752733814693551 10761542225629100722040327)
    ·
      refine ⟨16142313338443651083060491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10761542225629100722040327 16142313338443651083060491)
      ·
        refine ⟨24213470007665476624590737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16142313338443651083060491 24213470007665476624590737)
        ·
          refine ⟨18160102505749107468443053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24213470007665476624590737 18160102505749107468443053)
          ·
            refine ⟨6810038439655915300666145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18160102505749107468443053 6810038439655915300666145)
            ·
              refine ⟨5107528829741936475499609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810038439655915300666145 5107528829741936475499609)
              ·
                refine ⟨3830646622306452356624707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107528829741936475499609 3830646622306452356624707)
                ·
                  refine ⟨5745969933459678534937061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830646622306452356624707 5745969933459678534937061)
                  ·
                    refine ⟨1077369362523689725300699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5745969933459678534937061 1077369362523689725300699)
                    ·
                      rfl

theorem cell22_3147254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3147254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147254 prefixEnd_3147254 := by exact prefixLift 3147254
  have htrace : WordTrace (prefixWord ++ tailWord_3147254) baseStart_3147254 baseEnd_3147254 := by
    simpa [prefixWord, tailWord_3147254, baseEnd_3147254] using wordTrace_append hprefix tailTrace_3147254
  have hstable : (prefixWord ++ tailWord_3147254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147254).length < 2 ^ (prefixWord ++ tailWord_3147254).sum := by decide
  have hdescent : baseEnd_3147254 < baseStart_3147254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147346 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3147346 : Nat := 118140960795 + 3147346 * 2 ^ 59
def prefixEnd_3147346 : Nat := 4983230072969 + 3 ^ 40 * 3147346 * 2
def baseEnd_3147346 : Nat := 1077400856003832152000417

theorem tailTrace_3147346 : CollatzResearch.WordTrace tailWord_3147346 prefixEnd_3147346 1077400856003832152000417 := by
  unfold tailWord_3147346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28698284813927610186861473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76528759503806960498297261 28698284813927610186861473)
  ·
    refine ⟨21523713610445707640146105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28698284813927610186861473 21523713610445707640146105)
    ·
      refine ⟨16142785207834280730109579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21523713610445707640146105 16142785207834280730109579)
      ·
        refine ⟨24214177811751421095164369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16142785207834280730109579 24214177811751421095164369)
        ·
          refine ⟨18160633358813565821373277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24214177811751421095164369 18160633358813565821373277)
          ·
            refine ⟨6810237509555087183014979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18160633358813565821373277 6810237509555087183014979)
            ·
              refine ⟨10215356264332630774522469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810237509555087183014979 10215356264332630774522469)
              ·
                refine ⟨1915379299562368270222963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10215356264332630774522469 1915379299562368270222963)
                ·
                  refine ⟨2873068949343552405334445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915379299562368270222963 2873068949343552405334445)
                  ·
                    refine ⟨1077400856003832152000417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873068949343552405334445 1077400856003832152000417)
                    ·
                      rfl

theorem cell22_3147346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3147346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147346 prefixEnd_3147346 := by exact prefixLift 3147346
  have htrace : WordTrace (prefixWord ++ tailWord_3147346) baseStart_3147346 baseEnd_3147346 := by
    simpa [prefixWord, tailWord_3147346, baseEnd_3147346] using wordTrace_append hprefix tailTrace_3147346
  have hstable : (prefixWord ++ tailWord_3147346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147346).length < 2 ^ (prefixWord ++ tailWord_3147346).sum := by decide
  have hdescent : baseEnd_3147346 < baseStart_3147346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147372 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_3147372 : Nat := 118140960795 + 3147372 * 2 ^ 59
def prefixEnd_3147372 : Nat := 4983230072969 + 3 ^ 40 * 3147372 * 2
def baseEnd_3147372 : Nat := 1077409756335176750850337

theorem tailTrace_3147372 : CollatzResearch.WordTrace tailWord_3147372 prefixEnd_3147372 1077409756335176750850337 := by
  unfold tailWord_3147372
  simp only [CollatzResearch.WordTrace]
  refine ⟨57397043776808123593946185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76529391702410831458594913 57397043776808123593946185)
  ·
    refine ⟨43047782832606092695459639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57397043776808123593946185 43047782832606092695459639)
    ·
      refine ⟨64571674248909139043189459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43047782832606092695459639 64571674248909139043189459)
      ·
        refine ⟨96857511373363708564784189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64571674248909139043189459 96857511373363708564784189)
        ·
          refine ⟨36321566765011390711794071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96857511373363708564784189 36321566765011390711794071)
          ·
            refine ⟨54482350147517086067691107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36321566765011390711794071 54482350147517086067691107)
            ·
              refine ⟨81723525221275629101536661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54482350147517086067691107 81723525221275629101536661)
              ·
                refine ⟨3830790244747295114134531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81723525221275629101536661 3830790244747295114134531)
                ·
                  refine ⟨5746185367120942671201797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830790244747295114134531 5746185367120942671201797)
                  ·
                    refine ⟨1077409756335176750850337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5746185367120942671201797 1077409756335176750850337)
                    ·
                      rfl

theorem cell22_3147372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_3147372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147372 prefixEnd_3147372 := by exact prefixLift 3147372
  have htrace : WordTrace (prefixWord ++ tailWord_3147372) baseStart_3147372 baseEnd_3147372 := by
    simpa [prefixWord, tailWord_3147372, baseEnd_3147372] using wordTrace_append hprefix tailTrace_3147372
  have hstable : (prefixWord ++ tailWord_3147372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147372).length < 2 ^ (prefixWord ++ tailWord_3147372).sum := by decide
  have hdescent : baseEnd_3147372 < baseStart_3147372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147389 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_3147389 : Nat := 118140960795 + 3147389 * 2 ^ 59
def prefixEnd_3147389 : Nat := 4983230072969 + 3 ^ 40 * 3147389 * 2
def baseEnd_3147389 : Nat := 1077415575782594373175285

theorem tailTrace_3147389 : CollatzResearch.WordTrace tailWord_3147389 prefixEnd_3147389 1077415575782594373175285 := by
  unfold tailWord_3147389
  simp only [CollatzResearch.WordTrace]
  refine ⟨114794707594554659091261221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76529805063036439394174147 114794707594554659091261221)
  ·
    refine ⟨21524007673978998579611479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114794707594554659091261221 21524007673978998579611479)
    ·
      refine ⟨32286011510968497869417219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21524007673978998579611479 32286011510968497869417219)
      ·
        refine ⟨48429017266452746804125829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32286011510968497869417219 48429017266452746804125829)
        ·
          refine ⟨9080440737459890025773593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48429017266452746804125829 9080440737459890025773593)
          ·
            refine ⟨6810330553094917519330195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9080440737459890025773593 6810330553094917519330195)
            ·
              refine ⟨10215495829642376278995293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810330553094917519330195 10215495829642376278995293)
              ·
                refine ⟨3830810936115891104623235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10215495829642376278995293 3830810936115891104623235)
                ·
                  refine ⟨5746216404173836656934853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830810936115891104623235 5746216404173836656934853)
                  ·
                    refine ⟨1077415575782594373175285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5746216404173836656934853 1077415575782594373175285)
                    ·
                      rfl

theorem cell22_3147389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_3147389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147389 prefixEnd_3147389 := by exact prefixLift 3147389
  have htrace : WordTrace (prefixWord ++ tailWord_3147389) baseStart_3147389 baseEnd_3147389 := by
    simpa [prefixWord, tailWord_3147389, baseEnd_3147389] using wordTrace_append hprefix tailTrace_3147389
  have hstable : (prefixWord ++ tailWord_3147389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147389).length < 2 ^ (prefixWord ++ tailWord_3147389).sum := by decide
  have hdescent : baseEnd_3147389 < baseStart_3147389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147524 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3147524 : Nat := 118140960795 + 3147524 * 2 ^ 59
def prefixEnd_3147524 : Nat := 4983230072969 + 3 ^ 40 * 3147524 * 2
def baseEnd_3147524 : Nat := 1077461789041499021049871

theorem tailTrace_3147524 : CollatzResearch.WordTrace tailWord_3147524 prefixEnd_3147524 1077461789041499021049871 := by
  unfold tailWord_3147524
  simp only [CollatzResearch.WordTrace]
  refine ⟨57399815724532788573712813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76533087632710384764950417 57399815724532788573712813)
  ·
    refine ⟨21524930896699795715142305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57399815724532788573712813 21524930896699795715142305)
    ·
      refine ⟨16143698172524846786356729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21524930896699795715142305 16143698172524846786356729)
      ·
        refine ⟨12107773629393635089767547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16143698172524846786356729 12107773629393635089767547)
        ·
          refine ⟨18161660444090452634651321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12107773629393635089767547 18161660444090452634651321)
          ·
            refine ⟨13621245333067839475988491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18161660444090452634651321 13621245333067839475988491)
            ·
              refine ⟨20431867999601759213982737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13621245333067839475988491 20431867999601759213982737)
              ·
                refine ⟨15323900999701319410487053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20431867999601759213982737 15323900999701319410487053)
                ·
                  refine ⟨5746462874887994778932645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15323900999701319410487053 5746462874887994778932645)
                  ·
                    refine ⟨1077461789041499021049871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5746462874887994778932645 1077461789041499021049871)
                    ·
                      rfl

theorem cell22_3147524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3147524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147524 prefixEnd_3147524 := by exact prefixLift 3147524
  have htrace : WordTrace (prefixWord ++ tailWord_3147524) baseStart_3147524 baseEnd_3147524 := by
    simpa [prefixWord, tailWord_3147524, baseEnd_3147524] using wordTrace_append hprefix tailTrace_3147524
  have hstable : (prefixWord ++ tailWord_3147524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147524).length < 2 ^ (prefixWord ++ tailWord_3147524).sum := by decide
  have hdescent : baseEnd_3147524 < baseStart_3147524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147554 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3147554 : Nat := 118140960795 + 3147554 * 2 ^ 59
def prefixEnd_3147554 : Nat := 4983230072969 + 3 ^ 40 * 3147554 * 2
def baseEnd_3147554 : Nat := 1077472058654588942799779

theorem tailTrace_3147554 : CollatzResearch.WordTrace tailWord_3147554 prefixEnd_3147554 1077472058654588942799779 := by
  unfold tailWord_3147554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28700181409739223067754429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76533817092637928180678477 28700181409739223067754429)
  ·
    refine ⟨10762568028652208650407911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28700181409739223067754429 10762568028652208650407911)
    ·
      refine ⟨16143852042978312975611867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10762568028652208650407911 16143852042978312975611867)
      ·
        refine ⟨24215778064467469463417801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16143852042978312975611867 24215778064467469463417801)
        ·
          refine ⟨18161833548350602097563351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24215778064467469463417801 18161833548350602097563351)
          ·
            refine ⟨27242750322525903146345027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18161833548350602097563351 27242750322525903146345027)
            ·
              refine ⟨40864125483788854719517541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27242750322525903146345027 40864125483788854719517541)
              ·
                refine ⟨7662023528210410259909539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40864125483788854719517541 7662023528210410259909539)
                ·
                  refine ⟨11493035292315615389864309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662023528210410259909539 11493035292315615389864309)
                  ·
                    refine ⟨1077472058654588942799779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11493035292315615389864309 1077472058654588942799779)
                    ·
                      rfl

theorem cell22_3147554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3147554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147554 prefixEnd_3147554 := by exact prefixLift 3147554
  have htrace : WordTrace (prefixWord ++ tailWord_3147554) baseStart_3147554 baseEnd_3147554 := by
    simpa [prefixWord, tailWord_3147554, baseEnd_3147554] using wordTrace_append hprefix tailTrace_3147554
  have hstable : (prefixWord ++ tailWord_3147554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147554).length < 2 ^ (prefixWord ++ tailWord_3147554).sum := by decide
  have hdescent : baseEnd_3147554 < baseStart_3147554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147556 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3147556 : Nat := 118140960795 + 3147556 * 2 ^ 59
def prefixEnd_3147556 : Nat := 4983230072969 + 3 ^ 40 * 3147556 * 2
def baseEnd_3147556 : Nat := 359157581098487201416591

theorem tailTrace_3147556 : CollatzResearch.WordTrace tailWord_3147556 prefixEnd_3147556 359157581098487201416591 := by
  unfold tailWord_3147556
  simp only [CollatzResearch.WordTrace]
  refine ⟨57400399292474823306295261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76533865723299764408393681 57400399292474823306295261)
  ·
    refine ⟨21525149734678058739860723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57400399292474823306295261 21525149734678058739860723)
    ·
      refine ⟨32287724602017088109791085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21525149734678058739860723 32287724602017088109791085)
      ·
        refine ⟨12107896725756408041171657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32287724602017088109791085 12107896725756408041171657)
        ·
          refine ⟨9080922544317306030878743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12107896725756408041171657 9080922544317306030878743)
          ·
            refine ⟨13621383816475959046318115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9080922544317306030878743 13621383816475959046318115)
            ·
              refine ⟨20432075724713938569477173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13621383816475959046318115 20432075724713938569477173)
              ·
                refine ⟨1915507099191931740888485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20432075724713938569477173 1915507099191931740888485)
                ·
                  refine ⟨359157581098487201416591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915507099191931740888485 359157581098487201416591)
                  ·
                    rfl

theorem cell22_3147556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3147556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147556 prefixEnd_3147556 := by exact prefixLift 3147556
  have htrace : WordTrace (prefixWord ++ tailWord_3147556) baseStart_3147556 baseEnd_3147556 := by
    simpa [prefixWord, tailWord_3147556, baseEnd_3147556] using wordTrace_append hprefix tailTrace_3147556
  have hstable : (prefixWord ++ tailWord_3147556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147556).length < 2 ^ (prefixWord ++ tailWord_3147556).sum := by decide
  have hdescent : baseEnd_3147556 < baseStart_3147556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147571 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 4, 3]
def baseStart_3147571 : Nat := 118140960795 + 3147571 * 2 ^ 59
def prefixEnd_3147571 : Nat := 4983230072969 + 3 ^ 40 * 3147571 * 2
def baseEnd_3147571 : Nat := 1077477878102006565124727

theorem tailTrace_3147571 : CollatzResearch.WordTrace tailWord_3147571 prefixEnd_3147571 1077477878102006565124727 := by
  unfold tailWord_3147571
  simp only [CollatzResearch.WordTrace]
  refine ⟨114801345679895304174386567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76534230453263536116257711 114801345679895304174386567)
  ·
    refine ⟨172202018519842956261579851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114801345679895304174386567 172202018519842956261579851)
    ·
      refine ⟨258303027779764434392369777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172202018519842956261579851 258303027779764434392369777)
      ·
        refine ⟨193727270834823325794277333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258303027779764434392369777 193727270834823325794277333)
        ·
          refine ⟨4540482910191171698303375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 193727270834823325794277333 4540482910191171698303375)
          ·
            refine ⟨6810724365286757547455063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540482910191171698303375 6810724365286757547455063)
            ·
              refine ⟨10216086547930136321182595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810724365286757547455063 10216086547930136321182595)
              ·
                refine ⟨15324129821895204481773893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10216086547930136321182595 15324129821895204481773893)
                ·
                  refine ⟨2873274341605350840332605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15324129821895204481773893 2873274341605350840332605)
                  ·
                    refine ⟨1077477878102006565124727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873274341605350840332605 1077477878102006565124727)
                    ·
                      rfl

theorem cell22_3147571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 3].length) (baseStart_3147571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147571 prefixEnd_3147571 := by exact prefixLift 3147571
  have htrace : WordTrace (prefixWord ++ tailWord_3147571) baseStart_3147571 baseEnd_3147571 := by
    simpa [prefixWord, tailWord_3147571, baseEnd_3147571] using wordTrace_append hprefix tailTrace_3147571
  have hstable : (prefixWord ++ tailWord_3147571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147571).length < 2 ^ (prefixWord ++ tailWord_3147571).sum := by decide
  have hdescent : baseEnd_3147571 < baseStart_3147571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147601 : List Nat := [1, 2, 2, 1, 5, 3, 2, 6]
def baseStart_3147601 : Nat := 118140960795 + 3147601 * 2 ^ 59
def prefixEnd_3147601 : Nat := 4983230072969 + 3 ^ 40 * 3147601 * 2
def baseEnd_3147601 : Nat := 119720905301677387430515

theorem tailTrace_3147601 : CollatzResearch.WordTrace tailWord_3147601 prefixEnd_3147601 119720905301677387430515 := by
  unfold tailWord_3147601
  simp only [CollatzResearch.WordTrace]
  refine ⟨114802439869786619297978657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76534959913191079531985771 114802439869786619297978657)
  ·
    refine ⟨86101829902339964473483993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114802439869786619297978657 86101829902339964473483993)
    ·
      refine ⟨64576372426754973355112995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86101829902339964473483993 64576372426754973355112995)
      ·
        refine ⟨96864558640132460032669493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64576372426754973355112995 96864558640132460032669493)
        ·
          refine ⟨9081052372512418128062765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96864558640132460032669493 9081052372512418128062765)
          ·
            refine ⟨3405394639692156798023537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9081052372512418128062765 3405394639692156798023537)
            ·
              refine ⟨2554045979769117598517653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3405394639692156798023537 2554045979769117598517653)
              ·
                refine ⟨119720905301677387430515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2554045979769117598517653 119720905301677387430515)
                ·
                  rfl

theorem cell22_3147601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 6].length) (baseStart_3147601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147601 prefixEnd_3147601 := by exact prefixLift 3147601
  have htrace : WordTrace (prefixWord ++ tailWord_3147601) baseStart_3147601 baseEnd_3147601 := by
    simpa [prefixWord, tailWord_3147601, baseEnd_3147601] using wordTrace_append hprefix tailTrace_3147601
  have hstable : (prefixWord ++ tailWord_3147601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147601).length < 2 ^ (prefixWord ++ tailWord_3147601).sum := by decide
  have hdescent : baseEnd_3147601 < baseStart_3147601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147629 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3147629 : Nat := 118140960795 + 3147629 * 2 ^ 59
def prefixEnd_3147629 : Nat := 4983230072969 + 3 ^ 40 * 3147629 * 2
def baseEnd_3147629 : Nat := 359165910895771249058183

theorem tailTrace_3147629 : CollatzResearch.WordTrace tailWord_3147629 prefixEnd_3147629 359165910895771249058183 := by
  unfold tailWord_3147629
  simp only [CollatzResearch.WordTrace]
  refine ⟨114803461113685180079997941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76535640742456786719998627 114803461113685180079997941)
  ·
    refine ⟨10762824479407985632499807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114803461113685180079997941 10762824479407985632499807)
    ·
      refine ⟨16144236719111978448749711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10762824479407985632499807 16144236719111978448749711)
      ·
        refine ⟨24216355078667967673124567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16144236719111978448749711 24216355078667967673124567)
        ·
          refine ⟨36324532618001951509686851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24216355078667967673124567 36324532618001951509686851)
          ·
            refine ⟨54486798927002927264530277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36324532618001951509686851 54486798927002927264530277)
            ·
              refine ⟨10216274798813048862099427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54486798927002927264530277 10216274798813048862099427)
              ·
                refine ⟨15324412198219573293149141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10216274798813048862099427 15324412198219573293149141)
                ·
                  refine ⟨359165910895771249058183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15324412198219573293149141 359165910895771249058183)
                  ·
                    rfl

theorem cell22_3147629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3147629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147629 prefixEnd_3147629 := by exact prefixLift 3147629
  have htrace : WordTrace (prefixWord ++ tailWord_3147629) baseStart_3147629 baseEnd_3147629 := by
    simpa [prefixWord, tailWord_3147629, baseEnd_3147629] using wordTrace_append hprefix tailTrace_3147629
  have hstable : (prefixWord ++ tailWord_3147629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147629).length < 2 ^ (prefixWord ++ tailWord_3147629).sum := by decide
  have hdescent : baseEnd_3147629 < baseStart_3147629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147704 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3147704 : Nat := 118140960795 + 3147704 * 2 ^ 59
def prefixEnd_3147704 : Nat := 4983230072969 + 3 ^ 40 * 3147704 * 2
def baseEnd_3147704 : Nat := 1077523406720038551549319

theorem tailTrace_3147704 : CollatzResearch.WordTrace tailWord_3147704 prefixEnd_3147704 1077523406720038551549319 := by
  unfold tailWord_3147704
  simp only [CollatzResearch.WordTrace]
  refine ⟨57403098294206733944489083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76537464392275645259318777 57403098294206733944489083)
  ·
    refine ⟨86104647441310100916733625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57403098294206733944489083 86104647441310100916733625)
    ·
      refine ⟨64578485580982575687550219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86104647441310100916733625 64578485580982575687550219)
      ·
        refine ⟨96867728371473863531325329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64578485580982575687550219 96867728371473863531325329)
        ·
          refine ⟨72650796278605397648493997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96867728371473863531325329 72650796278605397648493997)
          ·
            refine ⟨27244048604477024118185249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72650796278605397648493997 27244048604477024118185249)
            ·
              refine ⟨20433036453357768088638937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27244048604477024118185249 20433036453357768088638937)
              ·
                refine ⟨15324777340018326066479203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20433036453357768088638937 15324777340018326066479203)
                ·
                  refine ⟨22987166010027489099718805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15324777340018326066479203 22987166010027489099718805)
                  ·
                    refine ⟨1077523406720038551549319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22987166010027489099718805 1077523406720038551549319)
                    ·
                      rfl

theorem cell22_3147704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3147704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147704 prefixEnd_3147704 := by exact prefixLift 3147704
  have htrace : WordTrace (prefixWord ++ tailWord_3147704) baseStart_3147704 baseEnd_3147704 := by
    simpa [prefixWord, tailWord_3147704, baseEnd_3147704] using wordTrace_append hprefix tailTrace_3147704
  have hstable : (prefixWord ++ tailWord_3147704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147704).length < 2 ^ (prefixWord ++ tailWord_3147704).sum := by decide
  have hdescent : baseEnd_3147704 < baseStart_3147704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147708 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 6]
def baseStart_3147708 : Nat := 118140960795 + 3147708 * 2 ^ 59
def prefixEnd_3147708 : Nat := 4983230072969 + 3 ^ 40 * 3147708 * 2
def baseEnd_3147708 : Nat := 359174925333927958149769

theorem tailTrace_3147708 : CollatzResearch.WordTrace tailWord_3147708 prefixEnd_3147708 359174925333927958149769 := by
  unfold tailWord_3147708
  simp only [CollatzResearch.WordTrace]
  refine ⟨57403171240199488286061889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76537561653599317714749185 57403171240199488286061889)
  ·
    refine ⟨43052378430149616214546417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57403171240199488286061889 43052378430149616214546417)
    ·
      refine ⟨32289283822612212160909813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43052378430149616214546417 32289283822612212160909813)
      ·
        refine ⟨3027120358369894890085295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32289283822612212160909813 3027120358369894890085295)
        ·
          refine ⟨4540680537554842335127943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027120358369894890085295 4540680537554842335127943)
          ·
            refine ⟨6811020806332263502691915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540680537554842335127943 6811020806332263502691915)
            ·
              refine ⟨10216531209498395254037873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811020806332263502691915 10216531209498395254037873)
              ·
                refine ⟨7662398407123796440528405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10216531209498395254037873 7662398407123796440528405)
                ·
                  refine ⟨359174925333927958149769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7662398407123796440528405 359174925333927958149769)
                  ·
                    rfl

theorem cell22_3147708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_3147708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147708 prefixEnd_3147708 := by exact prefixLift 3147708
  have htrace : WordTrace (prefixWord ++ tailWord_3147708) baseStart_3147708 baseEnd_3147708 := by
    simpa [prefixWord, tailWord_3147708, baseEnd_3147708] using wordTrace_append hprefix tailTrace_3147708
  have hstable : (prefixWord ++ tailWord_3147708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147708).length < 2 ^ (prefixWord ++ tailWord_3147708).sum := by decide
  have hdescent : baseEnd_3147708 < baseStart_3147708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147757 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_3147757 : Nat := 118140960795 + 3147757 * 2 ^ 59
def prefixEnd_3147757 : Nat := 4983230072969 + 3 ^ 40 * 3147757 * 2
def baseEnd_3147757 : Nat := 1077541549703164079974157

theorem tailTrace_3147757 : CollatzResearch.WordTrace tailWord_3147757 prefixEnd_3147757 1077541549703164079974157 := by
  unfold tailWord_3147757
  simp only [CollatzResearch.WordTrace]
  refine ⟨114808129657221457940657525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76538753104814305293771683 114808129657221457940657525)
  ·
    refine ⟨10763262155364511681936643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114808129657221457940657525 10763262155364511681936643)
    ·
      refine ⟨16144893233046767522904965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10763262155364511681936643 16144893233046767522904965)
      ·
        refine ⟨3027167481196268910544681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16144893233046767522904965 3027167481196268910544681)
        ·
          refine ⟨2270375610897201682908511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3027167481196268910544681 2270375610897201682908511)
          ·
            refine ⟨3405563416345802524362767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270375610897201682908511 3405563416345802524362767)
            ·
              refine ⟨5108345124518703786544151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405563416345802524362767 5108345124518703786544151)
              ·
                refine ⟨7662517686778055679816227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108345124518703786544151 7662517686778055679816227)
                ·
                  refine ⟨11493776530167083519724341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662517686778055679816227 11493776530167083519724341)
                  ·
                    refine ⟨1077541549703164079974157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11493776530167083519724341 1077541549703164079974157)
                    ·
                      rfl

theorem cell22_3147757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_3147757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147757 prefixEnd_3147757 := by exact prefixLift 3147757
  have htrace : WordTrace (prefixWord ++ tailWord_3147757) baseStart_3147757 baseEnd_3147757 := by
    simpa [prefixWord, tailWord_3147757, baseEnd_3147757] using wordTrace_append hprefix tailTrace_3147757
  have hstable : (prefixWord ++ tailWord_3147757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147757).length < 2 ^ (prefixWord ++ tailWord_3147757).sum := by decide
  have hdescent : baseEnd_3147757 < baseStart_3147757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147779 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_3147779 : Nat := 118140960795 + 3147779 * 2 ^ 59
def prefixEnd_3147779 : Nat := 4983230072969 + 3 ^ 40 * 3147779 * 2
def baseEnd_3147779 : Nat := 1077549080752763355924089

theorem tailTrace_3147779 : CollatzResearch.WordTrace tailWord_3147779 prefixEnd_3147779 1077549080752763355924089 := by
  unfold tailWord_3147779
  simp only [CollatzResearch.WordTrace]
  refine ⟨114808932063141755697958391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76539288042094503798638927 114808932063141755697958391)
  ·
    refine ⟨172213398094712633546937587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114808932063141755697958391 172213398094712633546937587)
    ·
      refine ⟨258320097142068950320406381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172213398094712633546937587 258320097142068950320406381)
      ·
        refine ⟨96870036428275856370152393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258320097142068950320406381 96870036428275856370152393)
        ·
          refine ⟨72652527321206892277614295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96870036428275856370152393 72652527321206892277614295)
          ·
            refine ⟨108978790981810338416421443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72652527321206892277614295 108978790981810338416421443)
            ·
              refine ⟨163468186472715507624632165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108978790981810338416421443 163468186472715507624632165)
              ·
                refine ⟨30650284963634157679618531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163468186472715507624632165 30650284963634157679618531)
                ·
                  refine ⟨45975427445451236519427797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30650284963634157679618531 45975427445451236519427797)
                  ·
                    refine ⟨1077549080752763355924089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45975427445451236519427797 1077549080752763355924089)
                    ·
                      rfl

theorem cell22_3147779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_3147779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147779 prefixEnd_3147779 := by exact prefixLift 3147779
  have htrace : WordTrace (prefixWord ++ tailWord_3147779) baseStart_3147779 baseEnd_3147779 := by
    simpa [prefixWord, tailWord_3147779, baseEnd_3147779] using wordTrace_append hprefix tailTrace_3147779
  have hstable : (prefixWord ++ tailWord_3147779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147779).length < 2 ^ (prefixWord ++ tailWord_3147779).sum := by decide
  have hdescent : baseEnd_3147779 < baseStart_3147779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147802 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_3147802 : Nat := 118140960795 + 3147802 * 2 ^ 59
def prefixEnd_3147802 : Nat := 4983230072969 + 3 ^ 40 * 3147802 * 2
def baseEnd_3147802 : Nat := 1077556954122798962599019

theorem tailTrace_3147802 : CollatzResearch.WordTrace tailWord_3147802 prefixEnd_3147802 1077556954122798962599019 := by
  unfold tailWord_3147802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28702442735514607656511415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76539847294705620417363773 28702442735514607656511415)
  ·
    refine ⟨43053664103271911484767123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28702442735514607656511415 43053664103271911484767123)
    ·
      refine ⟨64580496154907867227150685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43053664103271911484767123 64580496154907867227150685)
      ·
        refine ⟨24217686058090450210181507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64580496154907867227150685 24217686058090450210181507)
        ·
          refine ⟨36326529087135675315272261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24217686058090450210181507 36326529087135675315272261)
          ·
            refine ⟨6811224203837939121613549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36326529087135675315272261 6811224203837939121613549)
            ·
              refine ⟨2554209076439227170605081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6811224203837939121613549 2554209076439227170605081)
              ·
                refine ⟨1915656807329420377953811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554209076439227170605081 1915656807329420377953811)
                ·
                  refine ⟨2873485210994130566930717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915656807329420377953811 2873485210994130566930717)
                  ·
                    refine ⟨1077556954122798962599019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873485210994130566930717 1077556954122798962599019)
                    ·
                      rfl

theorem cell22_3147802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_3147802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147802 prefixEnd_3147802 := by exact prefixLift 3147802
  have htrace : WordTrace (prefixWord ++ tailWord_3147802) baseStart_3147802 baseEnd_3147802 := by
    simpa [prefixWord, tailWord_3147802, baseEnd_3147802] using wordTrace_append hprefix tailTrace_3147802
  have hstable : (prefixWord ++ tailWord_3147802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147802).length < 2 ^ (prefixWord ++ tailWord_3147802).sum := by decide
  have hdescent : baseEnd_3147802 < baseStart_3147802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147811 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 3, 4]
def baseStart_3147811 : Nat := 118140960795 + 3147811 * 2 ^ 59
def prefixEnd_3147811 : Nat := 4983230072969 + 3 ^ 40 * 3147811 * 2
def baseEnd_3147811 : Nat := 1077560035006725939123991

theorem tailTrace_3147811 : CollatzResearch.WordTrace tailWord_3147811 prefixEnd_3147811 1077560035006725939123991 := by
  unfold tailWord_3147811
  simp only [CollatzResearch.WordTrace]
  refine ⟨114810099199025825163123287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76540066132683883442082191 114810099199025825163123287)
  ·
    refine ⟨172215148798538737744684931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114810099199025825163123287 172215148798538737744684931)
    ·
      refine ⟨258322723197808106617027397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172215148798538737744684931 258322723197808106617027397)
      ·
        refine ⟨48435510599589019990692637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258322723197808106617027397 48435510599589019990692637)
        ·
          refine ⟨18163316474845882496509739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48435510599589019990692637 18163316474845882496509739)
          ·
            refine ⟨27244974712268823744764609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18163316474845882496509739 27244974712268823744764609)
            ·
              refine ⟨20433731034201617808573457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27244974712268823744764609 20433731034201617808573457)
              ·
                refine ⟨15325298275651213356430093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20433731034201617808573457 15325298275651213356430093)
                ·
                  refine ⟨5746986853369205008661285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15325298275651213356430093 5746986853369205008661285)
                  ·
                    refine ⟨1077560035006725939123991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5746986853369205008661285 1077560035006725939123991)
                    ·
                      rfl

theorem cell22_3147811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_3147811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147811 prefixEnd_3147811 := by exact prefixLift 3147811
  have htrace : WordTrace (prefixWord ++ tailWord_3147811) baseStart_3147811 baseEnd_3147811 := by
    simpa [prefixWord, tailWord_3147811, baseEnd_3147811] using wordTrace_append hprefix tailTrace_3147811
  have hstable : (prefixWord ++ tailWord_3147811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147811).length < 2 ^ (prefixWord ++ tailWord_3147811).sum := by decide
  have hdescent : baseEnd_3147811 < baseStart_3147811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147815 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 5]
def baseStart_3147815 : Nat := 118140960795 + 3147815 * 2 ^ 59
def prefixEnd_3147815 : Nat := 4983230072969 + 3 ^ 40 * 3147815 * 2
def baseEnd_3147815 : Nat := 359187134762823754007993

theorem tailTrace_3147815 : CollatzResearch.WordTrace tailWord_3147815 prefixEnd_3147815 359187134762823754007993 := by
  unfold tailWord_3147815
  simp only [CollatzResearch.WordTrace]
  refine ⟨114810245091011333846268899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76540163394007555897512599 114810245091011333846268899)
  ·
    refine ⟨172215367636517000769403349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114810245091011333846268899 172215367636517000769403349)
    ·
      refine ⟨4036297678980867205532891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 172215367636517000769403349 4036297678980867205532891)
      ·
        refine ⟨6054446518471300808299337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036297678980867205532891 6054446518471300808299337)
        ·
          refine ⟨4540834888853475606224503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6054446518471300808299337 4540834888853475606224503)
          ·
            refine ⟨6811252333280213409336755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540834888853475606224503 6811252333280213409336755)
            ·
              refine ⟨10216878499920320114005133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811252333280213409336755 10216878499920320114005133)
              ·
                refine ⟨3831329437470120042751925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10216878499920320114005133 3831329437470120042751925)
                ·
                  refine ⟨359187134762823754007993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3831329437470120042751925 359187134762823754007993)
                  ·
                    rfl

theorem cell22_3147815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 5].length) (baseStart_3147815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147815 prefixEnd_3147815 := by exact prefixLift 3147815
  have htrace : WordTrace (prefixWord ++ tailWord_3147815) baseStart_3147815 baseEnd_3147815 := by
    simpa [prefixWord, tailWord_3147815, baseEnd_3147815] using wordTrace_append hprefix tailTrace_3147815
  have hstable : (prefixWord ++ tailWord_3147815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147815).length < 2 ^ (prefixWord ++ tailWord_3147815).sum := by decide
  have hdescent : baseEnd_3147815 < baseStart_3147815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147888 : List Nat := [2, 1, 1, 1, 5, 3, 3, 6]
def baseStart_3147888 : Nat := 118140960795 + 3147888 * 2 ^ 59
def prefixEnd_3147888 : Nat := 4983230072969 + 3 ^ 40 * 3147888 * 2
def baseEnd_3147888 : Nat := 119731821520035933883195

theorem tailTrace_3147888 : CollatzResearch.WordTrace tailWord_3147888 prefixEnd_3147888 119731821520035933883195 := by
  unfold tailWord_3147888
  simp only [CollatzResearch.WordTrace]
  refine ⟨57406453809873433656838159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76541938413164578209117545 57406453809873433656838159)
  ·
    refine ⟨86109680714810150485257239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57406453809873433656838159 86109680714810150485257239)
    ·
      refine ⟨129164521072215225727885859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86109680714810150485257239 129164521072215225727885859)
      ·
        refine ⟨193746781608322838591828789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129164521072215225727885859 193746781608322838591828789)
        ·
          refine ⟨18163760775780266117983949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193746781608322838591828789 18163760775780266117983949)
          ·
            refine ⟨6811410290917599794243981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18163760775780266117983949 6811410290917599794243981)
            ·
              refine ⟨2554278859094099922841493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6811410290917599794243981 2554278859094099922841493)
              ·
                refine ⟨119731821520035933883195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2554278859094099922841493 119731821520035933883195)
                ·
                  rfl

theorem cell22_3147888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_3147888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147888 prefixEnd_3147888 := by exact prefixLift 3147888
  have htrace : WordTrace (prefixWord ++ tailWord_3147888) baseStart_3147888 baseEnd_3147888 := by
    simpa [prefixWord, tailWord_3147888, baseEnd_3147888] using wordTrace_append hprefix tailTrace_3147888
  have hstable : (prefixWord ++ tailWord_3147888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147888).length < 2 ^ (prefixWord ++ tailWord_3147888).sum := by decide
  have hdescent : baseEnd_3147888 < baseStart_3147888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147890 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_3147890 : Nat := 118140960795 + 3147890 * 2 ^ 59
def prefixEnd_3147890 : Nat := 4983230072969 + 3 ^ 40 * 3147890 * 2
def baseEnd_3147890 : Nat := 1077587078321196066398749

theorem tailTrace_3147890 : CollatzResearch.WordTrace tailWord_3147890 prefixEnd_3147890 1077587078321196066398749 := by
  unfold tailWord_3147890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28703245141434905413812281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76541987043826414436832749 28703245141434905413812281)
  ·
    refine ⟨21527433856076179060359211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28703245141434905413812281 21527433856076179060359211)
    ·
      refine ⟨32291150784114268590538817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21527433856076179060359211 32291150784114268590538817)
      ·
        refine ⟨24218363088085701442904113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32291150784114268590538817 24218363088085701442904113)
        ·
          refine ⟨18163772316064276082178085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24218363088085701442904113 18163772316064276082178085)
          ·
            refine ⟨3405707309262051765408391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18163772316064276082178085 3405707309262051765408391)
            ·
              refine ⟨5108560963893077648112587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405707309262051765408391 5108560963893077648112587)
              ·
                refine ⟨7662841445839616472168881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108560963893077648112587 7662841445839616472168881)
                ·
                  refine ⟨5747131084379712354126661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7662841445839616472168881 5747131084379712354126661)
                  ·
                    refine ⟨1077587078321196066398749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747131084379712354126661 1077587078321196066398749)
                    ·
                      rfl

theorem cell22_3147890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_3147890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147890 prefixEnd_3147890 := by exact prefixLift 3147890
  have htrace : WordTrace (prefixWord ++ tailWord_3147890) baseStart_3147890 baseEnd_3147890 := by
    simpa [prefixWord, tailWord_3147890, baseEnd_3147890] using wordTrace_append hprefix tailTrace_3147890
  have hstable : (prefixWord ++ tailWord_3147890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147890).length < 2 ^ (prefixWord ++ tailWord_3147890).sum := by decide
  have hdescent : baseEnd_3147890 < baseStart_3147890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147920 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 1, 3]
def baseStart_3147920 : Nat := 118140960795 + 3147920 * 2 ^ 59
def prefixEnd_3147920 : Nat := 4983230072969 + 3 ^ 40 * 3147920 * 2
def baseEnd_3147920 : Nat := 1077597347934285988148657

theorem tailTrace_3147920 : CollatzResearch.WordTrace tailWord_3147920 prefixEnd_3147920 1077597347934285988148657 := by
  unfold tailWord_3147920
  simp only [CollatzResearch.WordTrace]
  refine ⟨57407037377815468389420607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76542716503753957852560809 57407037377815468389420607)
  ·
    refine ⟨86110556066723202584130911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57407037377815468389420607 86110556066723202584130911)
    ·
      refine ⟨129165834100084803876196367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86110556066723202584130911 129165834100084803876196367)
      ·
        refine ⟨193748751150127205814294551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129165834100084803876196367 193748751150127205814294551)
        ·
          refine ⟨290623126725190808721441827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193748751150127205814294551 290623126725190808721441827)
          ·
            refine ⟨435934690087786213082162741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290623126725190808721441827 435934690087786213082162741)
            ·
              refine ⟨40868877195729957476452757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435934690087786213082162741 40868877195729957476452757)
              ·
                refine ⟨1915728618549841756708723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40868877195729957476452757 1915728618549841756708723)
                ·
                  refine ⟨2873592927824762635063085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915728618549841756708723 2873592927824762635063085)
                  ·
                    refine ⟨1077597347934285988148657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873592927824762635063085 1077597347934285988148657)
                    ·
                      rfl

theorem cell22_3147920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_3147920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147920 prefixEnd_3147920 := by exact prefixLift 3147920
  have htrace : WordTrace (prefixWord ++ tailWord_3147920) baseStart_3147920 baseEnd_3147920 := by
    simpa [prefixWord, tailWord_3147920, baseEnd_3147920] using wordTrace_append hprefix tailTrace_3147920
  have hstable : (prefixWord ++ tailWord_3147920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147920).length < 2 ^ (prefixWord ++ tailWord_3147920).sum := by decide
  have hdescent : baseEnd_3147920 < baseStart_3147920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147931 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_3147931 : Nat := 118140960795 + 3147931 * 2 ^ 59
def prefixEnd_3147931 : Nat := 4983230072969 + 3 ^ 40 * 3147931 * 2
def baseEnd_3147931 : Nat := 1077601113459085626123623

theorem tailTrace_3147931 : CollatzResearch.WordTrace tailWord_3147931 prefixEnd_3147931 1077601113459085626123623 := by
  unfold tailWord_3147931
  simp only [CollatzResearch.WordTrace]
  refine ⟨114814475958591085657491647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76542983972394057104994431 114814475958591085657491647)
  ·
    refine ⟨172221713937886628486237471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114814475958591085657491647 172221713937886628486237471)
    ·
      refine ⟨258332570906829942729356207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172221713937886628486237471 258332570906829942729356207)
      ·
        refine ⟨387498856360244914094034311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258332570906829942729356207 387498856360244914094034311)
        ·
          refine ⟨581248284540367371141051467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387498856360244914094034311 581248284540367371141051467)
          ·
            refine ⟨871872426810551056711577201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581248284540367371141051467 871872426810551056711577201)
            ·
              refine ⟨653904320107913292533682901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871872426810551056711577201 653904320107913292533682901)
              ·
                refine ⟨15325882502529217793758193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 653904320107913292533682901 15325882502529217793758193)
                ·
                  refine ⟨11494411876896913345318645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15325882502529217793758193 11494411876896913345318645)
                  ·
                    refine ⟨1077601113459085626123623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11494411876896913345318645 1077601113459085626123623)
                    ·
                      rfl

theorem cell22_3147931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_3147931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147931 prefixEnd_3147931 := by exact prefixLift 3147931
  have htrace : WordTrace (prefixWord ++ tailWord_3147931) baseStart_3147931 baseEnd_3147931 := by
    simpa [prefixWord, tailWord_3147931, baseEnd_3147931] using wordTrace_append hprefix tailTrace_3147931
  have hstable : (prefixWord ++ tailWord_3147931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147931).length < 2 ^ (prefixWord ++ tailWord_3147931).sum := by decide
  have hdescent : baseEnd_3147931 < baseStart_3147931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147963 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 1, 4]
def baseStart_3147963 : Nat := 118140960795 + 3147963 * 2 ^ 59
def prefixEnd_3147963 : Nat := 4983230072969 + 3 ^ 40 * 3147963 * 2
def baseEnd_3147963 : Nat := 1077612067713048209323525

theorem tailTrace_3147963 : CollatzResearch.WordTrace tailWord_3147963 prefixEnd_3147963 1077612067713048209323525 := by
  unfold tailWord_3147963
  simp only [CollatzResearch.WordTrace]
  refine ⟨114815643094475155122656543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76543762062983436748437695 114815643094475155122656543)
  ·
    refine ⟨172223464641712732683984815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114815643094475155122656543 172223464641712732683984815)
    ·
      refine ⟨258335196962569099025977223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172223464641712732683984815 258335196962569099025977223)
      ·
        refine ⟨387502795443853648538965835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258335196962569099025977223 387502795443853648538965835)
        ·
          refine ⟨581254193165780472808448753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387502795443853648538965835 581254193165780472808448753)
          ·
            refine ⟨435940644874335354606336565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581254193165780472808448753 435940644874335354606336565)
            ·
              refine ⟨40869435456968939494344053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435940644874335354606336565 40869435456968939494344053)
              ·
                refine ⟨3831509574090838077594755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40869435456968939494344053 3831509574090838077594755)
                ·
                  refine ⟨5747264361136257116392133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831509574090838077594755 5747264361136257116392133)
                  ·
                    refine ⟨1077612067713048209323525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747264361136257116392133 1077612067713048209323525)
                    ·
                      rfl

theorem cell22_3147963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 4].length) (baseStart_3147963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147963 prefixEnd_3147963 := by exact prefixLift 3147963
  have htrace : WordTrace (prefixWord ++ tailWord_3147963) baseStart_3147963 baseEnd_3147963 := by
    simpa [prefixWord, tailWord_3147963, baseEnd_3147963] using wordTrace_append hprefix tailTrace_3147963
  have hstable : (prefixWord ++ tailWord_3147963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147963).length < 2 ^ (prefixWord ++ tailWord_3147963).sum := by decide
  have hdescent : baseEnd_3147963 < baseStart_3147963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147997 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3147997 : Nat := 118140960795 + 3147997 * 2 ^ 59
def prefixEnd_3147997 : Nat := 4983230072969 + 3 ^ 40 * 3147997 * 2
def baseEnd_3147997 : Nat := 1077623706607883453973421

theorem tailTrace_3147997 : CollatzResearch.WordTrace tailWord_3147997 prefixEnd_3147997 1077623706607883453973421 := by
  unfold tailWord_3147997
  simp only [CollatzResearch.WordTrace]
  refine ⟨114816883176351978929394245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76544588784234652619596163 114816883176351978929394245)
  ·
    refine ⟨21528165595565996049261421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114816883176351978929394245 21528165595565996049261421)
    ·
      refine ⟨8073062098337248518473033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21528165595565996049261421 8073062098337248518473033)
      ·
        refine ⟨6054796573752936388854775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8073062098337248518473033 6054796573752936388854775)
        ·
          refine ⟨9082194860629404583282163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054796573752936388854775 9082194860629404583282163)
          ·
            refine ⟨13623292290944106874923245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9082194860629404583282163 13623292290944106874923245)
            ·
              refine ⟨5108734609104040078096217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13623292290944106874923245 5108734609104040078096217)
              ·
                refine ⟨3831550956828030058572163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5108734609104040078096217 3831550956828030058572163)
                ·
                  refine ⟨5747326435242045087858245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831550956828030058572163 5747326435242045087858245)
                  ·
                    refine ⟨1077623706607883453973421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747326435242045087858245 1077623706607883453973421)
                    ·
                      rfl

theorem cell22_3147997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3147997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3147997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3147997 prefixEnd_3147997 := by exact prefixLift 3147997
  have htrace : WordTrace (prefixWord ++ tailWord_3147997) baseStart_3147997 baseEnd_3147997 := by
    simpa [prefixWord, tailWord_3147997, baseEnd_3147997] using wordTrace_append hprefix tailTrace_3147997
  have hstable : (prefixWord ++ tailWord_3147997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147997).length < 2 ^ (prefixWord ++ tailWord_3147997).sum := by decide
  have hdescent : baseEnd_3147997 < baseStart_3147997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148040 : List Nat := [2, 1, 3, 2, 3, 3, 1, 7]
def baseStart_3148040 : Nat := 118140960795 + 3148040 * 2 ^ 59
def prefixEnd_3148040 : Nat := 4983230072969 + 3 ^ 40 * 3148040 * 2
def baseEnd_3148040 : Nat := 119737602931849519460921

theorem tailTrace_3148040 : CollatzResearch.WordTrace tailWord_3148040 prefixEnd_3148040 119737602931849519460921 := by
  unfold tailWord_3148040
  simp only [CollatzResearch.WordTrace]
  refine ⟨57409225757598098636604787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76545634343464131515473049 57409225757598098636604787)
  ·
    refine ⟨86113838636397147954907181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57409225757598098636604787 86113838636397147954907181)
    ·
      refine ⟨32292689488648930483090193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86113838636397147954907181 32292689488648930483090193)
      ·
        refine ⟨24219517116486697862317645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32292689488648930483090193 24219517116486697862317645)
        ·
          refine ⟨9082318918682511698369117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24219517116486697862317645 9082318918682511698369117)
          ·
            refine ⟨3405869594505941886888419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9082318918682511698369117 3405869594505941886888419)
            ·
              refine ⟨5108804391758912830332629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405869594505941886888419 5108804391758912830332629)
              ·
                refine ⟨119737602931849519460921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5108804391758912830332629 119737602931849519460921)
                ·
                  rfl

theorem cell22_3148040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_3148040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148040 prefixEnd_3148040 := by exact prefixLift 3148040
  have htrace : WordTrace (prefixWord ++ tailWord_3148040) baseStart_3148040 baseEnd_3148040 := by
    simpa [prefixWord, tailWord_3148040, baseEnd_3148040] using wordTrace_append hprefix tailTrace_3148040
  have hstable : (prefixWord ++ tailWord_3148040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148040).length < 2 ^ (prefixWord ++ tailWord_3148040).sum := by decide
  have hdescent : baseEnd_3148040 < baseStart_3148040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148055 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 5, 3]
def baseStart_3148055 : Nat := 118140960795 + 3148055 * 2 ^ 59
def prefixEnd_3148055 : Nat := 4983230072969 + 3 ^ 40 * 3148055 * 2
def baseEnd_3148055 : Nat := 1077643561193190636023243

theorem tailTrace_3148055 : CollatzResearch.WordTrace tailWord_3148055 prefixEnd_3148055 1077643561193190636023243 := by
  unfold tailWord_3148055
  simp only [CollatzResearch.WordTrace]
  refine ⟨114818998610141854835005619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76545999073427903223337079 114818998610141854835005619)
  ·
    refine ⟨172228497915212782252508429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114818998610141854835005619 172228497915212782252508429)
    ·
      refine ⟨64585686718204793344690661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172228497915212782252508429 64585686718204793344690661)
      ·
        refine ⟨12109816259663398752129499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64585686718204793344690661 12109816259663398752129499)
        ·
          refine ⟨18164724389495098128194249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12109816259663398752129499 18164724389495098128194249)
          ·
            refine ⟨13623543292121323596145687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18164724389495098128194249 13623543292121323596145687)
            ·
              refine ⟨20435314938181985394218531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13623543292121323596145687 20435314938181985394218531)
              ·
                refine ⟨30652972407272978091327797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20435314938181985394218531 30652972407272978091327797)
                ·
                  refine ⟨2873716163181841696061981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30652972407272978091327797 2873716163181841696061981)
                  ·
                    refine ⟨1077643561193190636023243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873716163181841696061981 1077643561193190636023243)
                    ·
                      rfl

theorem cell22_3148055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_3148055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148055 prefixEnd_3148055 := by exact prefixLift 3148055
  have htrace : WordTrace (prefixWord ++ tailWord_3148055) baseStart_3148055 baseEnd_3148055 := by
    simpa [prefixWord, tailWord_3148055, baseEnd_3148055] using wordTrace_append hprefix tailTrace_3148055
  have hstable : (prefixWord ++ tailWord_3148055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148055).length < 2 ^ (prefixWord ++ tailWord_3148055).sum := by decide
  have hdescent : baseEnd_3148055 < baseStart_3148055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148078 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3148078 : Nat := 118140960795 + 3148078 * 2 ^ 59
def prefixEnd_3148078 : Nat := 4983230072969 + 3 ^ 40 * 3148078 * 2
def baseEnd_3148078 : Nat := 1077651434563226242698173

theorem tailTrace_3148078 : CollatzResearch.WordTrace tailWord_3148078 prefixEnd_3148078 1077651434563226242698173 := by
  unfold tailWord_3148078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14352479686132316220386611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76546558326039019842061925 14352479686132316220386611)
  ·
    refine ⟨21528719529198474330579917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14352479686132316220386611 21528719529198474330579917)
    ·
      refine ⟨8073269823449427873967469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21528719529198474330579917 8073269823449427873967469)
      ·
        refine ⟨3027476183793535452737801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8073269823449427873967469 3027476183793535452737801)
        ·
          refine ⟨2270607137845151589553351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3027476183793535452737801 2270607137845151589553351)
          ·
            refine ⟨3405910706767727384330027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270607137845151589553351 3405910706767727384330027)
            ·
              refine ⟨5108866060151591076495041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405910706767727384330027 5108866060151591076495041)
              ·
                refine ⟨3831649545113693307371281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5108866060151591076495041 3831649545113693307371281)
                ·
                  refine ⟨2873737158835269980528461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831649545113693307371281 2873737158835269980528461)
                  ·
                    refine ⟨1077651434563226242698173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873737158835269980528461 1077651434563226242698173)
                    ·
                      rfl

theorem cell22_3148078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3148078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148078 prefixEnd_3148078 := by exact prefixLift 3148078
  have htrace : WordTrace (prefixWord ++ tailWord_3148078) baseStart_3148078 baseEnd_3148078 := by
    simpa [prefixWord, tailWord_3148078, baseEnd_3148078] using wordTrace_append hprefix tailTrace_3148078
  have hstable : (prefixWord ++ tailWord_3148078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148078).length < 2 ^ (prefixWord ++ tailWord_3148078).sum := by decide
  have hdescent : baseEnd_3148078 < baseStart_3148078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148083 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_3148083 : Nat := 118140960795 + 3148083 * 2 ^ 59
def prefixEnd_3148083 : Nat := 4983230072969 + 3 ^ 40 * 3148083 * 2
def baseEnd_3148083 : Nat := 1077653146165407896323157

theorem tailTrace_3148083 : CollatzResearch.WordTrace tailWord_3148083 prefixEnd_3148083 1077653146165407896323157 := by
  unfold tailWord_3148083
  simp only [CollatzResearch.WordTrace]
  refine ⟨114820019854040415617024903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76546679902693610411349935 114820019854040415617024903)
  ·
    refine ⟨172230029781060623425537355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114820019854040415617024903 172230029781060623425537355)
    ·
      refine ⟨258345044671590935138306033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172230029781060623425537355 258345044671590935138306033)
      ·
        refine ⟨193758783503693201353729525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258345044671590935138306033 193758783503693201353729525)
        ·
          refine ⟨18164885953471237626912143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193758783503693201353729525 18164885953471237626912143)
          ·
            refine ⟨27247328930206856440368215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18164885953471237626912143 27247328930206856440368215)
            ·
              refine ⟨40870993395310284660552323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27247328930206856440368215 40870993395310284660552323)
              ·
                refine ⟨61306490092965426990828485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40870993395310284660552323 61306490092965426990828485)
                ·
                  refine ⟨11494966892431017560780341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61306490092965426990828485 11494966892431017560780341)
                  ·
                    refine ⟨1077653146165407896323157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11494966892431017560780341 1077653146165407896323157)
                    ·
                      rfl

theorem cell22_3148083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_3148083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148083 prefixEnd_3148083 := by exact prefixLift 3148083
  have htrace : WordTrace (prefixWord ++ tailWord_3148083) baseStart_3148083 baseEnd_3148083 := by
    simpa [prefixWord, tailWord_3148083, baseEnd_3148083] using wordTrace_append hprefix tailTrace_3148083
  have hstable : (prefixWord ++ tailWord_3148083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148083).length < 2 ^ (prefixWord ++ tailWord_3148083).sum := by decide
  have hdescent : baseEnd_3148083 < baseStart_3148083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148089 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 1, 3]
def baseStart_3148089 : Nat := 118140960795 + 3148089 * 2 ^ 59
def prefixEnd_3148089 : Nat := 4983230072969 + 3 ^ 40 * 3148089 * 2
def baseEnd_3148089 : Nat := 1077655200088025880673139

theorem tailTrace_3148089 : CollatzResearch.WordTrace tailWord_3148089 prefixEnd_3148089 1077655200088025880673139 := by
  unfold tailWord_3148089
  simp only [CollatzResearch.WordTrace]
  refine ⟨114820238692018678641743321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76546825794679119094495547 114820238692018678641743321)
  ·
    refine ⟨86115179019014008981307491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114820238692018678641743321 86115179019014008981307491)
    ·
      refine ⟨129172768528521013471961237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86115179019014008981307491 129172768528521013471961237)
      ·
        refine ⟨6054973524774422506498183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129172768528521013471961237 6054973524774422506498183)
        ·
          refine ⟨9082460287161633759747275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054973524774422506498183 9082460287161633759747275)
          ·
            refine ⟨13623690430742450639620913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9082460287161633759747275 13623690430742450639620913)
            ·
              refine ⟨10217767823056837979715685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13623690430742450639620913 10217767823056837979715685)
              ·
                refine ⟨1915831466823157121196691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10217767823056837979715685 1915831466823157121196691)
                ·
                  refine ⟨2873747200234735681795037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915831466823157121196691 2873747200234735681795037)
                  ·
                    refine ⟨1077655200088025880673139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873747200234735681795037 1077655200088025880673139)
                    ·
                      rfl

theorem cell22_3148089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_3148089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148089 prefixEnd_3148089 := by exact prefixLift 3148089
  have htrace : WordTrace (prefixWord ++ tailWord_3148089) baseStart_3148089 baseEnd_3148089 := by
    simpa [prefixWord, tailWord_3148089, baseEnd_3148089] using wordTrace_append hprefix tailTrace_3148089
  have hstable : (prefixWord ++ tailWord_3148089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148089).length < 2 ^ (prefixWord ++ tailWord_3148089).sum := by decide
  have hdescent : baseEnd_3148089 < baseStart_3148089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148143 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_3148143 : Nat := 118140960795 + 3148143 * 2 ^ 59
def prefixEnd_3148143 : Nat := 4983230072969 + 3 ^ 40 * 3148143 * 2
def baseEnd_3148143 : Nat := 1077673685391587739822973

theorem tailTrace_3148143 : CollatzResearch.WordTrace tailWord_3148143 prefixEnd_3148143 1077673685391587739822973 := by
  unfold tailWord_3148143
  simp only [CollatzResearch.WordTrace]
  refine ⟨114822208233823045864209083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76548138822548697242806055 114822208233823045864209083)
  ·
    refine ⟨172233312350734568796313625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114822208233823045864209083 172233312350734568796313625)
    ·
      refine ⟨129174984263050926597235219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172233312350734568796313625 129174984263050926597235219)
      ·
        refine ⟨193762476394576389895852829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129174984263050926597235219 193762476394576389895852829)
        ·
          refine ⟨72660928647966146210944811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193762476394576389895852829 72660928647966146210944811)
          ·
            refine ⟨108991392971949219316417217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72660928647966146210944811 108991392971949219316417217)
            ·
              refine ⟨81743544728961914487312913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108991392971949219316417217 81743544728961914487312913)
              ·
                refine ⟨61307658546721435865484685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81743544728961914487312913 61307658546721435865484685)
                ·
                  refine ⟨22990371955020538449556757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61307658546721435865484685 22990371955020538449556757)
                  ·
                    refine ⟨1077673685391587739822973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22990371955020538449556757 1077673685391587739822973)
                    ·
                      rfl

theorem cell22_3148143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_3148143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148143 prefixEnd_3148143 := by exact prefixLift 3148143
  have htrace : WordTrace (prefixWord ++ tailWord_3148143) baseStart_3148143 baseEnd_3148143 := by
    simpa [prefixWord, tailWord_3148143, baseEnd_3148143] using wordTrace_append hprefix tailTrace_3148143
  have hstable : (prefixWord ++ tailWord_3148143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148143).length < 2 ^ (prefixWord ++ tailWord_3148143).sum := by decide
  have hdescent : baseEnd_3148143 < baseStart_3148143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148258 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3148258 : Nat := 118140960795 + 3148258 * 2 ^ 59
def prefixEnd_3148258 : Nat := 4983230072969 + 3 ^ 40 * 3148258 * 2
def baseEnd_3148258 : Nat := 1077713052241765773197621

theorem tailTrace_3148258 : CollatzResearch.WordTrace tailWord_3148258 prefixEnd_3148258 1077713052241765773197621 := by
  unfold tailWord_3148258
  simp only [CollatzResearch.WordTrace]
  refine ⟨28706600657101605126161357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76550935085604280336430285 28706600657101605126161357)
  ·
    refine ⟨10764975246413101922310509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28706600657101605126161357 10764975246413101922310509)
    ·
      refine ⟨4036865717404913220866441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10764975246413101922310509 4036865717404913220866441)
      ·
        refine ⟨3027649288053684915649831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4036865717404913220866441 3027649288053684915649831)
        ·
          refine ⟨4541473932080527373474747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027649288053684915649831 4541473932080527373474747)
          ·
            refine ⟨6812210898120791060212121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541473932080527373474747 6812210898120791060212121)
            ·
              refine ⟨5109158173590593295159091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6812210898120791060212121 5109158173590593295159091)
              ·
                refine ⟨7663737260385889942738637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5109158173590593295159091 7663737260385889942738637)
                ·
                  refine ⟨2873901472644708728526989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7663737260385889942738637 2873901472644708728526989)
                  ·
                    refine ⟨1077713052241765773197621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2873901472644708728526989 1077713052241765773197621)
                    ·
                      rfl

theorem cell22_3148258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3148258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148258 prefixEnd_3148258 := by exact prefixLift 3148258
  have htrace : WordTrace (prefixWord ++ tailWord_3148258) baseStart_3148258 baseEnd_3148258 := by
    simpa [prefixWord, tailWord_3148258, baseEnd_3148258] using wordTrace_append hprefix tailTrace_3148258
  have hstable : (prefixWord ++ tailWord_3148258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148258).length < 2 ^ (prefixWord ++ tailWord_3148258).sum := by decide
  have hdescent : baseEnd_3148258 < baseStart_3148258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148299 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 4]
def baseStart_3148299 : Nat := 118140960795 + 3148299 * 2 ^ 59
def prefixEnd_3148299 : Nat := 4983230072969 + 3 ^ 40 * 3148299 * 2
def baseEnd_3148299 : Nat := 359242362459885110974165

theorem tailTrace_3148299 : CollatzResearch.WordTrace tailWord_3148299 prefixEnd_3148299 359242362459885110974165 := by
  unfold tailWord_3148299
  simp only [CollatzResearch.WordTrace]
  refine ⟨114827898021257884506887951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76551932014171923004591967 114827898021257884506887951)
  ·
    refine ⟨172241847031886826760331927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114827898021257884506887951 172241847031886826760331927)
    ·
      refine ⟨258362770547830240140497891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172241847031886826760331927 258362770547830240140497891)
      ·
        refine ⟨387544155821745360210746837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258362770547830240140497891 387544155821745360210746837)
        ·
          refine ⟨9083066152072156879939379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 387544155821745360210746837 9083066152072156879939379)
          ·
            refine ⟨13624599228108235319909069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083066152072156879939379 13624599228108235319909069)
            ·
              refine ⟨5109224710540588244965901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13624599228108235319909069 5109224710540588244965901)
              ·
                refine ⟨1915959266452720591862213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5109224710540588244965901 1915959266452720591862213)
                ·
                  refine ⟨359242362459885110974165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915959266452720591862213 359242362459885110974165)
                  ·
                    rfl

theorem cell22_3148299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 4].length) (baseStart_3148299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148299 prefixEnd_3148299 := by exact prefixLift 3148299
  have htrace : WordTrace (prefixWord ++ tailWord_3148299) baseStart_3148299 baseEnd_3148299 := by
    simpa [prefixWord, tailWord_3148299, baseEnd_3148299] using wordTrace_append hprefix tailTrace_3148299
  have hstable : (prefixWord ++ tailWord_3148299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148299).length < 2 ^ (prefixWord ++ tailWord_3148299).sum := by decide
  have hdescent : baseEnd_3148299 < baseStart_3148299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148312 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_3148312 : Nat := 118140960795 + 3148312 * 2 ^ 59
def prefixEnd_3148312 : Nat := 4983230072969 + 3 ^ 40 * 3148312 * 2
def baseEnd_3148312 : Nat := 1077731537545327632347455

theorem tailTrace_3148312 : CollatzResearch.WordTrace tailWord_3148312 prefixEnd_3148312 1077731537545327632347455 := by
  unfold tailWord_3148312
  simp only [CollatzResearch.WordTrace]
  refine ⟨57414186085105393863555595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76552248113473858484740793 57414186085105393863555595)
  ·
    refine ⟨86121279127658090795333393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57414186085105393863555595 86121279127658090795333393)
    ·
      refine ⟨64590959345743568096500045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86121279127658090795333393 64590959345743568096500045)
      ·
        refine ⟨24221609754653838036187517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64590959345743568096500045 24221609754653838036187517)
        ·
          refine ⟨9083103657995189263570319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24221609754653838036187517 9083103657995189263570319)
          ·
            refine ⟨13624655486992783895355479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083103657995189263570319 13624655486992783895355479)
            ·
              refine ⟨20436983230489175843033219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13624655486992783895355479 20436983230489175843033219)
              ·
                refine ⟨30655474845733763764549829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20436983230489175843033219 30655474845733763764549829)
                ·
                  refine ⟨5747901533575080705853093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30655474845733763764549829 5747901533575080705853093)
                  ·
                    refine ⟨1077731537545327632347455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747901533575080705853093 1077731537545327632347455)
                    ·
                      rfl

theorem cell22_3148312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_3148312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148312 prefixEnd_3148312 := by exact prefixLift 3148312
  have htrace : WordTrace (prefixWord ++ tailWord_3148312) baseStart_3148312 baseEnd_3148312 := by
    simpa [prefixWord, tailWord_3148312, baseEnd_3148312] using wordTrace_append hprefix tailTrace_3148312
  have hstable : (prefixWord ++ tailWord_3148312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148312).length < 2 ^ (prefixWord ++ tailWord_3148312).sum := by decide
  have hdescent : baseEnd_3148312 < baseStart_3148312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148316 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 4]
def baseStart_3148316 : Nat := 118140960795 + 3148316 * 2 ^ 59
def prefixEnd_3148316 : Nat := 4983230072969 + 3 ^ 40 * 3148316 * 2
def baseEnd_3148316 : Nat := 359244302275690985082481

theorem tailTrace_3148316 : CollatzResearch.WordTrace tailWord_3148316 prefixEnd_3148316 359244302275690985082481 := by
  unfold tailWord_3148316
  simp only [CollatzResearch.WordTrace]
  refine ⟨57414259031098148205128401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76552345374797530940171201 57414259031098148205128401)
  ·
    refine ⟨43060694273323611153846301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57414259031098148205128401 43060694273323611153846301)
    ·
      refine ⟨16147760352496354182692363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43060694273323611153846301 16147760352496354182692363)
      ·
        refine ⟨24221640528744531274038545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16147760352496354182692363 24221640528744531274038545)
        ·
          refine ⟨18166230396558398455528909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24221640528744531274038545 18166230396558398455528909)
          ·
            refine ⟨6812336398709399420823341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18166230396558398455528909 6812336398709399420823341)
            ·
              refine ⟨2554626149516024782808753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6812336398709399420823341 2554626149516024782808753)
              ·
                refine ⟨1915969612137018587106565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554626149516024782808753 1915969612137018587106565)
                ·
                  refine ⟨359244302275690985082481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915969612137018587106565 359244302275690985082481)
                  ·
                    rfl

theorem cell22_3148316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_3148316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148316 prefixEnd_3148316 := by exact prefixLift 3148316
  have htrace : WordTrace (prefixWord ++ tailWord_3148316) baseStart_3148316 baseEnd_3148316 := by
    simpa [prefixWord, tailWord_3148316, baseEnd_3148316] using wordTrace_append hprefix tailTrace_3148316
  have hstable : (prefixWord ++ tailWord_3148316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148316).length < 2 ^ (prefixWord ++ tailWord_3148316).sum := by decide
  have hdescent : baseEnd_3148316 < baseStart_3148316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148355 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 9]
def baseStart_3148355 : Nat := 118140960795 + 3148355 * 2 ^ 59
def prefixEnd_3148355 : Nat := 4983230072969 + 3 ^ 40 * 3148355 * 2
def baseEnd_3148355 : Nat := 359248752441363284507441

theorem tailTrace_3148355 : CollatzResearch.WordTrace tailWord_3148355 prefixEnd_3148355 359248752441363284507441 := by
  unfold tailWord_3148355
  simp only [CollatzResearch.WordTrace]
  refine ⟨114829940509055006070926519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76553293672703337380617679 114829940509055006070926519)
  ·
    refine ⟨172244910763582509106389779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114829940509055006070926519 172244910763582509106389779)
    ·
      refine ⟨258367366145373763659584669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172244910763582509106389779 258367366145373763659584669)
      ·
        refine ⟨96887762304515161372344251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258367366145373763659584669 96887762304515161372344251)
        ·
          refine ⟨145331643456772742058516377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96887762304515161372344251 145331643456772742058516377)
          ·
            refine ⟨108998732592579556543887283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145331643456772742058516377 108998732592579556543887283)
            ·
              refine ⟨163498098888869334815830925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108998732592579556543887283 163498098888869334815830925)
              ·
                refine ⟨61311787083326000555936597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163498098888869334815830925 61311787083326000555936597)
                ·
                  refine ⟨359248752441363284507441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61311787083326000555936597 359248752441363284507441)
                  ·
                    rfl

theorem cell22_3148355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_3148355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148355 prefixEnd_3148355 := by exact prefixLift 3148355
  have htrace : WordTrace (prefixWord ++ tailWord_3148355) baseStart_3148355 baseEnd_3148355 := by
    simpa [prefixWord, tailWord_3148355, baseEnd_3148355] using wordTrace_append hprefix tailTrace_3148355
  have hstable : (prefixWord ++ tailWord_3148355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148355).length < 2 ^ (prefixWord ++ tailWord_3148355).sum := by decide
  have hdescent : baseEnd_3148355 < baseStart_3148355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148387 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 2, 5]
def baseStart_3148387 : Nat := 118140960795 + 3148387 * 2 ^ 59
def prefixEnd_3148387 : Nat := 4983230072969 + 3 ^ 40 * 3148387 * 2
def baseEnd_3148387 : Nat := 1077757211578052436722225

theorem tailTrace_3148387 : CollatzResearch.WordTrace tailWord_3148387 prefixEnd_3148387 1077757211578052436722225 := by
  unfold tailWord_3148387
  simp only [CollatzResearch.WordTrace]
  refine ⟨114831107644939075536091415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76554071763292717024060943 114831107644939075536091415)
  ·
    refine ⟨172246661467408613304137123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114831107644939075536091415 172246661467408613304137123)
    ·
      refine ⟨258369992201112919956205685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172246661467408613304137123 258369992201112919956205685)
      ·
        refine ⟨24222186768854336245894283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258369992201112919956205685 24222186768854336245894283)
        ·
          refine ⟨36333280153281504368841425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24222186768854336245894283 36333280153281504368841425)
          ·
            refine ⟨27249960114961128276631069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36333280153281504368841425 27249960114961128276631069)
            ·
              refine ⟨10218735043110423103736651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27249960114961128276631069 10218735043110423103736651)
              ·
                refine ⟨15328102564665634655604977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10218735043110423103736651 15328102564665634655604977)
                ·
                  refine ⟨11496076923499225991703733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15328102564665634655604977 11496076923499225991703733)
                  ·
                    refine ⟨1077757211578052436722225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11496076923499225991703733 1077757211578052436722225)
                    ·
                      rfl

theorem cell22_3148387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_3148387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148387 prefixEnd_3148387 := by exact prefixLift 3148387
  have htrace : WordTrace (prefixWord ++ tailWord_3148387) baseStart_3148387 baseEnd_3148387 := by
    simpa [prefixWord, tailWord_3148387, baseEnd_3148387] using wordTrace_append hprefix tailTrace_3148387
  have hstable : (prefixWord ++ tailWord_3148387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148387).length < 2 ^ (prefixWord ++ tailWord_3148387).sum := by decide
  have hdescent : baseEnd_3148387 < baseStart_3148387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148417 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 8]
def baseStart_3148417 : Nat := 118140960795 + 3148417 * 2 ^ 59
def prefixEnd_3148417 : Nat := 4983230072969 + 3 ^ 40 * 3148417 * 2
def baseEnd_3148417 : Nat := 359255827063714119490711

theorem tailTrace_3148417 : CollatzResearch.WordTrace tailWord_3148417 prefixEnd_3148417 359255827063714119490711 := by
  unfold tailWord_3148417
  simp only [CollatzResearch.WordTrace]
  refine ⟨114832201834830390659683505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76554801223220260439789003 114832201834830390659683505)
  ·
    refine ⟨86124151376122792994762629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114832201834830390659683505 86124151376122792994762629)
    ·
      refine ⟨16148278383023023686517993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86124151376122792994762629 16148278383023023686517993)
      ·
        refine ⟨12111208787267267764888495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16148278383023023686517993 12111208787267267764888495)
        ·
          refine ⟨18166813180900901647332743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12111208787267267764888495 18166813180900901647332743)
          ·
            refine ⟨27250219771351352470999115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18166813180900901647332743 27250219771351352470999115)
            ·
              refine ⟨40875329657027028706498673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27250219771351352470999115 40875329657027028706498673)
              ·
                refine ⟨30656497242770271529874005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40875329657027028706498673 30656497242770271529874005)
                ·
                  refine ⟨359255827063714119490711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30656497242770271529874005 359255827063714119490711)
                  ·
                    rfl

theorem cell22_3148417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_3148417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148417 prefixEnd_3148417 := by exact prefixLift 3148417
  have htrace : WordTrace (prefixWord ++ tailWord_3148417) baseStart_3148417 baseEnd_3148417 := by
    simpa [prefixWord, tailWord_3148417, baseEnd_3148417] using wordTrace_append hprefix tailTrace_3148417
  have hstable : (prefixWord ++ tailWord_3148417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148417).length < 2 ^ (prefixWord ++ tailWord_3148417).sum := by decide
  have hdescent : baseEnd_3148417 < baseStart_3148417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148434 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_3148434 : Nat := 118140960795 + 3148434 * 2 ^ 59
def prefixEnd_3148434 : Nat := 4983230072969 + 3 ^ 40 * 3148434 * 2
def baseEnd_3148434 : Nat := 359257766879519993599027

theorem tailTrace_3148434 : CollatzResearch.WordTrace tailWord_3148434 prefixEnd_3148434 359257766879519993599027 := by
  unfold tailWord_3148434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28708205468942200640763089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76555214583845868375368237 28708205468942200640763089)
  ·
    refine ⟨21531154101706650480572317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28708205468942200640763089 21531154101706650480572317)
    ·
      refine ⟨8074182788139993930214619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21531154101706650480572317 8074182788139993930214619)
      ·
        refine ⟨12111274182209990895321929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8074182788139993930214619 12111274182209990895321929)
        ·
          refine ⟨9083455636657493171491447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12111274182209990895321929 9083455636657493171491447)
          ·
            refine ⟨13625183454986239757237171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083455636657493171491447 13625183454986239757237171)
            ·
              refine ⟨20437775182479359635855757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13625183454986239757237171 20437775182479359635855757)
              ·
                refine ⟨7664165693429759863445909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20437775182479359635855757 7664165693429759863445909)
                ·
                  refine ⟨359257766879519993599027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7664165693429759863445909 359257766879519993599027)
                  ·
                    rfl

theorem cell22_3148434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_3148434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148434 prefixEnd_3148434 := by exact prefixLift 3148434
  have htrace : WordTrace (prefixWord ++ tailWord_3148434) baseStart_3148434 baseEnd_3148434 := by
    simpa [prefixWord, tailWord_3148434, baseEnd_3148434] using wordTrace_append hprefix tailTrace_3148434
  have hstable : (prefixWord ++ tailWord_3148434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148434).length < 2 ^ (prefixWord ++ tailWord_3148434).sum := by decide
  have hdescent : baseEnd_3148434 < baseStart_3148434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148554 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_3148554 : Nat := 118140960795 + 3148554 * 2 ^ 59
def prefixEnd_3148554 : Nat := 4983230072969 + 3 ^ 40 * 3148554 * 2
def baseEnd_3148554 : Nat := 1077814379090919667796713

theorem tailTrace_3148554 : CollatzResearch.WordTrace tailWord_3148554 prefixEnd_3148554 1077814379090919667796713 := by
  unfold tailWord_3148554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28709299658833515764355179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76558132423556042038280477 28709299658833515764355179)
  ·
    refine ⟨43063949488250273646532769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28709299658833515764355179 43063949488250273646532769)
    ·
      refine ⟨32297962116187705234899577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43063949488250273646532769 32297962116187705234899577)
      ·
        refine ⟨24223471587140778926174683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32297962116187705234899577 24223471587140778926174683)
        ·
          refine ⟨36335207380711168389262025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24223471587140778926174683 36335207380711168389262025)
          ·
            refine ⟨27251405535533376291946519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36335207380711168389262025 27251405535533376291946519)
            ·
              refine ⟨40877108303300064437919779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27251405535533376291946519 40877108303300064437919779)
              ·
                refine ⟨61315662454950096656879669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40877108303300064437919779 61315662454950096656879669)
                ·
                  refine ⟨5748343355151571561582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61315662454950096656879669 5748343355151571561582469)
                  ·
                    refine ⟨1077814379090919667796713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5748343355151571561582469 1077814379090919667796713)
                    ·
                      rfl

theorem cell22_3148554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_3148554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148554 prefixEnd_3148554 := by exact prefixLift 3148554
  have htrace : WordTrace (prefixWord ++ tailWord_3148554) baseStart_3148554 baseEnd_3148554 := by
    simpa [prefixWord, tailWord_3148554, baseEnd_3148554] using wordTrace_append hprefix tailTrace_3148554
  have hstable : (prefixWord ++ tailWord_3148554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148554).length < 2 ^ (prefixWord ++ tailWord_3148554).sum := by decide
  have hdescent : baseEnd_3148554 < baseStart_3148554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148599 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3148599 : Nat := 118140960795 + 3148599 * 2 ^ 59
def prefixEnd_3148599 : Nat := 4983230072969 + 3 ^ 40 * 3148599 * 2
def baseEnd_3148599 : Nat := 1077829783510554550421575

theorem tailTrace_3148599 : CollatzResearch.WordTrace tailWord_3148599 prefixEnd_3148599 1077829783510554550421575 := by
  unfold tailWord_3148599
  simp only [CollatzResearch.WordTrace]
  refine ⟨114838839920171035742808851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76559226613447357161872567 114838839920171035742808851)
  ·
    refine ⟨172258259880256553614213277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114838839920171035742808851 172258259880256553614213277)
    ·
      refine ⟨64596847455096207605329979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172258259880256553614213277 64596847455096207605329979)
      ·
        refine ⟨96895271182644311407994969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64596847455096207605329979 96895271182644311407994969)
        ·
          refine ⟨72671453386983233555996227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96895271182644311407994969 72671453386983233555996227)
          ·
            refine ⟨109007180080474850333994341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72671453386983233555996227 109007180080474850333994341)
            ·
              refine ⟨20438846265089034437623939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109007180080474850333994341 20438846265089034437623939)
              ·
                refine ⟨30658269397633551656435909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20438846265089034437623939 30658269397633551656435909)
                ·
                  refine ⟨5748425512056290935581733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30658269397633551656435909 5748425512056290935581733)
                  ·
                    refine ⟨1077829783510554550421575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5748425512056290935581733 1077829783510554550421575)
                    ·
                      rfl

theorem cell22_3148599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3148599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148599 prefixEnd_3148599 := by exact prefixLift 3148599
  have htrace : WordTrace (prefixWord ++ tailWord_3148599) baseStart_3148599 baseEnd_3148599 := by
    simpa [prefixWord, tailWord_3148599, baseEnd_3148599] using wordTrace_append hprefix tailTrace_3148599
  have hstable : (prefixWord ++ tailWord_3148599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148599).length < 2 ^ (prefixWord ++ tailWord_3148599).sum := by decide
  have hdescent : baseEnd_3148599 < baseStart_3148599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148629 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3148629 : Nat := 118140960795 + 3148629 * 2 ^ 59
def prefixEnd_3148629 : Nat := 4983230072969 + 3 ^ 40 * 3148629 * 2
def baseEnd_3148629 : Nat := 1077840053123644472171483

theorem tailTrace_3148629 : CollatzResearch.WordTrace tailWord_3148629 prefixEnd_3148629 1077840053123644472171483 := by
  unfold tailWord_3148629
  simp only [CollatzResearch.WordTrace]
  refine ⟨114839934110062350866400941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76559956073374900577600627 114839934110062350866400941)
  ·
    refine ⟨43064975291273381574900353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114839934110062350866400941 43064975291273381574900353)
    ·
      refine ⟨32298731468455036181175265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43064975291273381574900353 32298731468455036181175265)
      ·
        refine ⟨24224048601341277135881449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32298731468455036181175265 24224048601341277135881449)
        ·
          refine ⟨18168036451005957851911087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24224048601341277135881449 18168036451005957851911087)
          ·
            refine ⟨27252054676508936777866631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18168036451005957851911087 27252054676508936777866631)
            ·
              refine ⟨40878082014763405166799947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27252054676508936777866631 40878082014763405166799947)
              ·
                refine ⟨61317123022145107750199921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40878082014763405166799947 61317123022145107750199921)
                ·
                  refine ⟨45987842266608830812649941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61317123022145107750199921 45987842266608830812649941)
                  ·
                    refine ⟨1077840053123644472171483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45987842266608830812649941 1077840053123644472171483)
                    ·
                      rfl

theorem cell22_3148629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3148629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148629 prefixEnd_3148629 := by exact prefixLift 3148629
  have htrace : WordTrace (prefixWord ++ tailWord_3148629) baseStart_3148629 baseEnd_3148629 := by
    simpa [prefixWord, tailWord_3148629, baseEnd_3148629] using wordTrace_append hprefix tailTrace_3148629
  have hstable : (prefixWord ++ tailWord_3148629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148629).length < 2 ^ (prefixWord ++ tailWord_3148629).sum := by decide
  have hdescent : baseEnd_3148629 < baseStart_3148629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148631 : List Nat := [1, 1, 3, 2, 4, 1, 4, 6]
def baseStart_3148631 : Nat := 118140960795 + 3148631 * 2 ^ 59
def prefixEnd_3148631 : Nat := 4983230072969 + 3 ^ 40 * 3148631 * 2
def baseEnd_3148631 : Nat := 119760081973835237069053

theorem tailTrace_3148631 : CollatzResearch.WordTrace tailWord_3148631 prefixEnd_3148631 119760081973835237069053 := by
  unfold tailWord_3148631
  simp only [CollatzResearch.WordTrace]
  refine ⟨114840007056055105207973747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76560004704036736805315831 114840007056055105207973747)
  ·
    refine ⟨172260010584082657811960621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114840007056055105207973747 172260010584082657811960621)
    ·
      refine ⟨64597503969030996679485233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172260010584082657811960621 64597503969030996679485233)
      ·
        refine ⟨48448127976773247509613925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64597503969030996679485233 48448127976773247509613925)
        ·
          refine ⟨9084023995644983908052611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48448127976773247509613925 9084023995644983908052611)
          ·
            refine ⟨13626035993467475862078917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084023995644983908052611 13626035993467475862078917)
            ·
              refine ⟨2554881748775151724139797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13626035993467475862078917 2554881748775151724139797)
              ·
                refine ⟨119760081973835237069053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2554881748775151724139797 119760081973835237069053)
                ·
                  rfl

theorem cell22_3148631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 6].length) (baseStart_3148631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148631 prefixEnd_3148631 := by exact prefixLift 3148631
  have htrace : WordTrace (prefixWord ++ tailWord_3148631) baseStart_3148631 baseEnd_3148631 := by
    simpa [prefixWord, tailWord_3148631, baseEnd_3148631] using wordTrace_append hprefix tailTrace_3148631
  have hstable : (prefixWord ++ tailWord_3148631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148631).length < 2 ^ (prefixWord ++ tailWord_3148631).sum := by decide
  have hdescent : baseEnd_3148631 < baseStart_3148631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148659 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 7]
def baseStart_3148659 : Nat := 118140960795 + 3148659 * 2 ^ 59
def prefixEnd_3148659 : Nat := 4983230072969 + 3 ^ 40 * 3148659 * 2
def baseEnd_3148659 : Nat := 359283440912244797973797

theorem tailTrace_3148659 : CollatzResearch.WordTrace tailWord_3148659 prefixEnd_3148659 359283440912244797973797 := by
  unfold tailWord_3148659
  simp only [CollatzResearch.WordTrace]
  refine ⟨114841028299953665989993031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76560685533302443993328687 114841028299953665989993031)
  ·
    refine ⟨172261542449930498984989547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114841028299953665989993031 172261542449930498984989547)
    ·
      refine ⟨258392313674895748477484321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172261542449930498984989547 258392313674895748477484321)
      ·
        refine ⟨193794235256171811358113241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258392313674895748477484321 193794235256171811358113241)
        ·
          refine ⟨145345676442128858518584931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193794235256171811358113241 145345676442128858518584931)
          ·
            refine ⟨218018514663193287777877397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145345676442128858518584931 218018514663193287777877397)
            ·
              refine ⟨10219617874837185364588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 218018514663193287777877397 10219617874837185364588003)
              ·
                refine ⟨15329426812255778046882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219617874837185364588003 15329426812255778046882005)
                ·
                  refine ⟨359283440912244797973797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15329426812255778046882005 359283440912244797973797)
                  ·
                    rfl

theorem cell22_3148659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_3148659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148659 prefixEnd_3148659 := by exact prefixLift 3148659
  have htrace : WordTrace (prefixWord ++ tailWord_3148659) baseStart_3148659 baseEnd_3148659 := by
    simpa [prefixWord, tailWord_3148659, baseEnd_3148659] using wordTrace_append hprefix tailTrace_3148659
  have hstable : (prefixWord ++ tailWord_3148659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148659).length < 2 ^ (prefixWord ++ tailWord_3148659).sum := by decide
  have hdescent : baseEnd_3148659 < baseStart_3148659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148663 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 1, 3]
def baseStart_3148663 : Nat := 118140960795 + 3148663 * 2 ^ 59
def prefixEnd_3148663 : Nat := 4983230072969 + 3 ^ 40 * 3148663 * 2
def baseEnd_3148663 : Nat := 1077851692018479716821379

theorem tailTrace_3148663 : CollatzResearch.WordTrace tailWord_3148663 prefixEnd_3148663 1077851692018479716821379 := by
  unfold tailWord_3148663
  simp only [CollatzResearch.WordTrace]
  refine ⟨114841174191939174673138643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76560782794626116448759095 114841174191939174673138643)
  ·
    refine ⟨172261761287908762009707965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114841174191939174673138643 172261761287908762009707965)
    ·
      refine ⟨64598160482965785753640487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172261761287908762009707965 64598160482965785753640487)
      ·
        refine ⟨96897240724448678630460731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64598160482965785753640487 96897240724448678630460731)
        ·
          refine ⟨145345861086673017945691097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96897240724448678630460731 145345861086673017945691097)
          ·
            refine ⟨109009395815004763459268323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145345861086673017945691097 109009395815004763459268323)
            ·
              refine ⟨163514093722507145188902485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109009395815004763459268323 163514093722507145188902485)
              ·
                refine ⟨1916180785810630607682451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 163514093722507145188902485 1916180785810630607682451)
                ·
                  refine ⟨2874271178715945911523677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916180785810630607682451 2874271178715945911523677)
                  ·
                    refine ⟨1077851692018479716821379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2874271178715945911523677 1077851692018479716821379)
                    ·
                      rfl

theorem cell22_3148663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_3148663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148663 prefixEnd_3148663 := by exact prefixLift 3148663
  have htrace : WordTrace (prefixWord ++ tailWord_3148663) baseStart_3148663 baseEnd_3148663 := by
    simpa [prefixWord, tailWord_3148663, baseEnd_3148663] using wordTrace_append hprefix tailTrace_3148663
  have hstable : (prefixWord ++ tailWord_3148663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148663).length < 2 ^ (prefixWord ++ tailWord_3148663).sum := by decide
  have hdescent : baseEnd_3148663 < baseStart_3148663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148736 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_3148736 : Nat := 118140960795 + 3148736 * 2 ^ 59
def prefixEnd_3148736 : Nat := 4983230072969 + 3 ^ 40 * 3148736 * 2
def baseEnd_3148736 : Nat := 1077876681410331859746155

theorem tailTrace_3148736 : CollatzResearch.WordTrace tailWord_3148736 prefixEnd_3148736 1077876681410331859746155 := by
  unfold tailWord_3148736
  simp only [CollatzResearch.WordTrace]
  refine ⟨57421918360337354070273031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76562557813783138760364041 57421918360337354070273031)
  ·
    refine ⟨86132877540506031105409547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57421918360337354070273031 86132877540506031105409547)
    ·
      refine ⟨129199316310759046658114321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86132877540506031105409547 129199316310759046658114321)
      ·
        refine ⟨96899487233069284993585741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129199316310759046658114321 96899487233069284993585741)
        ·
          refine ⟨36337307712400981872594653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96899487233069284993585741 36337307712400981872594653)
          ·
            refine ⟨13626490392150368202222995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36337307712400981872594653 13626490392150368202222995)
            ·
              refine ⟨20439735588225552303334493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626490392150368202222995 20439735588225552303334493)
              ·
                refine ⟨7664900845584582113750435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20439735588225552303334493 7664900845584582113750435)
                ·
                  refine ⟨11497351268376873170625653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7664900845584582113750435 11497351268376873170625653)
                  ·
                    refine ⟨1077876681410331859746155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11497351268376873170625653 1077876681410331859746155)
                    ·
                      rfl

theorem cell22_3148736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_3148736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148736 prefixEnd_3148736 := by exact prefixLift 3148736
  have htrace : WordTrace (prefixWord ++ tailWord_3148736) baseStart_3148736 baseEnd_3148736 := by
    simpa [prefixWord, tailWord_3148736, baseEnd_3148736] using wordTrace_append hprefix tailTrace_3148736
  have hstable : (prefixWord ++ tailWord_3148736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148736).length < 2 ^ (prefixWord ++ tailWord_3148736).sum := by decide
  have hdescent : baseEnd_3148736 < baseStart_3148736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148751 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 1, 6]
def baseStart_3148751 : Nat := 118140960795 + 3148751 * 2 ^ 59
def prefixEnd_3148751 : Nat := 4983230072969 + 3 ^ 40 * 3148751 * 2
def baseEnd_3148751 : Nat := 1077881816216876820621109

theorem tailTrace_3148751 : CollatzResearch.WordTrace tailWord_3148751 prefixEnd_3148751 1077881816216876820621109 := by
  unfold tailWord_3148751
  simp only [CollatzResearch.WordTrace]
  refine ⟨114844383815620365702342107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76562922543746910468228071 114844383815620365702342107)
  ·
    refine ⟨172266575723430548553513161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114844383815620365702342107 172266575723430548553513161)
    ·
      refine ⟨129199931792572911415134871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172266575723430548553513161 129199931792572911415134871)
      ·
        refine ⟨193799897688859367122702307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129199931792572911415134871 193799897688859367122702307)
        ·
          refine ⟨290699846533289050684053461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193799897688859367122702307 290699846533289050684053461)
          ·
            refine ⟨6813277653123962125407503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 290699846533289050684053461 6813277653123962125407503)
            ·
              refine ⟨10219916479685943188111255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813277653123962125407503 10219916479685943188111255)
              ·
                refine ⟨15329874719528914782166883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219916479685943188111255 15329874719528914782166883)
                ·
                  refine ⟨22994812079293372173250325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15329874719528914782166883 22994812079293372173250325)
                  ·
                    refine ⟨1077881816216876820621109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22994812079293372173250325 1077881816216876820621109)
                    ·
                      rfl

theorem cell22_3148751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_3148751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148751 prefixEnd_3148751 := by exact prefixLift 3148751
  have htrace : WordTrace (prefixWord ++ tailWord_3148751) baseStart_3148751 baseEnd_3148751 := by
    simpa [prefixWord, tailWord_3148751, baseEnd_3148751] using wordTrace_append hprefix tailTrace_3148751
  have hstable : (prefixWord ++ tailWord_3148751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148751).length < 2 ^ (prefixWord ++ tailWord_3148751).sum := by decide
  have hdescent : baseEnd_3148751 < baseStart_3148751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148757 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_3148757 : Nat := 118140960795 + 3148757 * 2 ^ 59
def prefixEnd_3148757 : Nat := 4983230072969 + 3 ^ 40 * 3148757 * 2
def baseEnd_3148757 : Nat := 1077883870139494804971091

theorem tailTrace_3148757 : CollatzResearch.WordTrace tailWord_3148757 prefixEnd_3148757 1077883870139494804971091 := by
  unfold tailWord_3148757
  simp only [CollatzResearch.WordTrace]
  refine ⟨114844602653598628727060525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76563068435732419151373683 114844602653598628727060525)
  ·
    refine ⟨43066725995099485772647697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114844602653598628727060525 43066725995099485772647697)
    ·
      refine ⟨32300044496324614329485773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43066725995099485772647697 32300044496324614329485773)
      ·
        refine ⟨12112516686121730373557165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32300044496324614329485773 12112516686121730373557165)
        ·
          refine ⟨4542193757295648890083937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12112516686121730373557165 4542193757295648890083937)
          ·
            refine ⟨3406645317971736667562953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4542193757295648890083937 3406645317971736667562953)
            ·
              refine ⟨2554983988478802500672215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406645317971736667562953 2554983988478802500672215)
              ·
                refine ⟨3832475982718203751008323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554983988478802500672215 3832475982718203751008323)
                ·
                  refine ⟨5748713974077305626512485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832475982718203751008323 5748713974077305626512485)
                  ·
                    refine ⟨1077883870139494804971091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5748713974077305626512485 1077883870139494804971091)
                    ·
                      rfl

theorem cell22_3148757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_3148757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148757 prefixEnd_3148757 := by exact prefixLift 3148757
  have htrace : WordTrace (prefixWord ++ tailWord_3148757) baseStart_3148757 baseEnd_3148757 := by
    simpa [prefixWord, tailWord_3148757, baseEnd_3148757] using wordTrace_append hprefix tailTrace_3148757
  have hstable : (prefixWord ++ tailWord_3148757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148757).length < 2 ^ (prefixWord ++ tailWord_3148757).sum := by decide
  have hdescent : baseEnd_3148757 < baseStart_3148757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148811 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 7]
def baseStart_3148811 : Nat := 118140960795 + 3148811 * 2 ^ 59
def prefixEnd_3148811 : Nat := 4983230072969 + 3 ^ 40 * 3148811 * 2
def baseEnd_3148811 : Nat := 359300785147685554706975

theorem tailTrace_3148811 : CollatzResearch.WordTrace tailWord_3148811 prefixEnd_3148811 359300785147685554706975 := by
  unfold tailWord_3148811
  simp only [CollatzResearch.WordTrace]
  refine ⟨114846572195402995949526287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76564381463601997299684191 114846572195402995949526287)
  ·
    refine ⟨172269858293104493924289431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114846572195402995949526287 172269858293104493924289431)
    ·
      refine ⟨258404787439656740886434147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172269858293104493924289431 258404787439656740886434147)
      ·
        refine ⟨387607181159485111329651221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258404787439656740886434147 387607181159485111329651221)
        ·
          refine ⟨18169086616850864593577401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 387607181159485111329651221 18169086616850864593577401)
          ·
            refine ⟨13626814962638148445183051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18169086616850864593577401 13626814962638148445183051)
            ·
              refine ⟨20440222443957222667774577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626814962638148445183051 20440222443957222667774577)
              ·
                refine ⟨15330166832967917000830933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20440222443957222667774577 15330166832967917000830933)
                ·
                  refine ⟨359300785147685554706975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15330166832967917000830933 359300785147685554706975)
                  ·
                    rfl

theorem cell22_3148811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_3148811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148811 prefixEnd_3148811 := by exact prefixLift 3148811
  have htrace : WordTrace (prefixWord ++ tailWord_3148811) baseStart_3148811 baseEnd_3148811 := by
    simpa [prefixWord, tailWord_3148811, baseEnd_3148811] using wordTrace_append hprefix tailTrace_3148811
  have hstable : (prefixWord ++ tailWord_3148811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148811).length < 2 ^ (prefixWord ++ tailWord_3148811).sum := by decide
  have hdescent : baseEnd_3148811 < baseStart_3148811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148905 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_3148905 : Nat := 118140960795 + 3148905 * 2 ^ 59
def prefixEnd_3148905 : Nat := 4983230072969 + 3 ^ 40 * 3148905 * 2
def baseEnd_3148905 : Nat := 1077934533564071752270637

theorem tailTrace_3148905 : CollatzResearch.WordTrace tailWord_3148905 prefixEnd_3148905 1077934533564071752270637 := by
  unfold tailWord_3148905
  simp only [CollatzResearch.WordTrace]
  refine ⟨114850000657062450003448169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76566667104708300002298779 114850000657062450003448169)
  ·
    refine ⟨86137500492796837502586127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114850000657062450003448169 86137500492796837502586127)
    ·
      refine ⟨129206250739195256253879191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86137500492796837502586127 129206250739195256253879191)
      ·
        refine ⟨193809376108792884380818787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129206250739195256253879191 193809376108792884380818787)
        ·
          refine ⟨290714064163189326571228181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193809376108792884380818787 290714064163189326571228181)
          ·
            refine ⟨13627221757649499683026321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290714064163189326571228181 13627221757649499683026321)
            ·
              refine ⟨10220416318237124762269741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13627221757649499683026321 10220416318237124762269741)
              ·
                refine ⟨3832656119338921785851153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10220416318237124762269741 3832656119338921785851153)
                ·
                  refine ⟨2874492089504191339388365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3832656119338921785851153 2874492089504191339388365)
                  ·
                    refine ⟨1077934533564071752270637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2874492089504191339388365 1077934533564071752270637)
                    ·
                      rfl

theorem cell22_3148905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_3148905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148905 prefixEnd_3148905 := by exact prefixLift 3148905
  have htrace : WordTrace (prefixWord ++ tailWord_3148905) baseStart_3148905 baseEnd_3148905 := by
    simpa [prefixWord, tailWord_3148905, baseEnd_3148905] using wordTrace_append hprefix tailTrace_3148905
  have hstable : (prefixWord ++ tailWord_3148905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148905).length < 2 ^ (prefixWord ++ tailWord_3148905).sum := by decide
  have hdescent : baseEnd_3148905 < baseStart_3148905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148926 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3148926 : Nat := 118140960795 + 3148926 * 2 ^ 59
def prefixEnd_3148926 : Nat := 4983230072969 + 3 ^ 40 * 3148926 * 2
def baseEnd_3148926 : Nat := 1077941722293234697495573

theorem tailTrace_3148926 : CollatzResearch.WordTrace tailWord_3148926 prefixEnd_3148926 1077941722293234697495573 := by
  unfold tailWord_3148926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14356345823748296323745329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76567177726657580393308421 14356345823748296323745329)
  ·
    refine ⟨10767259367811222242808997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14356345823748296323745329 10767259367811222242808997)
    ·
      refine ⟨2018861131464604170526687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10767259367811222242808997 2018861131464604170526687)
      ·
        refine ⟨3028291697196906255790031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018861131464604170526687 3028291697196906255790031)
        ·
          refine ⟨4542437545795359383685047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028291697196906255790031 4542437545795359383685047)
          ·
            refine ⟨6813656318693039075527571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542437545795359383685047 6813656318693039075527571)
            ·
              refine ⟨10220484478039558613291357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813656318693039075527571 10220484478039558613291357)
              ·
                refine ⟨3832681679264834479984259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10220484478039558613291357 3832681679264834479984259)
                ·
                  refine ⟨5749022518897251719976389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832681679264834479984259 5749022518897251719976389)
                  ·
                    refine ⟨1077941722293234697495573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749022518897251719976389 1077941722293234697495573)
                    ·
                      rfl

theorem cell22_3148926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3148926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148926 prefixEnd_3148926 := by exact prefixLift 3148926
  have htrace : WordTrace (prefixWord ++ tailWord_3148926) baseStart_3148926 baseEnd_3148926 := by
    simpa [prefixWord, tailWord_3148926, baseEnd_3148926] using wordTrace_append hprefix tailTrace_3148926
  have hstable : (prefixWord ++ tailWord_3148926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148926).length < 2 ^ (prefixWord ++ tailWord_3148926).sum := by decide
  have hdescent : baseEnd_3148926 < baseStart_3148926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148963 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 5]
def baseStart_3148963 : Nat := 118140960795 + 3148963 * 2 ^ 59
def prefixEnd_3148963 : Nat := 4983230072969 + 3 ^ 40 * 3148963 * 2
def baseEnd_3148963 : Nat := 359318129383126311440153

theorem tailTrace_3148963 : CollatzResearch.WordTrace tailWord_3148963 prefixEnd_3148963 359318129383126311440153 := by
  unfold tailWord_3148963
  simp only [CollatzResearch.WordTrace]
  refine ⟨114852116090852325909059543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76568077393901550606039695 114852116090852325909059543)
  ·
    refine ⟨172278174136278488863589315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114852116090852325909059543 172278174136278488863589315)
    ·
      refine ⟨258417261204417733295383973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172278174136278488863589315 258417261204417733295383973)
      ·
        refine ⟨48453236475828324992884495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258417261204417733295383973 48453236475828324992884495)
        ·
          refine ⟨72679854713742487489326743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48453236475828324992884495 72679854713742487489326743)
          ·
            refine ⟨109019782070613731233990115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72679854713742487489326743 109019782070613731233990115)
            ·
              refine ⟨163529673105920596850985173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109019782070613731233990115 163529673105920596850985173)
              ·
                refine ⟨3832726713420013988694965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 163529673105920596850985173 3832726713420013988694965)
                ·
                  refine ⟨359318129383126311440153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3832726713420013988694965 359318129383126311440153)
                  ·
                    rfl

theorem cell22_3148963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 5].length) (baseStart_3148963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148963 prefixEnd_3148963 := by exact prefixLift 3148963
  have htrace : WordTrace (prefixWord ++ tailWord_3148963) baseStart_3148963 baseEnd_3148963 := by
    simpa [prefixWord, tailWord_3148963, baseEnd_3148963] using wordTrace_append hprefix tailTrace_3148963
  have hstable : (prefixWord ++ tailWord_3148963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148963).length < 2 ^ (prefixWord ++ tailWord_3148963).sum := by decide
  have hdescent : baseEnd_3148963 < baseStart_3148963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148967 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3148967 : Nat := 118140960795 + 3148967 * 2 ^ 59
def prefixEnd_3148967 : Nat := 4983230072969 + 3 ^ 40 * 3148967 * 2
def baseEnd_3148967 : Nat := 1077955757431124257220447

theorem tailTrace_3148967 : CollatzResearch.WordTrace tailWord_3148967 prefixEnd_3148967 1077955757431124257220447 := by
  unfold tailWord_3148967
  simp only [CollatzResearch.WordTrace]
  refine ⟨114852261982837834592205155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76568174655225223061470103 114852261982837834592205155)
  ·
    refine ⟨172278392974256751888307733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114852261982837834592205155 172278392974256751888307733)
    ·
      refine ⟨8075549670668285244764425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172278392974256751888307733 8075549670668285244764425)
      ·
        refine ⟨6056662253001213933573319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8075549670668285244764425 6056662253001213933573319)
        ·
          refine ⟨9084993379501820900359979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056662253001213933573319 9084993379501820900359979)
          ·
            refine ⟨13627490069252731350539969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084993379501820900359979 13627490069252731350539969)
            ·
              refine ⟨10220617551939548512904977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13627490069252731350539969 10220617551939548512904977)
              ·
                refine ⟨7665463163954661384678733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10220617551939548512904977 7665463163954661384678733)
                ·
                  refine ⟨2874548686482998019254525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7665463163954661384678733 2874548686482998019254525)
                  ·
                    refine ⟨1077955757431124257220447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2874548686482998019254525 1077955757431124257220447)
                    ·
                      rfl

theorem cell22_3148967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3148967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3148967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3148967 prefixEnd_3148967 := by exact prefixLift 3148967
  have htrace : WordTrace (prefixWord ++ tailWord_3148967) baseStart_3148967 baseEnd_3148967 := by
    simpa [prefixWord, tailWord_3148967, baseEnd_3148967] using wordTrace_append hprefix tailTrace_3148967
  have hstable : (prefixWord ++ tailWord_3148967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148967).length < 2 ^ (prefixWord ++ tailWord_3148967).sum := by decide
  have hdescent : baseEnd_3148967 < baseStart_3148967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149010 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3149010 : Nat := 118140960795 + 3149010 * 2 ^ 59
def prefixEnd_3149010 : Nat := 4983230072969 + 3 ^ 40 * 3149010 * 2
def baseEnd_3149010 : Nat := 1077970477209886478395315

theorem tailTrace_3149010 : CollatzResearch.WordTrace tailWord_3149010 prefixEnd_3149010 1077970477209886478395315 := by
  unfold tailWord_3149010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28713457580420513234005121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76569220214454701957346989 28713457580420513234005121)
  ·
    refine ⟨21535093185315384925503841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28713457580420513234005121 21535093185315384925503841)
    ·
      refine ⟨16151319888986538694127881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21535093185315384925503841 16151319888986538694127881)
      ·
        refine ⟨12113489916739904020595911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16151319888986538694127881 12113489916739904020595911)
        ·
          refine ⟨18170234875109856030893867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12113489916739904020595911 18170234875109856030893867)
          ·
            refine ⟨27255352312664784046340801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18170234875109856030893867 27255352312664784046340801)
            ·
              refine ⟨20441514234498588034755601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27255352312664784046340801 20441514234498588034755601)
              ·
                refine ⟨15331135675873941026066701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20441514234498588034755601 15331135675873941026066701)
                ·
                  refine ⟨5749175878452727884775013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15331135675873941026066701 5749175878452727884775013)
                  ·
                    refine ⟨1077970477209886478395315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749175878452727884775013 1077970477209886478395315)
                    ·
                      rfl

theorem cell22_3149010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3149010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149010 prefixEnd_3149010 := by exact prefixLift 3149010
  have htrace : WordTrace (prefixWord ++ tailWord_3149010) baseStart_3149010 baseEnd_3149010 := by
    simpa [prefixWord, tailWord_3149010, baseEnd_3149010] using wordTrace_append hprefix tailTrace_3149010
  have hstable : (prefixWord ++ tailWord_3149010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149010).length < 2 ^ (prefixWord ++ tailWord_3149010).sum := by decide
  have hdescent : baseEnd_3149010 < baseStart_3149010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149014 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3149014 : Nat := 118140960795 + 3149014 * 2 ^ 59
def prefixEnd_3149014 : Nat := 4983230072969 + 3 ^ 40 * 3149014 * 2
def baseEnd_3149014 : Nat := 359323948830543933765101

theorem tailTrace_3149014 : CollatzResearch.WordTrace tailWord_3149014 prefixEnd_3149014 359323948830543933765101 := by
  unfold tailWord_3149014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178373513354222601197881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76569317475778374412777397 7178373513354222601197881)
  ·
    refine ⟨5383780135015666950898411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7178373513354222601197881 5383780135015666950898411)
    ·
      refine ⟨8075670202523500426347617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5383780135015666950898411 8075670202523500426347617)
      ·
        refine ⟨6056752651892625319760713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8075670202523500426347617 6056752651892625319760713)
        ·
          refine ⟨4542564488919468989820535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6056752651892625319760713 4542564488919468989820535)
          ·
            refine ⟨6813846733379203484730803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542564488919468989820535 6813846733379203484730803)
            ·
              refine ⟨10220770100068805227096205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813846733379203484730803 10220770100068805227096205)
              ·
                refine ⟨3832788787525801960161077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10220770100068805227096205 3832788787525801960161077)
                ·
                  refine ⟨359323948830543933765101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3832788787525801960161077 359323948830543933765101)
                  ·
                    rfl

theorem cell22_3149014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3149014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149014 prefixEnd_3149014 := by exact prefixLift 3149014
  have htrace : WordTrace (prefixWord ++ tailWord_3149014) baseStart_3149014 baseEnd_3149014 := by
    simpa [prefixWord, tailWord_3149014, baseEnd_3149014] using wordTrace_append hprefix tailTrace_3149014
  have hstable : (prefixWord ++ tailWord_3149014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149014).length < 2 ^ (prefixWord ++ tailWord_3149014).sum := by decide
  have hdescent : baseEnd_3149014 < baseStart_3149014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149055 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 2, 4]
def baseStart_3149055 : Nat := 118140960795 + 3149055 * 2 ^ 59
def prefixEnd_3149055 : Nat := 4983230072969 + 3 ^ 40 * 3149055 * 2
def baseEnd_3149055 : Nat := 1077985881629521361020177

theorem tailTrace_3149055 : CollatzResearch.WordTrace tailWord_3149055 prefixEnd_3149055 1077985881629521361020177 := by
  unfold tailWord_3149055
  simp only [CollatzResearch.WordTrace]
  refine ⟨114855471606519025621408619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76570314404346017080939079 114855471606519025621408619)
  ·
    refine ⟨172283207409778538432112929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114855471606519025621408619 172283207409778538432112929)
    ·
      refine ⟨129212405557333903824084697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172283207409778538432112929 129212405557333903824084697)
      ·
        refine ⟨96909304168000427868063523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129212405557333903824084697 96909304168000427868063523)
        ·
          refine ⟨145363956252000641802095285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96909304168000427868063523 145363956252000641802095285)
          ·
            refine ⟨13627870898625060168946433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145363956252000641802095285 13627870898625060168946433)
            ·
              refine ⟨10220903173968795126709825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13627870898625060168946433 10220903173968795126709825)
              ·
                refine ⟨7665677380476596345032369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10220903173968795126709825 7665677380476596345032369)
                ·
                  refine ⟨5749258035357447258774277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7665677380476596345032369 5749258035357447258774277)
                  ·
                    refine ⟨1077985881629521361020177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749258035357447258774277 1077985881629521361020177)
                    ·
                      rfl

theorem cell22_3149055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_3149055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149055 prefixEnd_3149055 := by exact prefixLift 3149055
  have htrace : WordTrace (prefixWord ++ tailWord_3149055) baseStart_3149055 baseEnd_3149055 := by
    simpa [prefixWord, tailWord_3149055, baseEnd_3149055] using wordTrace_append hprefix tailTrace_3149055
  have hstable : (prefixWord ++ tailWord_3149055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149055).length < 2 ^ (prefixWord ++ tailWord_3149055).sum := by decide
  have hdescent : baseEnd_3149055 < baseStart_3149055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149057 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3149057 : Nat := 118140960795 + 3149057 * 2 ^ 59
def prefixEnd_3149057 : Nat := 4983230072969 + 3 ^ 40 * 3149057 * 2
def baseEnd_3149057 : Nat := 1077986566270394022470171

theorem tailTrace_3149057 : CollatzResearch.WordTrace tailWord_3149057 prefixEnd_3149057 1077986566270394022470171 := by
  unfold tailWord_3149057
  simp only [CollatzResearch.WordTrace]
  refine ⟨114855544552511779962981425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76570363035007853308654283 114855544552511779962981425)
  ·
    refine ⟨86141658414383834972236069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114855544552511779962981425 86141658414383834972236069)
    ·
      refine ⟨16151560952696969057294263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86141658414383834972236069 16151560952696969057294263)
      ·
        refine ⟨24227341429045453585941395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16151560952696969057294263 24227341429045453585941395)
        ·
          refine ⟨36341012143568180378912093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227341429045453585941395 36341012143568180378912093)
          ·
            refine ⟨13627879553838067642092035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36341012143568180378912093 13627879553838067642092035)
            ·
              refine ⟨20441819330757101463138053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13627879553838067642092035 20441819330757101463138053)
              ·
                refine ⟨3832841124516956524338385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20441819330757101463138053 3832841124516956524338385)
                ·
                  refine ⟨2874630843387717393253789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3832841124516956524338385 2874630843387717393253789)
                  ·
                    refine ⟨1077986566270394022470171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2874630843387717393253789 1077986566270394022470171)
                    ·
                      rfl

theorem cell22_3149057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3149057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149057 prefixEnd_3149057 := by exact prefixLift 3149057
  have htrace : WordTrace (prefixWord ++ tailWord_3149057) baseStart_3149057 baseEnd_3149057 := by
    simpa [prefixWord, tailWord_3149057, baseEnd_3149057] using wordTrace_append hprefix tailTrace_3149057
  have hstable : (prefixWord ++ tailWord_3149057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149057).length < 2 ^ (prefixWord ++ tailWord_3149057).sum := by decide
  have hdescent : baseEnd_3149057 < baseStart_3149057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149059 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 4]
def baseStart_3149059 : Nat := 118140960795 + 3149059 * 2 ^ 59
def prefixEnd_3149059 : Nat := 4983230072969 + 3 ^ 40 * 3149059 * 2
def baseEnd_3149059 : Nat := 359329083637088894640055

theorem tailTrace_3149059 : CollatzResearch.WordTrace tailWord_3149059 prefixEnd_3149059 359329083637088894640055 := by
  unfold tailWord_3149059
  simp only [CollatzResearch.WordTrace]
  refine ⟨114855617498504534304554231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76570411665669689536369487 114855617498504534304554231)
  ·
    refine ⟨172283426247756801456831347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114855617498504534304554231 172283426247756801456831347)
    ·
      refine ⟨258425139371635202185247021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172283426247756801456831347 258425139371635202185247021)
      ·
        refine ⟨96909427264363200819467633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258425139371635202185247021 96909427264363200819467633)
        ·
          refine ⟨72682070448272400614600725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96909427264363200819467633 72682070448272400614600725)
          ·
            refine ⟨3406972052262768778809409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72682070448272400614600725 3406972052262768778809409)
            ·
              refine ⟨2555229039197076584107057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3406972052262768778809409 2555229039197076584107057)
              ·
                refine ⟨1916421779397807438080293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555229039197076584107057 1916421779397807438080293)
                ·
                  refine ⟨359329083637088894640055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916421779397807438080293 359329083637088894640055)
                  ·
                    rfl

theorem cell22_3149059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 4].length) (baseStart_3149059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149059 prefixEnd_3149059 := by exact prefixLift 3149059
  have htrace : WordTrace (prefixWord ++ tailWord_3149059) baseStart_3149059 baseEnd_3149059 := by
    simpa [prefixWord, tailWord_3149059, baseEnd_3149059] using wordTrace_append hprefix tailTrace_3149059
  have hstable : (prefixWord ++ tailWord_3149059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149059).length < 2 ^ (prefixWord ++ tailWord_3149059).sum := by decide
  have hdescent : baseEnd_3149059 < baseStart_3149059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149070 : List Nat := [4, 1, 1, 2, 1, 3, 3, 7]
def baseStart_3149070 : Nat := 118140960795 + 3149070 * 2 ^ 59
def prefixEnd_3149070 : Nat := 4983230072969 + 3 ^ 40 * 3149070 * 2
def baseEnd_3149070 : Nat := 119776779604007369099459

theorem tailTrace_3149070 : CollatzResearch.WordTrace tailWord_3149070 prefixEnd_3149070 119776779604007369099459 := by
  unfold tailWord_3149070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357002337683085397900583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76570679134309788788803109 14357002337683085397900583)
  ·
    refine ⟨21535503506524628096850875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14357002337683085397900583 21535503506524628096850875)
    ·
      refine ⟨32303255259786942145276313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21535503506524628096850875 32303255259786942145276313)
      ·
        refine ⟨24227441444840206608957235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32303255259786942145276313 24227441444840206608957235)
        ·
          refine ⟨36341162167260309913435853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227441444840206608957235 36341162167260309913435853)
          ·
            refine ⟨13627935812722616217538445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36341162167260309913435853 13627935812722616217538445)
            ·
              refine ⟨5110475929770981081576917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13627935812722616217538445 5110475929770981081576917)
              ·
                refine ⟨119776779604007369099459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5110475929770981081576917 119776779604007369099459)
                ·
                  rfl

theorem cell22_3149070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_3149070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149070 prefixEnd_3149070 := by exact prefixLift 3149070
  have htrace : WordTrace (prefixWord ++ tailWord_3149070) baseStart_3149070 baseEnd_3149070 := by
    simpa [prefixWord, tailWord_3149070, baseEnd_3149070] using wordTrace_append hprefix tailTrace_3149070
  have hstable : (prefixWord ++ tailWord_3149070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149070).length < 2 ^ (prefixWord ++ tailWord_3149070).sum := by decide
  have hdescent : baseEnd_3149070 < baseStart_3149070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149083 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_3149083 : Nat := 118140960795 + 3149083 * 2 ^ 59
def prefixEnd_3149083 : Nat := 4983230072969 + 3 ^ 40 * 3149083 * 2
def baseEnd_3149083 : Nat := 1077995466601738621320091

theorem tailTrace_3149083 : CollatzResearch.WordTrace tailWord_3149083 prefixEnd_3149083 1077995466601738621320091 := by
  unfold tailWord_3149083
  simp only [CollatzResearch.WordTrace]
  refine ⟨114856492850417586403427903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76570995233611724268951935 114856492850417586403427903)
  ·
    refine ⟨172284739275626379605141855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114856492850417586403427903 172284739275626379605141855)
    ·
      refine ⟨258427108913439569407712783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172284739275626379605141855 258427108913439569407712783)
      ·
        refine ⟨387640663370159354111569175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258427108913439569407712783 387640663370159354111569175)
        ·
          refine ⟨581460995055239031167353763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387640663370159354111569175 581460995055239031167353763)
          ·
            refine ⟨872191492582858546751030645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581460995055239031167353763 872191492582858546751030645)
            ·
              refine ⟨81767952429642988757909123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 872191492582858546751030645 81767952429642988757909123)
              ·
                refine ⟨122651928644464483136863685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81767952429642988757909123 122651928644464483136863685)
                ·
                  refine ⟨22997236620837090588161941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122651928644464483136863685 22997236620837090588161941)
                  ·
                    refine ⟨1077995466601738621320091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22997236620837090588161941 1077995466601738621320091)
                    ·
                      rfl

theorem cell22_3149083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_3149083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149083 prefixEnd_3149083 := by exact prefixLift 3149083
  have htrace : WordTrace (prefixWord ++ tailWord_3149083) baseStart_3149083 baseEnd_3149083 := by
    simpa [prefixWord, tailWord_3149083, baseEnd_3149083] using wordTrace_append hprefix tailTrace_3149083
  have hstable : (prefixWord ++ tailWord_3149083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149083).length < 2 ^ (prefixWord ++ tailWord_3149083).sum := by decide
  have hdescent : baseEnd_3149083 < baseStart_3149083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149087 : List Nat := [1, 1, 2, 4, 4, 1, 3, 6]
def baseStart_3149087 : Nat := 118140960795 + 3149087 * 2 ^ 59
def prefixEnd_3149087 : Nat := 4983230072969 + 3 ^ 40 * 3149087 * 2
def baseEnd_3149087 : Nat := 119777426209275993802231

theorem tailTrace_3149087 : CollatzResearch.WordTrace tailWord_3149087 prefixEnd_3149087 119777426209275993802231 := by
  unfold tailWord_3149087
  simp only [CollatzResearch.WordTrace]
  refine ⟨114856638742403095086573515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76571092494935396724382343 114856638742403095086573515)
  ·
    refine ⟨172284958113604642629860273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114856638742403095086573515 172284958113604642629860273)
    ·
      refine ⟨129213718585203481972395205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172284958113604642629860273 129213718585203481972395205)
      ·
        refine ⟨24227572234725652869824101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129213718585203481972395205 24227572234725652869824101)
        ·
          refine ⟨4542669794011059913092019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24227572234725652869824101 4542669794011059913092019)
          ·
            refine ⟨6814004691016589869638029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542669794011059913092019 6814004691016589869638029)
            ·
              refine ⟨2555251759131221201114261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6814004691016589869638029 2555251759131221201114261)
              ·
                refine ⟨119777426209275993802231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2555251759131221201114261 119777426209275993802231)
                ·
                  rfl

theorem cell22_3149087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 6].length) (baseStart_3149087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149087 prefixEnd_3149087 := by exact prefixLift 3149087
  have htrace : WordTrace (prefixWord ++ tailWord_3149087) baseStart_3149087 baseEnd_3149087 := by
    simpa [prefixWord, tailWord_3149087, baseEnd_3149087] using wordTrace_append hprefix tailTrace_3149087
  have hstable : (prefixWord ++ tailWord_3149087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149087).length < 2 ^ (prefixWord ++ tailWord_3149087).sum := by decide
  have hdescent : baseEnd_3149087 < baseStart_3149087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149119 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 1, 3]
def baseStart_3149119 : Nat := 118140960795 + 3149119 * 2 ^ 59
def prefixEnd_3149119 : Nat := 4983230072969 + 3 ^ 40 * 3149119 * 2
def baseEnd_3149119 : Nat := 1078007790137446527419981

theorem tailTrace_3149119 : CollatzResearch.WordTrace tailWord_3149119 prefixEnd_3149119 1078007790137446527419981 := by
  unfold tailWord_3149119
  simp only [CollatzResearch.WordTrace]
  refine ⟨114857805878287164551738411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76571870585524776367825607 114857805878287164551738411)
  ·
    refine ⟨172286708817430746827607617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114857805878287164551738411 172286708817430746827607617)
    ·
      refine ⟨129215031613073060120705713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172286708817430746827607617 129215031613073060120705713)
      ·
        refine ⟨96911273709804795090529285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129215031613073060120705713 96911273709804795090529285)
        ·
          refine ⟨18170863820588399079474241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96911273709804795090529285 18170863820588399079474241)
          ·
            refine ⟨13628147865441299309605681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18170863820588399079474241 13628147865441299309605681)
            ·
              refine ⟨10221110899080974482204261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13628147865441299309605681 10221110899080974482204261)
              ·
                refine ⟨1916458293577682715413299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10221110899080974482204261 1916458293577682715413299)
                ·
                  refine ⟨2874687440366524073119949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916458293577682715413299 2874687440366524073119949)
                  ·
                    refine ⟨1078007790137446527419981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2874687440366524073119949 1078007790137446527419981)
                    ·
                      rfl

theorem cell22_3149119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_3149119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149119 prefixEnd_3149119 := by exact prefixLift 3149119
  have htrace : WordTrace (prefixWord ++ tailWord_3149119) baseStart_3149119 baseEnd_3149119 := by
    simpa [prefixWord, tailWord_3149119, baseEnd_3149119] using wordTrace_append hprefix tailTrace_3149119
  have hstable : (prefixWord ++ tailWord_3149119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149119).length < 2 ^ (prefixWord ++ tailWord_3149119).sum := by decide
  have hdescent : baseEnd_3149119 < baseStart_3149119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149145 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_3149145 : Nat := 118140960795 + 3149145 * 2 ^ 59
def prefixEnd_3149145 : Nat := 4983230072969 + 3 ^ 40 * 3149145 * 2
def baseEnd_3149145 : Nat := 1078016690468791126269901

theorem tailTrace_3149145 : CollatzResearch.WordTrace tailWord_3149145 prefixEnd_3149145 1078016690468791126269901 := by
  unfold tailWord_3149145
  simp only [CollatzResearch.WordTrace]
  refine ⟨114858754176192970992184889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76572502784128647328123259 114858754176192970992184889)
  ·
    refine ⟨86144065632144728244138667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114858754176192970992184889 86144065632144728244138667)
    ·
      refine ⟨129216098448217092366208001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86144065632144728244138667 129216098448217092366208001)
      ·
        refine ⟨96912073836162819274656001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129216098448217092366208001 96912073836162819274656001)
        ·
          refine ⟨72684055377122114455992001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96912073836162819274656001 72684055377122114455992001)
          ·
            refine ⟨54513041532841585841994001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72684055377122114455992001 54513041532841585841994001)
            ·
              refine ⟨40884781149631189381495501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54513041532841585841994001 40884781149631189381495501)
              ·
                refine ⟨15331792931111696018060813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40884781149631189381495501 15331792931111696018060813)
                ·
                  refine ⟨5749422349166886006772805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15331792931111696018060813 5749422349166886006772805)
                  ·
                    refine ⟨1078016690468791126269901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749422349166886006772805 1078016690468791126269901)
                    ·
                      rfl

theorem cell22_3149145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_3149145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149145 prefixEnd_3149145 := by exact prefixLift 3149145
  have htrace : WordTrace (prefixWord ++ tailWord_3149145) baseStart_3149145 baseEnd_3149145 := by
    simpa [prefixWord, tailWord_3149145, baseEnd_3149145] using wordTrace_append hprefix tailTrace_3149145
  have hstable : (prefixWord ++ tailWord_3149145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149145).length < 2 ^ (prefixWord ++ tailWord_3149145).sum := by decide
  have hdescent : baseEnd_3149145 < baseStart_3149145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149177 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 4]
def baseStart_3149177 : Nat := 118140960795 + 3149177 * 2 ^ 59
def prefixEnd_3149177 : Nat := 4983230072969 + 3 ^ 40 * 3149177 * 2
def baseEnd_3149177 : Nat := 359342548240917903156601

theorem tailTrace_3149177 : CollatzResearch.WordTrace tailWord_3149177 prefixEnd_3149177 359342548240917903156601 := by
  unfold tailWord_3149177
  simp only [CollatzResearch.WordTrace]
  refine ⟨114859921312077040457349785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76573280874718026971566523 114859921312077040457349785)
  ·
    refine ⟨86144940984057780343012339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114859921312077040457349785 86144940984057780343012339)
    ·
      refine ⟨129217411476086670514518509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86144940984057780343012339 129217411476086670514518509)
      ·
        refine ⟨48456529303532501442944441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129217411476086670514518509 48456529303532501442944441)
        ·
          refine ⟨36342396977649376082208331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48456529303532501442944441 36342396977649376082208331)
          ·
            refine ⟨54513595466474064123312497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36342396977649376082208331 54513595466474064123312497)
            ·
              refine ⟨40885196599855548092484373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54513595466474064123312497 40885196599855548092484373)
              ·
                refine ⟨1916493590618228816835205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40885196599855548092484373 1916493590618228816835205)
                ·
                  refine ⟨359342548240917903156601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916493590618228816835205 359342548240917903156601)
                  ·
                    rfl

theorem cell22_3149177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_3149177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149177 prefixEnd_3149177 := by exact prefixLift 3149177
  have htrace : WordTrace (prefixWord ++ tailWord_3149177) baseStart_3149177 baseEnd_3149177 := by
    simpa [prefixWord, tailWord_3149177, baseEnd_3149177] using wordTrace_append hprefix tailTrace_3149177
  have hstable : (prefixWord ++ tailWord_3149177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149177).length < 2 ^ (prefixWord ++ tailWord_3149177).sum := by decide
  have hdescent : baseEnd_3149177 < baseStart_3149177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149205 : List Nat := [1, 3, 2, 1, 1, 2, 4, 8]
def baseStart_3149205 : Nat := 118140960795 + 3149205 * 2 ^ 59
def prefixEnd_3149205 : Nat := 4983230072969 + 3 ^ 40 * 3149205 * 2
def baseEnd_3149205 : Nat := 119781914410552329974413

theorem tailTrace_3149205 : CollatzResearch.WordTrace tailWord_3149205 prefixEnd_3149205 119781914410552329974413 := by
  unfold tailWord_3149205
  simp only [CollatzResearch.WordTrace]
  refine ⟨114860942555975601239369069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76573961703983734159579379 114860942555975601239369069)
  ·
    refine ⟨43072853458490850464763401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114860942555975601239369069 43072853458490850464763401)
    ·
      refine ⟨32304640093868137848572551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43072853458490850464763401 32304640093868137848572551)
      ·
        refine ⟨48456960140802206772858827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32304640093868137848572551 48456960140802206772858827)
        ·
          refine ⟨72685440211203310159288241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48456960140802206772858827 72685440211203310159288241)
          ·
            refine ⟨54514080158402482619466181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72685440211203310159288241 54514080158402482619466181)
            ·
              refine ⟨10221390029700465491149909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54514080158402482619466181 10221390029700465491149909)
              ·
                refine ⟨119781914410552329974413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10221390029700465491149909 119781914410552329974413)
                ·
                  rfl

theorem cell22_3149205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 8].length) (baseStart_3149205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149205 prefixEnd_3149205 := by exact prefixLift 3149205
  have htrace : WordTrace (prefixWord ++ tailWord_3149205) baseStart_3149205 baseEnd_3149205 := by
    simpa [prefixWord, tailWord_3149205, baseEnd_3149205] using wordTrace_append hprefix tailTrace_3149205
  have hstable : (prefixWord ++ tailWord_3149205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149205).length < 2 ^ (prefixWord ++ tailWord_3149205).sum := by decide
  have hdescent : baseEnd_3149205 < baseStart_3149205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149402 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_3149402 : Nat := 118140960795 + 3149402 * 2 ^ 59
def prefixEnd_3149402 : Nat := 4983230072969 + 3 ^ 40 * 3149402 * 2
def baseEnd_3149402 : Nat := 359368222273642707531371

theorem tailTrace_3149402 : CollatzResearch.WordTrace tailWord_3149402 prefixEnd_3149402 359368222273642707531371 := by
  unfold tailWord_3149402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28717031934065475971072615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76578751824174602589526973 28717031934065475971072615)
  ·
    refine ⟨43075547901098213956608923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28717031934065475971072615 43075547901098213956608923)
    ·
      refine ⟨64613321851647320934913385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43075547901098213956608923 64613321851647320934913385)
      ·
        refine ⟨48459991388735490701185039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64613321851647320934913385 48459991388735490701185039)
        ·
          refine ⟨72689987083103236051777559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48459991388735490701185039 72689987083103236051777559)
          ·
            refine ⟨109034980624654854077666339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72689987083103236051777559 109034980624654854077666339)
            ·
              refine ⟨163552470936982281116499509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109034980624654854077666339 163552470936982281116499509)
              ·
                refine ⟨15333044150342088854671829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163552470936982281116499509 15333044150342088854671829)
                ·
                  refine ⟨359368222273642707531371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15333044150342088854671829 359368222273642707531371)
                  ·
                    rfl

theorem cell22_3149402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_3149402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149402 prefixEnd_3149402 := by exact prefixLift 3149402
  have htrace : WordTrace (prefixWord ++ tailWord_3149402) baseStart_3149402 baseEnd_3149402 := by
    simpa [prefixWord, tailWord_3149402, baseEnd_3149402] using wordTrace_append hprefix tailTrace_3149402
  have hstable : (prefixWord ++ tailWord_3149402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149402).length < 2 ^ (prefixWord ++ tailWord_3149402).sum := by decide
  have hdescent : baseEnd_3149402 < baseStart_3149402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149404 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3149404 : Nat := 118140960795 + 3149404 * 2 ^ 59
def prefixEnd_3149404 : Nat := 4983230072969 + 3 ^ 40 * 3149404 * 2
def baseEnd_3149404 : Nat := 1078105351461800784044107

theorem tailTrace_3149404 : CollatzResearch.WordTrace tailWord_3149404 prefixEnd_3149404 1078105351461800784044107 := by
  unfold tailWord_3149404
  simp only [CollatzResearch.WordTrace]
  refine ⟨57434100341127329112931633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76578800454836438817242177 57434100341127329112931633)
  ·
    refine ⟨43075575255845496834698725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57434100341127329112931633 43075575255845496834698725)
    ·
      refine ⟨8076670360471030656506011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43075575255845496834698725 8076670360471030656506011)
      ·
        refine ⟨12115005540706545984759017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8076670360471030656506011 12115005540706545984759017)
        ·
          refine ⟨9086254155529909488569263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12115005540706545984759017 9086254155529909488569263)
          ·
            refine ⟨13629381233294864232853895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9086254155529909488569263 13629381233294864232853895)
            ·
              refine ⟨20444071849942296349280843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13629381233294864232853895 20444071849942296349280843)
              ·
                refine ⟨30666107774913444523921265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20444071849942296349280843 30666107774913444523921265)
                ·
                  refine ⟨22999580831185083392940949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30666107774913444523921265 22999580831185083392940949)
                  ·
                    refine ⟨1078105351461800784044107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22999580831185083392940949 1078105351461800784044107)
                    ·
                      rfl

theorem cell22_3149404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3149404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149404 prefixEnd_3149404 := by exact prefixLift 3149404
  have htrace : WordTrace (prefixWord ++ tailWord_3149404) baseStart_3149404 baseEnd_3149404 := by
    simpa [prefixWord, tailWord_3149404, baseEnd_3149404] using wordTrace_append hprefix tailTrace_3149404
  have hstable : (prefixWord ++ tailWord_3149404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149404).length < 2 ^ (prefixWord ++ tailWord_3149404).sum := by decide
  have hdescent : baseEnd_3149404 < baseStart_3149404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149417 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_3149417 : Nat := 118140960795 + 3149417 * 2 ^ 59
def prefixEnd_3149417 : Nat := 4983230072969 + 3 ^ 40 * 3149417 * 2
def baseEnd_3149417 : Nat := 1078109801627473083469067

theorem tailTrace_3149417 : CollatzResearch.WordTrace tailWord_3149417 prefixEnd_3149417 1078109801627473083469067 := by
  unfold tailWord_3149417
  simp only [CollatzResearch.WordTrace]
  refine ⟨114868674831207561446086505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76579116554138374297391003 114868674831207561446086505)
  ·
    refine ⟨86151506123405671084564879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114868674831207561446086505 86151506123405671084564879)
    ·
      refine ⟨129227259185108506626847319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86151506123405671084564879 129227259185108506626847319)
      ·
        refine ⟨193840888777662759940270979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129227259185108506626847319 193840888777662759940270979)
        ·
          refine ⟨290761333166494139910406469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193840888777662759940270979 290761333166494139910406469)
          ·
            refine ⟨54517749968717651233201213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290761333166494139910406469 54517749968717651233201213)
            ·
              refine ⟨20444156238269119212450455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54517749968717651233201213 20444156238269119212450455)
              ·
                refine ⟨30666234357403678818675683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20444156238269119212450455 30666234357403678818675683)
                ·
                  refine ⟨45999351536105518228013525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30666234357403678818675683 45999351536105518228013525)
                  ·
                    refine ⟨1078109801627473083469067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45999351536105518228013525 1078109801627473083469067)
                    ·
                      rfl

theorem cell22_3149417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_3149417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149417 prefixEnd_3149417 := by exact prefixLift 3149417
  have htrace : WordTrace (prefixWord ++ tailWord_3149417) baseStart_3149417 baseEnd_3149417 := by
    simpa [prefixWord, tailWord_3149417, baseEnd_3149417] using wordTrace_append hprefix tailTrace_3149417
  have hstable : (prefixWord ++ tailWord_3149417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149417).length < 2 ^ (prefixWord ++ tailWord_3149417).sum := by decide
  have hdescent : baseEnd_3149417 < baseStart_3149417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149464 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_3149464 : Nat := 118140960795 + 3149464 * 2 ^ 59
def prefixEnd_3149464 : Nat := 4983230072969 + 3 ^ 40 * 3149464 * 2
def baseEnd_3149464 : Nat := 359375296895993542514641

theorem tailTrace_3149464 : CollatzResearch.WordTrace tailWord_3149464 prefixEnd_3149464 359375296895993542514641 := by
  unfold tailWord_3149464
  simp only [CollatzResearch.WordTrace]
  refine ⟨57435194531018644236523723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76580259374691525648698297 57435194531018644236523723)
  ·
    refine ⟨86152791796527966354785585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57435194531018644236523723 86152791796527966354785585)
    ·
      refine ⟨64614593847395974766089189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86152791796527966354785585 64614593847395974766089189)
      ·
        refine ⟨12115236346386745268641723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64614593847395974766089189 12115236346386745268641723)
        ·
          refine ⟨18172854519580117902962585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12115236346386745268641723 18172854519580117902962585)
          ·
            refine ⟨13629640889685088427221939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18172854519580117902962585 13629640889685088427221939)
            ·
              refine ⟨20444461334527632640832909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13629640889685088427221939 20444461334527632640832909)
              ·
                refine ⟨7666673000447862240312341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20444461334527632640832909 7666673000447862240312341)
                ·
                  refine ⟨359375296895993542514641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7666673000447862240312341 359375296895993542514641)
                  ·
                    rfl

theorem cell22_3149464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_3149464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149464 prefixEnd_3149464 := by exact prefixLift 3149464
  have htrace : WordTrace (prefixWord ++ tailWord_3149464) baseStart_3149464 baseEnd_3149464 := by
    simpa [prefixWord, tailWord_3149464, baseEnd_3149464] using wordTrace_append hprefix tailTrace_3149464
  have hstable : (prefixWord ++ tailWord_3149464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149464).length < 2 ^ (prefixWord ++ tailWord_3149464).sum := by decide
  have hdescent : baseEnd_3149464 < baseStart_3149464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149498 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_3149498 : Nat := 118140960795 + 3149498 * 2 ^ 59
def prefixEnd_3149498 : Nat := 4983230072969 + 3 ^ 40 * 3149498 * 2
def baseEnd_3149498 : Nat := 359379176527605290731273

theorem tailTrace_3149498 : CollatzResearch.WordTrace tailWord_3149498 prefixEnd_3149498 359379176527605290731273 := by
  unfold tailWord_3149498
  simp only [CollatzResearch.WordTrace]
  refine ⟨28717907285978528069946287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76581086095942741519856765 28717907285978528069946287)
  ·
    refine ⟨43076860928967792104919431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28717907285978528069946287 43076860928967792104919431)
    ·
      refine ⟨64615291393451688157379147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43076860928967792104919431 64615291393451688157379147)
      ·
        refine ⟨96922937090177532236068721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64615291393451688157379147 96922937090177532236068721)
        ·
          refine ⟨72692202817633149177051541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96922937090177532236068721 72692202817633149177051541)
          ·
            refine ⟨3407447007076553867674291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72692202817633149177051541 3407447007076553867674291)
            ·
              refine ⟨5111170510614830801511437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407447007076553867674291 5111170510614830801511437)
              ·
                refine ⟨1916688941480561550566789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5111170510614830801511437 1916688941480561550566789)
                ·
                  refine ⟨359379176527605290731273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916688941480561550566789 359379176527605290731273)
                  ·
                    rfl

theorem cell22_3149498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_3149498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149498 prefixEnd_3149498 := by exact prefixLift 3149498
  have htrace : WordTrace (prefixWord ++ tailWord_3149498) baseStart_3149498 baseEnd_3149498 := by
    simpa [prefixWord, tailWord_3149498, baseEnd_3149498] using wordTrace_append hprefix tailTrace_3149498
  have hstable : (prefixWord ++ tailWord_3149498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149498).length < 2 ^ (prefixWord ++ tailWord_3149498).sum := by decide
  have hdescent : baseEnd_3149498 < baseStart_3149498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149530 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_3149530 : Nat := 118140960795 + 3149530 * 2 ^ 59
def prefixEnd_3149530 : Nat := 4983230072969 + 3 ^ 40 * 3149530 * 2
def baseEnd_3149530 : Nat := 1078148483836778455393721

theorem tailTrace_3149530 : CollatzResearch.WordTrace tailWord_3149530 prefixEnd_3149530 1078148483836778455393721 := by
  unfold tailWord_3149530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28718199069949545436237511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76581864186532121163300029 28718199069949545436237511)
  ·
    refine ⟨43077298604924318154356267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28718199069949545436237511 43077298604924318154356267)
    ·
      refine ⟨64615947907386477231534401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43077298604924318154356267 64615947907386477231534401)
      ·
        refine ⟨48461960930539857923650801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64615947907386477231534401 48461960930539857923650801)
        ·
          refine ⟨36346470697904893442738101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48461960930539857923650801 36346470697904893442738101)
          ·
            refine ⟨3407481627928583760256697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36346470697904893442738101 3407481627928583760256697)
            ·
              refine ⟨2555611220946437820192523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407481627928583760256697 2555611220946437820192523)
              ·
                refine ⟨3833416831419656730288785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555611220946437820192523 3833416831419656730288785)
                ·
                  refine ⟨2875062623564742547716589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833416831419656730288785 2875062623564742547716589)
                  ·
                    refine ⟨1078148483836778455393721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875062623564742547716589 1078148483836778455393721)
                    ·
                      rfl

theorem cell22_3149530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_3149530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149530 prefixEnd_3149530 := by exact prefixLift 3149530
  have htrace : WordTrace (prefixWord ++ tailWord_3149530) baseStart_3149530 baseEnd_3149530 := by
    simpa [prefixWord, tailWord_3149530, baseEnd_3149530] using wordTrace_append hprefix tailTrace_3149530
  have hstable : (prefixWord ++ tailWord_3149530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149530).length < 2 ^ (prefixWord ++ tailWord_3149530).sum := by decide
  have hdescent : baseEnd_3149530 < baseStart_3149530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149541 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_3149541 : Nat := 118140960795 + 3149541 * 2 ^ 59
def prefixEnd_3149541 : Nat := 4983230072969 + 3 ^ 40 * 3149541 * 2
def baseEnd_3149541 : Nat := 1078152249361578093368687

theorem tailTrace_3149541 : CollatzResearch.WordTrace tailWord_3149541 prefixEnd_3149541 1078152249361578093368687 := by
  unfold tailWord_3149541
  simp only [CollatzResearch.WordTrace]
  refine ⟨114873197482758330623600477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76582131655172220415733651 114873197482758330623600477)
  ·
    refine ⟨43077449056034373983850179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114873197482758330623600477 43077449056034373983850179)
    ·
      refine ⟨64616173584051560975775269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43077449056034373983850179 64616173584051560975775269)
      ·
        refine ⟨12115532547009667682957863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64616173584051560975775269 12115532547009667682957863)
        ·
          refine ⟨18173298820514501524436795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12115532547009667682957863 18173298820514501524436795)
          ·
            refine ⟨27259948230771752286655193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18173298820514501524436795 27259948230771752286655193)
            ·
              refine ⟨20444961173078814214991395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27259948230771752286655193 20444961173078814214991395)
              ·
                refine ⟨30667441759618221322487093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20444961173078814214991395 30667441759618221322487093)
                ·
                  refine ⟨2875072664964208248983165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30667441759618221322487093 2875072664964208248983165)
                  ·
                    refine ⟨1078152249361578093368687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875072664964208248983165 1078152249361578093368687)
                    ·
                      rfl

theorem cell22_3149541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_3149541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149541 prefixEnd_3149541 := by exact prefixLift 3149541
  have htrace : WordTrace (prefixWord ++ tailWord_3149541) baseStart_3149541 baseEnd_3149541 := by
    simpa [prefixWord, tailWord_3149541, baseEnd_3149541] using wordTrace_append hprefix tailTrace_3149541
  have hstable : (prefixWord ++ tailWord_3149541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149541).length < 2 ^ (prefixWord ++ tailWord_3149541).sum := by decide
  have hdescent : baseEnd_3149541 < baseStart_3149541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149601 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3149601 : Nat := 118140960795 + 3149601 * 2 ^ 59
def prefixEnd_3149601 : Nat := 4983230072969 + 3 ^ 40 * 3149601 * 2
def baseEnd_3149601 : Nat := 1078172788587757936868503

theorem tailTrace_3149601 : CollatzResearch.WordTrace tailWord_3149601 prefixEnd_3149601 1078172788587757936868503 := by
  unfold tailWord_3149601
  simp only [CollatzResearch.WordTrace]
  refine ⟨114875385862540960870784657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76583590575027307247189771 114875385862540960870784657)
  ·
    refine ⟨86156539396905720653088493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114875385862540960870784657 86156539396905720653088493)
    ·
      refine ⟨32308702273839645244908185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86156539396905720653088493 32308702273839645244908185)
      ·
        refine ⟨24231526705379733933681139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32308702273839645244908185 24231526705379733933681139)
        ·
          refine ⟨36347290058069600900521709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24231526705379733933681139 36347290058069600900521709)
          ·
            refine ⟨13630233771776100337695641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36347290058069600900521709 13630233771776100337695641)
            ·
              refine ⟨10222675328832075253271731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13630233771776100337695641 10222675328832075253271731)
              ·
                refine ⟨15334012993248112879907597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10222675328832075253271731 15334012993248112879907597)
                ·
                  refine ⟨5750254872468042329965349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15334012993248112879907597 5750254872468042329965349)
                  ·
                    refine ⟨1078172788587757936868503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5750254872468042329965349 1078172788587757936868503)
                    ·
                      rfl

theorem cell22_3149601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3149601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149601 prefixEnd_3149601 := by exact prefixLift 3149601
  have htrace : WordTrace (prefixWord ++ tailWord_3149601) baseStart_3149601 baseEnd_3149601 := by
    simpa [prefixWord, tailWord_3149601, baseEnd_3149601] using wordTrace_append hprefix tailTrace_3149601
  have hstable : (prefixWord ++ tailWord_3149601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149601).length < 2 ^ (prefixWord ++ tailWord_3149601).sum := by decide
  have hdescent : baseEnd_3149601 < baseStart_3149601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149618 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_3149618 : Nat := 118140960795 + 3149618 * 2 ^ 59
def prefixEnd_3149618 : Nat := 4983230072969 + 3 ^ 40 * 3149618 * 2
def baseEnd_3149618 : Nat := 1078178608035175559193451

theorem tailTrace_3149618 : CollatzResearch.WordTrace tailWord_3149618 prefixEnd_3149618 1078178608035175559193451 := by
  unfold tailWord_3149618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28719001475869843193538377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76584003935652915182769005 28719001475869843193538377)
  ·
    refine ⟨21539251106902382395153783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28719001475869843193538377 21539251106902382395153783)
    ·
      refine ⟨32308876660353573592730675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21539251106902382395153783 32308876660353573592730675)
      ·
        refine ⟨48463314990530360389096013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32308876660353573592730675 48463314990530360389096013)
        ·
          refine ⟨18173743121448885145911005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48463314990530360389096013 18173743121448885145911005)
          ·
            refine ⟨6815153670543331929716627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18173743121448885145911005 6815153670543331929716627)
            ·
              refine ⟨10222730505814997894574941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6815153670543331929716627 10222730505814997894574941)
              ·
                refine ⟨3833523939680624210465603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10222730505814997894574941 3833523939680624210465603)
                ·
                  refine ⟨5750285909520936315698405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833523939680624210465603 5750285909520936315698405)
                  ·
                    refine ⟨1078178608035175559193451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5750285909520936315698405 1078178608035175559193451)
                    ·
                      rfl

theorem cell22_3149618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_3149618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149618 prefixEnd_3149618 := by exact prefixLift 3149618
  have htrace : WordTrace (prefixWord ++ tailWord_3149618) baseStart_3149618 baseEnd_3149618 := by
    simpa [prefixWord, tailWord_3149618, baseEnd_3149618] using wordTrace_append hprefix tailTrace_3149618
  have hstable : (prefixWord ++ tailWord_3149618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149618).length < 2 ^ (prefixWord ++ tailWord_3149618).sum := by decide
  have hdescent : baseEnd_3149618 < baseStart_3149618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149667 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 4]
def baseStart_3149667 : Nat := 118140960795 + 3149667 * 2 ^ 59
def prefixEnd_3149667 : Nat := 4983230072969 + 3 ^ 40 * 3149667 * 2
def baseEnd_3149667 : Nat := 359398460578851921572767

theorem tailTrace_3149667 : CollatzResearch.WordTrace tailWord_3149667 prefixEnd_3149667 359398460578851921572767 := by
  unfold tailWord_3149667
  simp only [CollatzResearch.WordTrace]
  refine ⟨114877793080301854142687255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76585195386867902761791503 114877793080301854142687255)
  ·
    refine ⟨172316689620452781214030883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114877793080301854142687255 172316689620452781214030883)
    ·
      refine ⟨258475034430679171821046325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172316689620452781214030883 258475034430679171821046325)
      ·
        refine ⟨24232034477876172358223093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258475034430679171821046325 24232034477876172358223093)
        ·
          refine ⟨2271753232300891158583415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24232034477876172358223093 2271753232300891158583415)
          ·
            refine ⟨3407629848451336737875123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271753232300891158583415 3407629848451336737875123)
            ·
              refine ⟨5111444772677005106812685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407629848451336737875123 5111444772677005106812685)
              ·
                refine ⟨1916791789753876915054757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5111444772677005106812685 1916791789753876915054757)
                ·
                  refine ⟨359398460578851921572767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916791789753876915054757 359398460578851921572767)
                  ·
                    rfl

theorem cell22_3149667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 4].length) (baseStart_3149667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149667 prefixEnd_3149667 := by exact prefixLift 3149667
  have htrace : WordTrace (prefixWord ++ tailWord_3149667) baseStart_3149667 baseEnd_3149667 := by
    simpa [prefixWord, tailWord_3149667, baseEnd_3149667] using wordTrace_append hprefix tailTrace_3149667
  have hstable : (prefixWord ++ tailWord_3149667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149667).length < 2 ^ (prefixWord ++ tailWord_3149667).sum := by decide
  have hdescent : baseEnd_3149667 < baseStart_3149667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149678 : List Nat := [4, 1, 2, 3, 1, 3, 8]
def baseStart_3149678 : Nat := 118140960795 + 3149678 * 2 ^ 59
def prefixEnd_3149678 : Nat := 4983230072969 + 3 ^ 40 * 3149678 * 2
def baseEnd_3149678 : Nat := 39933301750420570470121

theorem tailTrace_3149678 : CollatzResearch.WordTrace tailWord_3149678 prefixEnd_3149678 39933301750420570470121 := by
  unfold tailWord_3149678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14359774285407750377667211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76585462855508002014225125 14359774285407750377667211)
  ·
    refine ⟨21539661428111625566500817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14359774285407750377667211 21539661428111625566500817)
    ·
      refine ⟨16154746071083719174875613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21539661428111625566500817 16154746071083719174875613)
      ·
        refine ⟨6058029776656394690578355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16154746071083719174875613 6058029776656394690578355)
        ·
          refine ⟨9087044664984592035867533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058029776656394690578355 9087044664984592035867533)
          ·
            refine ⟨3407641749369222013450325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9087044664984592035867533 3407641749369222013450325)
            ·
              refine ⟨39933301750420570470121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3407641749369222013450325 39933301750420570470121)
              ·
                rfl

theorem cell22_3149678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 8].length) (baseStart_3149678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149678 prefixEnd_3149678 := by exact prefixLift 3149678
  have htrace : WordTrace (prefixWord ++ tailWord_3149678) baseStart_3149678 baseEnd_3149678 := by
    simpa [prefixWord, tailWord_3149678, baseEnd_3149678] using wordTrace_append hprefix tailTrace_3149678
  have hstable : (prefixWord ++ tailWord_3149678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149678).length < 2 ^ (prefixWord ++ tailWord_3149678).sum := by decide
  have hdescent : baseEnd_3149678 < baseStart_3149678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149751 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 6]
def baseStart_3149751 : Nat := 118140960795 + 3149751 * 2 ^ 59
def prefixEnd_3149751 : Nat := 4983230072969 + 3 ^ 40 * 3149751 * 2
def baseEnd_3149751 : Nat := 359408045551069181872681

theorem tailTrace_3149751 : CollatzResearch.WordTrace tailWord_3149751 prefixEnd_3149751 359408045551069181872681 := by
  unfold tailWord_3149751
  simp only [CollatzResearch.WordTrace]
  refine ⟨114880856811997536488745107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76587237874665024325830071 114880856811997536488745107)
  ·
    refine ⟨172321285217996304733117661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114880856811997536488745107 172321285217996304733117661)
    ·
      refine ⟨64620481956748614274919123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172321285217996304733117661 64620481956748614274919123)
      ·
        refine ⟨96930722935122921412378685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64620481956748614274919123 96930722935122921412378685)
        ·
          refine ⟨36349021100671095529642007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96930722935122921412378685 36349021100671095529642007)
          ·
            refine ⟨54523531651006643294463011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36349021100671095529642007 54523531651006643294463011)
            ·
              refine ⟨81785297476509964941694517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54523531651006643294463011 81785297476509964941694517)
              ·
                refine ⟨7667371638422809213283861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81785297476509964941694517 7667371638422809213283861)
                ·
                  refine ⟨359408045551069181872681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7667371638422809213283861 359408045551069181872681)
                  ·
                    rfl

theorem cell22_3149751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 6].length) (baseStart_3149751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149751 prefixEnd_3149751 := by exact prefixLift 3149751
  have htrace : WordTrace (prefixWord ++ tailWord_3149751) baseStart_3149751 baseEnd_3149751 := by
    simpa [prefixWord, tailWord_3149751, baseEnd_3149751] using wordTrace_append hprefix tailTrace_3149751
  have hstable : (prefixWord ++ tailWord_3149751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149751).length < 2 ^ (prefixWord ++ tailWord_3149751).sum := by decide
  have hdescent : baseEnd_3149751 < baseStart_3149751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149768 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_3149768 : Nat := 118140960795 + 3149768 * 2 ^ 59
def prefixEnd_3149768 : Nat := 4983230072969 + 3 ^ 40 * 3149768 * 2
def baseEnd_3149768 : Nat := 359409985366875055980997

theorem tailTrace_3149768 : CollatzResearch.WordTrace tailWord_3149768 prefixEnd_3149768 359409985366875055980997 := by
  unfold tailWord_3149768
  simp only [CollatzResearch.WordTrace]
  refine ⟨57440738426467974196056979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76587651235290632261409305 57440738426467974196056979)
  ·
    refine ⟨86161107639701961294085469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57440738426467974196056979 86161107639701961294085469)
    ·
      refine ⟨32310415364888235485282051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86161107639701961294085469 32310415364888235485282051)
      ·
        refine ⟨48465623047332353227923077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32310415364888235485282051 48465623047332353227923077)
        ·
          refine ⟨9087304321374816230235577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48465623047332353227923077 9087304321374816230235577)
          ·
            refine ⟨6815478241031112172676683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9087304321374816230235577 6815478241031112172676683)
            ·
              refine ⟨10223217361546668259015025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6815478241031112172676683 10223217361546668259015025)
              ·
                refine ⟨7667413021160001194261269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10223217361546668259015025 7667413021160001194261269)
                ·
                  refine ⟨359409985366875055980997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7667413021160001194261269 359409985366875055980997)
                  ·
                    rfl

theorem cell22_3149768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_3149768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149768 prefixEnd_3149768 := by exact prefixLift 3149768
  have htrace : WordTrace (prefixWord ++ tailWord_3149768) baseStart_3149768 baseEnd_3149768 := by
    simpa [prefixWord, tailWord_3149768, baseEnd_3149768] using wordTrace_append hprefix tailTrace_3149768
  have hstable : (prefixWord ++ tailWord_3149768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149768).length < 2 ^ (prefixWord ++ tailWord_3149768).sum := by decide
  have hdescent : baseEnd_3149768 < baseStart_3149768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149783 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 4, 3]
def baseStart_3149783 : Nat := 118140960795 + 3149783 * 2 ^ 59
def prefixEnd_3149783 : Nat := 4983230072969 + 3 ^ 40 * 3149783 * 2
def baseEnd_3149783 : Nat := 1078235090907170128817945

theorem tailTrace_3149783 : CollatzResearch.WordTrace tailWord_3149783 prefixEnd_3149783 1078235090907170128817945 := by
  unfold tailWord_3149783
  simp only [CollatzResearch.WordTrace]
  refine ⟨114882023947881605953910003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76588015965254403969273335 114882023947881605953910003)
  ·
    refine ⟨172323035921822408930865005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114882023947881605953910003 172323035921822408930865005)
    ·
      refine ⟨64621138470683403349074377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172323035921822408930865005 64621138470683403349074377)
      ·
        refine ⟨48465853853012552511805783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64621138470683403349074377 48465853853012552511805783)
        ·
          refine ⟨72698780779518828767708675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48465853853012552511805783 72698780779518828767708675)
          ·
            refine ⟨109048171169278243151563013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72698780779518828767708675 109048171169278243151563013)
            ·
              refine ⟨20446532094239670590918065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109048171169278243151563013 20446532094239670590918065)
              ·
                refine ⟨15334899070679752943188549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20446532094239670590918065 15334899070679752943188549)
                ·
                  refine ⟨2875293575752453676847853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15334899070679752943188549 2875293575752453676847853)
                  ·
                    refine ⟨1078235090907170128817945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875293575752453676847853 1078235090907170128817945)
                    ·
                      rfl

theorem cell22_3149783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_3149783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149783 prefixEnd_3149783 := by exact prefixLift 3149783
  have htrace : WordTrace (prefixWord ++ tailWord_3149783) baseStart_3149783 baseEnd_3149783 := by
    simpa [prefixWord, tailWord_3149783, baseEnd_3149783] using wordTrace_append hprefix tailTrace_3149783
  have hstable : (prefixWord ++ tailWord_3149783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149783).length < 2 ^ (prefixWord ++ tailWord_3149783).sum := by decide
  have hdescent : baseEnd_3149783 < baseStart_3149783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149796 : List Nat := [2, 3, 1, 1, 1, 1, 13]
def baseStart_3149796 : Nat := 118140960795 + 3149796 * 2 ^ 59
def prefixEnd_3149796 : Nat := 4983230072969 + 3 ^ 40 * 3149796 * 2
def baseEnd_3149796 : Nat := 39934797817512682527515

theorem tailTrace_3149796 : CollatzResearch.WordTrace tailWord_3149796 prefixEnd_3149796 39934797817512682527515 := by
  unfold tailWord_3149796
  simp only [CollatzResearch.WordTrace]
  refine ⟨57441249048417254587066621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76588332064556339449422161 57441249048417254587066621)
  ·
    refine ⟨21540468393156470470149983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57441249048417254587066621 21540468393156470470149983)
    ·
      refine ⟨32310702589734705705224975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21540468393156470470149983 32310702589734705705224975)
      ·
        refine ⟨48466053884602058557837463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32310702589734705705224975 48466053884602058557837463)
        ·
          refine ⟨72699080826903087836756195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48466053884602058557837463 72699080826903087836756195)
          ·
            refine ⟨109048621240354631755134293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72699080826903087836756195 109048621240354631755134293)
            ·
              refine ⟨39934797817512682527515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 109048621240354631755134293 39934797817512682527515)
              ·
                rfl

theorem cell22_3149796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 13].length) (baseStart_3149796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149796 prefixEnd_3149796 := by exact prefixLift 3149796
  have htrace : WordTrace (prefixWord ++ tailWord_3149796) baseStart_3149796 baseEnd_3149796 := by
    simpa [prefixWord, tailWord_3149796, baseEnd_3149796] using wordTrace_append hprefix tailTrace_3149796
  have hstable : (prefixWord ++ tailWord_3149796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149796).length < 2 ^ (prefixWord ++ tailWord_3149796).sum := by decide
  have hdescent : baseEnd_3149796 < baseStart_3149796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149817 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 2, 3]
def baseStart_3149817 : Nat := 118140960795 + 3149817 * 2 ^ 59
def prefixEnd_3149817 : Nat := 4983230072969 + 3 ^ 40 * 3149817 * 2
def baseEnd_3149817 : Nat := 1078246729802005373467841

theorem tailTrace_3149817 : CollatzResearch.WordTrace tailWord_3149817 prefixEnd_3149817 1078246729802005373467841 := by
  unfold tailWord_3149817
  simp only [CollatzResearch.WordTrace]
  refine ⟨114883264029758429760647705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76588842686505619840431803 114883264029758429760647705)
  ·
    refine ⟨86162448022318822320485779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114883264029758429760647705 86162448022318822320485779)
    ·
      refine ⟨129243672033478233480728669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86162448022318822320485779 129243672033478233480728669)
      ·
        refine ⟨48466377012554337555273251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129243672033478233480728669 48466377012554337555273251)
        ·
          refine ⟨72699565518831506332909877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48466377012554337555273251 72699565518831506332909877)
          ·
            refine ⟨6815584267390453718710301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72699565518831506332909877 6815584267390453718710301)
            ·
              refine ⟨2555844100271420144516363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6815584267390453718710301 2555844100271420144516363)
              ·
                refine ⟨3833766150407130216774545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555844100271420144516363 3833766150407130216774545)
                ·
                  refine ⟨2875324612805347662580909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833766150407130216774545 2875324612805347662580909)
                  ·
                    refine ⟨1078246729802005373467841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875324612805347662580909 1078246729802005373467841)
                    ·
                      rfl

theorem cell22_3149817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_3149817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149817 prefixEnd_3149817 := by exact prefixLift 3149817
  have htrace : WordTrace (prefixWord ++ tailWord_3149817) baseStart_3149817 baseEnd_3149817 := by
    simpa [prefixWord, tailWord_3149817, baseEnd_3149817] using wordTrace_append hprefix tailTrace_3149817
  have hstable : (prefixWord ++ tailWord_3149817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149817).length < 2 ^ (prefixWord ++ tailWord_3149817).sum := by decide
  have hdescent : baseEnd_3149817 < baseStart_3149817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149858 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_3149858 : Nat := 118140960795 + 3149858 * 2 ^ 59
def prefixEnd_3149858 : Nat := 4983230072969 + 3 ^ 40 * 3149858 * 2
def baseEnd_3149858 : Nat := 359420254979964977730905

theorem tailTrace_3149858 : CollatzResearch.WordTrace tailWord_3149858 prefixEnd_3149858 359420254979964977730905 := by
  unfold tailWord_3149858
  simp only [CollatzResearch.WordTrace]
  refine ⟨28721189855652473440722557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76589839615073262508593485 28721189855652473440722557)
  ·
    refine ⟨10770446195869677540270959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28721189855652473440722557 10770446195869677540270959)
    ·
      refine ⟨16155669293804516310406439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10770446195869677540270959 16155669293804516310406439)
      ·
        refine ⟨24233503940706774465609659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16155669293804516310406439 24233503940706774465609659)
        ·
          refine ⟨36350255911060161698414489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24233503940706774465609659 36350255911060161698414489)
          ·
            refine ⟨27262691933295121273810867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36350255911060161698414489 27262691933295121273810867)
            ·
              refine ⟨40894037899942681910716301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27262691933295121273810867 40894037899942681910716301)
              ·
                refine ⟨15335264212478505716518613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40894037899942681910716301 15335264212478505716518613)
                ·
                  refine ⟨359420254979964977730905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15335264212478505716518613 359420254979964977730905)
                  ·
                    rfl

theorem cell22_3149858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_3149858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149858 prefixEnd_3149858 := by exact prefixLift 3149858
  have htrace : WordTrace (prefixWord ++ tailWord_3149858) baseStart_3149858 baseEnd_3149858 := by
    simpa [prefixWord, tailWord_3149858, baseEnd_3149858] using wordTrace_append hprefix tailTrace_3149858
  have hstable : (prefixWord ++ tailWord_3149858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149858).length < 2 ^ (prefixWord ++ tailWord_3149858).sum := by decide
  have hdescent : baseEnd_3149858 < baseStart_3149858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149875 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 5]
def baseStart_3149875 : Nat := 118140960795 + 3149875 * 2 ^ 59
def prefixEnd_3149875 : Nat := 4983230072969 + 3 ^ 40 * 3149875 * 2
def baseEnd_3149875 : Nat := 359422194795770851839221

theorem tailTrace_3149875 : CollatzResearch.WordTrace tailWord_3149875 prefixEnd_3149875 359422194795770851839221 := by
  unfold tailWord_3149875
  simp only [CollatzResearch.WordTrace]
  refine ⟨114885379463548305666259079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76590252975698870444172719 114885379463548305666259079)
  ·
    refine ⟨172328069195322458499388619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114885379463548305666259079 172328069195322458499388619)
    ·
      refine ⟨258492103792983687749082929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172328069195322458499388619 258492103792983687749082929)
      ·
        refine ⟨193869077844737765811812197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258492103792983687749082929 193869077844737765811812197)
        ·
          refine ⟨36350452095888331089714787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193869077844737765811812197 36350452095888331089714787)
          ·
            refine ⟨54525678143832496634572181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36350452095888331089714787 54525678143832496634572181)
            ·
              refine ⟨2555891162992148279745571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54525678143832496634572181 2555891162992148279745571)
              ·
                refine ⟨3833836744488222419618357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555891162992148279745571 3833836744488222419618357)
                ·
                  refine ⟨359422194795770851839221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3833836744488222419618357 359422194795770851839221)
                  ·
                    rfl

theorem cell22_3149875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 5].length) (baseStart_3149875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149875 prefixEnd_3149875 := by exact prefixLift 3149875
  have htrace : WordTrace (prefixWord ++ tailWord_3149875) baseStart_3149875 baseEnd_3149875 := by
    simpa [prefixWord, tailWord_3149875, baseEnd_3149875] using wordTrace_append hprefix tailTrace_3149875
  have hstable : (prefixWord ++ tailWord_3149875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149875).length < 2 ^ (prefixWord ++ tailWord_3149875).sum := by decide
  have hdescent : baseEnd_3149875 < baseStart_3149875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149935 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 1, 5]
def baseStart_3149935 : Nat := 118140960795 + 3149935 * 2 ^ 59
def prefixEnd_3149935 : Nat := 4983230072969 + 3 ^ 40 * 3149935 * 2
def baseEnd_3149935 : Nat := 1078287123613492399017479

theorem tailTrace_3149935 : CollatzResearch.WordTrace tailWord_3149935 prefixEnd_3149935 1078287123613492399017479 := by
  unfold tailWord_3149935
  simp only [CollatzResearch.WordTrace]
  refine ⟨114887567843330935913443259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76591711895553957275628839 114887567843330935913443259)
  ·
    refine ⟨172331351764996403870164889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114887567843330935913443259 172331351764996403870164889)
    ·
      refine ⟨129248513823747302902623667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172331351764996403870164889 129248513823747302902623667)
      ·
        refine ⟨193872770735620954353935501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129248513823747302902623667 193872770735620954353935501)
        ·
          refine ⟨72702289025857857882725813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193872770735620954353935501 72702289025857857882725813)
          ·
            refine ⟨6815839596174174176505545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72702289025857857882725813 6815839596174174176505545)
            ·
              refine ⟨5111879697130630632379159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6815839596174174176505545 5111879697130630632379159)
              ·
                refine ⟨7667819545695945948568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111879697130630632379159 7667819545695945948568739)
                ·
                  refine ⟨11501729318543918922853109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7667819545695945948568739 11501729318543918922853109)
                  ·
                    refine ⟨1078287123613492399017479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11501729318543918922853109 1078287123613492399017479)
                    ·
                      rfl

theorem cell22_3149935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_3149935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149935 prefixEnd_3149935 := by exact prefixLift 3149935
  have htrace : WordTrace (prefixWord ++ tailWord_3149935) baseStart_3149935 baseEnd_3149935 := by
    simpa [prefixWord, tailWord_3149935, baseEnd_3149935] using wordTrace_append hprefix tailTrace_3149935
  have hstable : (prefixWord ++ tailWord_3149935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149935).length < 2 ^ (prefixWord ++ tailWord_3149935).sum := by decide
  have hdescent : baseEnd_3149935 < baseStart_3149935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149986 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3149986 : Nat := 118140960795 + 3149986 * 2 ^ 59
def prefixEnd_3149986 : Nat := 4983230072969 + 3 ^ 40 * 3149986 * 2
def baseEnd_3149986 : Nat := 1078304581955745265992323

theorem tailTrace_3149986 : CollatzResearch.WordTrace tailWord_3149986 prefixEnd_3149986 1078304581955745265992323 := by
  unfold tailWord_3149986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28722356991536542905887453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76592951977430781082366541 28722356991536542905887453)
  ·
    refine ⟨10770883871826203589707795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28722356991536542905887453 10770883871826203589707795)
    ·
      refine ⟨16156325807739305384561693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10770883871826203589707795 16156325807739305384561693)
      ·
        refine ⟨6058622177902239519210635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16156325807739305384561693 6058622177902239519210635)
        ·
          refine ⟨9087933266853359278815953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058622177902239519210635 9087933266853359278815953)
          ·
            refine ⟨6815949950140019459111965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9087933266853359278815953 6815949950140019459111965)
            ·
              refine ⟨2555981231302507297166987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6815949950140019459111965 2555981231302507297166987)
              ·
                refine ⟨3833971846953760945750481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555981231302507297166987 3833971846953760945750481)
                ·
                  refine ⟨2875478885215320709312861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833971846953760945750481 2875478885215320709312861)
                  ·
                    refine ⟨1078304581955745265992323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875478885215320709312861 1078304581955745265992323)
                    ·
                      rfl

theorem cell22_3149986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3149986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3149986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3149986 prefixEnd_3149986 := by exact prefixLift 3149986
  have htrace : WordTrace (prefixWord ++ tailWord_3149986) baseStart_3149986 baseEnd_3149986 := by
    simpa [prefixWord, tailWord_3149986, baseEnd_3149986] using wordTrace_append hprefix tailTrace_3149986
  have hstable : (prefixWord ++ tailWord_3149986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149986).length < 2 ^ (prefixWord ++ tailWord_3149986).sum := by decide
  have hdescent : baseEnd_3149986 < baseStart_3149986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150074 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_3150074 : Nat := 118140960795 + 3150074 * 2 ^ 59
def prefixEnd_3150074 : Nat := 4983230072969 + 3 ^ 40 * 3150074 * 2
def baseEnd_3150074 : Nat := 1078334706154142369792053

theorem tailTrace_3150074 : CollatzResearch.WordTrace tailWord_3150074 prefixEnd_3150074 1078334706154142369792053 := by
  unfold tailWord_3150074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28723159397456840663188319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76595091726551575101835517 28723159397456840663188319)
  ·
    refine ⟨43084739096185260994782479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28723159397456840663188319 43084739096185260994782479)
    ·
      refine ⟨64627108644277891492173719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43084739096185260994782479 64627108644277891492173719)
      ·
        refine ⟨96940662966416837238260579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64627108644277891492173719 96940662966416837238260579)
        ·
          refine ⟨145410994449625255857390869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96940662966416837238260579 145410994449625255857390869)
          ·
            refine ⟨6816140364826183868315197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145410994449625255857390869 6816140364826183868315197)
            ·
              refine ⟨2556052636809818950618199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6816140364826183868315197 2556052636809818950618199)
              ·
                refine ⟨3834078955214728425927299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556052636809818950618199 3834078955214728425927299)
                ·
                  refine ⟨5751118432822092638890949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834078955214728425927299 5751118432822092638890949)
                  ·
                    refine ⟨1078334706154142369792053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751118432822092638890949 1078334706154142369792053)
                    ·
                      rfl

theorem cell22_3150074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_3150074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150074 prefixEnd_3150074 := by exact prefixLift 3150074
  have htrace : WordTrace (prefixWord ++ tailWord_3150074) baseStart_3150074 baseEnd_3150074 := by
    simpa [prefixWord, tailWord_3150074, baseEnd_3150074] using wordTrace_append hprefix tailTrace_3150074
  have hstable : (prefixWord ++ tailWord_3150074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150074).length < 2 ^ (prefixWord ++ tailWord_3150074).sum := by decide
  have hdescent : baseEnd_3150074 < baseStart_3150074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150085 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_3150085 : Nat := 118140960795 + 3150085 * 2 ^ 59
def prefixEnd_3150085 : Nat := 4983230072969 + 3 ^ 40 * 3150085 * 2
def baseEnd_3150085 : Nat := 1078338471678942007767019

theorem tailTrace_3150085 : CollatzResearch.WordTrace tailWord_3150085 prefixEnd_3150085 1078338471678942007767019 := by
  unfold tailWord_3150085
  simp only [CollatzResearch.WordTrace]
  refine ⟨114893038792787511531403709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76595359195191674354269139 114893038792787511531403709)
  ·
    refine ⟨43084889547295316824276391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114893038792787511531403709 43084889547295316824276391)
    ·
      refine ⟨64627334320942975236414587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43084889547295316824276391 64627334320942975236414587)
      ·
        refine ⟨96941001481414462854621881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64627334320942975236414587 96941001481414462854621881)
        ·
          refine ⟨72705751111060847140966411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96941001481414462854621881 72705751111060847140966411)
          ·
            refine ⟨109058626666591270711449617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72705751111060847140966411 109058626666591270711449617)
            ·
              refine ⟨81793969999943453033587213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109058626666591270711449617 81793969999943453033587213)
              ·
                refine ⟨30672738749978794887595205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81793969999943453033587213 30672738749978794887595205)
                ·
                  refine ⟨5751138515621024041424101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30672738749978794887595205 5751138515621024041424101)
                  ·
                    refine ⟨1078338471678942007767019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751138515621024041424101 1078338471678942007767019)
                    ·
                      rfl

theorem cell22_3150085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_3150085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150085 prefixEnd_3150085 := by exact prefixLift 3150085
  have htrace : WordTrace (prefixWord ++ tailWord_3150085) baseStart_3150085 baseEnd_3150085 := by
    simpa [prefixWord, tailWord_3150085, baseEnd_3150085] using wordTrace_append hprefix tailTrace_3150085
  have hstable : (prefixWord ++ tailWord_3150085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150085).length < 2 ^ (prefixWord ++ tailWord_3150085).sum := by decide
  have hdescent : baseEnd_3150085 < baseStart_3150085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150089 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 4]
def baseStart_3150089 : Nat := 118140960795 + 3150089 * 2 ^ 59
def prefixEnd_3150089 : Nat := 4983230072969 + 3 ^ 40 * 3150089 * 2
def baseEnd_3150089 : Nat := 359446613653562443555669

theorem tailTrace_3150089 : CollatzResearch.WordTrace tailWord_3150089 prefixEnd_3150089 359446613653562443555669 := by
  unfold tailWord_3150089
  simp only [CollatzResearch.WordTrace]
  refine ⟨114893184684773020214549321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76595456456515346809699547 114893184684773020214549321)
  ·
    refine ⟨86169888513579765160911991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114893184684773020214549321 86169888513579765160911991)
    ·
      refine ⟨129254832770369647741367987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86169888513579765160911991 129254832770369647741367987)
      ·
        refine ⟨193882249155554471612051981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129254832770369647741367987 193882249155554471612051981)
        ·
          refine ⟨72705843433332926854519493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193882249155554471612051981 72705843433332926854519493)
          ·
            refine ⟨13632345643749923785222405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72705843433332926854519493 13632345643749923785222405)
            ·
              refine ⟨2556064808203110709729201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13632345643749923785222405 2556064808203110709729201)
              ·
                refine ⟨1917048606152333032296901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556064808203110709729201 1917048606152333032296901)
                ·
                  refine ⟨359446613653562443555669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917048606152333032296901 359446613653562443555669)
                  ·
                    rfl

theorem cell22_3150089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_3150089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150089 prefixEnd_3150089 := by exact prefixLift 3150089
  have htrace : WordTrace (prefixWord ++ tailWord_3150089) baseStart_3150089 baseEnd_3150089 := by
    simpa [prefixWord, tailWord_3150089, baseEnd_3150089] using wordTrace_append hprefix tailTrace_3150089
  have hstable : (prefixWord ++ tailWord_3150089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150089).length < 2 ^ (prefixWord ++ tailWord_3150089).sum := by decide
  have hdescent : baseEnd_3150089 < baseStart_3150089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
