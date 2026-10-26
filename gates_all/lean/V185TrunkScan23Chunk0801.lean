import V185TrunkScan23Chunk0800

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4738136 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_4738136 : Nat := 118140960795 + 4738136 * 2 ^ 59
def prefixEnd_4738136 : Nat := 4983230072969 + 3 ^ 40 * 4738136 * 2
def baseEnd_4738136 : Nat := 2432941174371579254809715

theorem tailTrace_4738136 : CollatzResearch.WordTrace tailWord_4738136 prefixEnd_4738136 2432941174371579254809715 := by
  unfold tailWord_4738136
  simp only [CollatzResearch.WordTrace]
  refine ⟨86407008581274978024737131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115209344775033304032982841 86407008581274978024737131)
  ·
    refine ⟨129610512871912467037105697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86407008581274978024737131 129610512871912467037105697)
    ·
      refine ⟨97207884653934350277829273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129610512871912467037105697 97207884653934350277829273)
      ·
        refine ⟨72905913490450762708371955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97207884653934350277829273 72905913490450762708371955)
        ·
          refine ⟨109358870235676144062557933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72905913490450762708371955 109358870235676144062557933)
          ·
            refine ⟨41009576338378554023459225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109358870235676144062557933 41009576338378554023459225)
            ·
              refine ⟨30757182253783915517594419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41009576338378554023459225 30757182253783915517594419)
              ·
                refine ⟨46135773380675873276391629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30757182253783915517594419 46135773380675873276391629)
                ·
                  refine ⟨17300915017753452478646861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46135773380675873276391629 17300915017753452478646861)
                  ·
                    refine ⟨6487843131657544679492573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17300915017753452478646861 6487843131657544679492573)
                    ·
                      refine ⟨2432941174371579254809715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6487843131657544679492573 2432941174371579254809715)
                      ·
                        rfl

theorem cell23_4738136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_4738136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738136 prefixEnd_4738136 := by exact prefixLift 4738136
  have htrace : WordTrace (prefixWord ++ tailWord_4738136) baseStart_4738136 baseEnd_4738136 := by
    simpa [prefixWord, tailWord_4738136, baseEnd_4738136] using wordTrace_append hprefix tailTrace_4738136
  have hstable : (prefixWord ++ tailWord_4738136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738136).length < 2 ^ (prefixWord ++ tailWord_4738136).sum := by decide
  have hdescent : baseEnd_4738136 < baseStart_4738136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738153 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 3]
def baseStart_4738153 : Nat := 118140960795 + 4738153 * 2 ^ 59
def prefixEnd_4738153 : Nat := 4983230072969 + 3 ^ 40 * 4738153 * 2
def baseEnd_4738153 : Nat := 2432949903542705688297137

theorem tailTrace_4738153 : CollatzResearch.WordTrace tailWord_4738153 prefixEnd_4738153 2432949903542705688297137 := by
  unfold tailWord_4738153
  simp only [CollatzResearch.WordTrace]
  refine ⟨172814637203488367952843113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115209758135658911968562075 172814637203488367952843113)
  ·
    refine ⟨129610977902616275964632335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172814637203488367952843113 129610977902616275964632335)
    ·
      refine ⟨194416466853924413946948503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129610977902616275964632335 194416466853924413946948503)
      ·
        refine ⟨291624700280886620920422755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194416466853924413946948503 291624700280886620920422755)
        ·
          refine ⟨437437050421329931380634133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291624700280886620920422755 437437050421329931380634133)
          ·
            refine ⟨20504861738499840533467225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 437437050421329931380634133 20504861738499840533467225)
            ·
              refine ⟨15378646303874880400100419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20504861738499840533467225 15378646303874880400100419)
              ·
                refine ⟨23067969455812320600150629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15378646303874880400100419 23067969455812320600150629)
                ·
                  refine ⟨4325244272964810112528243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23067969455812320600150629 4325244272964810112528243)
                  ·
                    refine ⟨6487866409447215168792365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4325244272964810112528243 6487866409447215168792365)
                    ·
                      refine ⟨2432949903542705688297137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6487866409447215168792365 2432949903542705688297137)
                      ·
                        rfl

theorem cell23_4738153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_4738153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738153 prefixEnd_4738153 := by exact prefixLift 4738153
  have htrace : WordTrace (prefixWord ++ tailWord_4738153) baseStart_4738153 baseEnd_4738153 := by
    simpa [prefixWord, tailWord_4738153, baseEnd_4738153] using wordTrace_append hprefix tailTrace_4738153
  have hstable : (prefixWord ++ tailWord_4738153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738153).length < 2 ^ (prefixWord ++ tailWord_4738153).sum := by decide
  have hdescent : baseEnd_4738153 < baseStart_4738153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738174 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4738174 : Nat := 118140960795 + 4738174 * 2 ^ 59
def prefixEnd_4738174 : Nat := 4983230072969 + 3 ^ 40 * 4738174 * 2
def baseEnd_4738174 : Nat := 2432960686636450106134541

theorem tailTrace_4738174 : CollatzResearch.WordTrace tailWord_4738174 prefixEnd_4738174 2432960686636450106134541 := by
  unfold tailWord_4738174
  simp only [CollatzResearch.WordTrace]
  refine ⟨21601925392051536067419697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115210268757608192359571717 21601925392051536067419697)
  ·
    refine ⟨16201444044038652050564773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21601925392051536067419697 16201444044038652050564773)
    ·
      refine ⟨3037770758257247259480895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16201444044038652050564773 3037770758257247259480895)
      ·
        refine ⟨4556656137385870889221343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037770758257247259480895 4556656137385870889221343)
        ·
          refine ⟨6834984206078806333832015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556656137385870889221343 6834984206078806333832015)
          ·
            refine ⟨10252476309118209500748023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834984206078806333832015 10252476309118209500748023)
            ·
              refine ⟨15378714463677314251122035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10252476309118209500748023 15378714463677314251122035)
              ·
                refine ⟨23068071695515971376683053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15378714463677314251122035 23068071695515971376683053)
                ·
                  refine ⟨8650526885818489266256145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23068071695515971376683053 8650526885818489266256145)
                  ·
                    refine ⟨6487895164363866949692109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8650526885818489266256145 6487895164363866949692109)
                    ·
                      refine ⟨2432960686636450106134541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6487895164363866949692109 2432960686636450106134541)
                      ·
                        rfl

theorem cell23_4738174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4738174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738174 prefixEnd_4738174 := by exact prefixLift 4738174
  have htrace : WordTrace (prefixWord ++ tailWord_4738174) baseStart_4738174 baseEnd_4738174 := by
    simpa [prefixWord, tailWord_4738174, baseEnd_4738174] using wordTrace_append hprefix tailTrace_4738174
  have hstable : (prefixWord ++ tailWord_4738174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738174).length < 2 ^ (prefixWord ++ tailWord_4738174).sum := by decide
  have hdescent : baseEnd_4738174 < baseStart_4738174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738180 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_4738180 : Nat := 118140960795 + 4738180 * 2 ^ 59
def prefixEnd_4738180 : Nat := 4983230072969 + 3 ^ 40 * 4738180 * 2
def baseEnd_4738180 : Nat := 2432963767520377082659513

theorem tailTrace_4738180 : CollatzResearch.WordTrace tailWord_4738180 prefixEnd_4738180 2432963767520377082659513 := by
  unfold tailWord_4738180
  simp only [CollatzResearch.WordTrace]
  refine ⟨86407810987195275782037997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115210414649593701042717329 86407810987195275782037997)
  ·
    refine ⟨32402929120198228418264249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86407810987195275782037997 32402929120198228418264249)
    ·
      refine ⟨24302196840148671313698187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32402929120198228418264249 24302196840148671313698187)
      ·
        refine ⟨36453295260223006970547281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24302196840148671313698187 36453295260223006970547281)
        ·
          refine ⟨27339971445167255227910461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36453295260223006970547281 27339971445167255227910461)
          ·
            refine ⟨10252489291937720710466423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27339971445167255227910461 10252489291937720710466423)
            ·
              refine ⟨15378733937906581065699635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10252489291937720710466423 15378733937906581065699635)
              ·
                refine ⟨23068100906859871598549453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15378733937906581065699635 23068100906859871598549453)
                ·
                  refine ⟨8650537840072451849456045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23068100906859871598549453 8650537840072451849456045)
                  ·
                    refine ⟨3243951690027169443546017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8650537840072451849456045 3243951690027169443546017)
                    ·
                      refine ⟨2432963767520377082659513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3243951690027169443546017 2432963767520377082659513)
                      ·
                        rfl

theorem cell23_4738180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_4738180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738180 prefixEnd_4738180 := by exact prefixLift 4738180
  have htrace : WordTrace (prefixWord ++ tailWord_4738180) baseStart_4738180 baseEnd_4738180 := by
    simpa [prefixWord, tailWord_4738180, baseEnd_4738180] using wordTrace_append hprefix tailTrace_4738180
  have hstable : (prefixWord ++ tailWord_4738180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738180).length < 2 ^ (prefixWord ++ tailWord_4738180).sum := by decide
  have hdescent : baseEnd_4738180 < baseStart_4738180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738250 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_4738250 : Nat := 118140960795 + 4738250 * 2 ^ 59
def prefixEnd_4738250 : Nat := 4983230072969 + 3 ^ 40 * 4738250 * 2
def baseEnd_4738250 : Nat := 270333301240687978753799

theorem tailTrace_4738250 : CollatzResearch.WordTrace tailWord_4738250 prefixEnd_4738250 270333301240687978753799 := by
  unfold tailWord_4738250
  simp only [CollatzResearch.WordTrace]
  refine ⟨43204543771034238379781051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115212116722757969012749469 43204543771034238379781051)
  ·
    refine ⟨64806815656551357569671577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43204543771034238379781051 64806815656551357569671577)
    ·
      refine ⟨48605111742413518177253683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64806815656551357569671577 48605111742413518177253683)
      ·
        refine ⟨72907667613620277265880525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48605111742413518177253683 72907667613620277265880525)
        ·
          refine ⟨27340375355107603974705197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72907667613620277265880525 27340375355107603974705197)
          ·
            refine ⟨10252640758165351490514449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27340375355107603974705197 10252640758165351490514449)
            ·
              refine ⟨7689480568624013617885837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10252640758165351490514449 7689480568624013617885837)
              ·
                refine ⟨2883555213234005106707189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7689480568624013617885837 2883555213234005106707189)
                ·
                  refine ⟨270333301240687978753799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2883555213234005106707189 270333301240687978753799)
                  ·
                    rfl

theorem cell23_4738250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_4738250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738250 prefixEnd_4738250 := by exact prefixLift 4738250
  have htrace : WordTrace (prefixWord ++ tailWord_4738250) baseStart_4738250 baseEnd_4738250 := by
    simpa [prefixWord, tailWord_4738250, baseEnd_4738250] using wordTrace_append hprefix tailTrace_4738250
  have hstable : (prefixWord ++ tailWord_4738250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738250).length < 2 ^ (prefixWord ++ tailWord_4738250).sum := by decide
  have hdescent : baseEnd_4738250 < baseStart_4738250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738303 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_4738303 : Nat := 118140960795 + 4738303 * 2 ^ 59
def prefixEnd_4738303 : Nat := 4983230072969 + 3 ^ 40 * 4738303 * 2
def baseEnd_4738303 : Nat := 2433026925640880101421447

theorem tailTrace_4738303 : CollatzResearch.WordTrace tailWord_4738303 prefixEnd_4738303 2433026925640880101421447 := by
  unfold tailWord_4738303
  simp only [CollatzResearch.WordTrace]
  refine ⟨172820108152944943570803563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115213405435296629047202375 172820108152944943570803563)
  ·
    refine ⟨259230162229417415356205345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172820108152944943570803563 259230162229417415356205345)
    ·
      refine ⟨194422621672063061517154009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259230162229417415356205345 194422621672063061517154009)
      ·
        refine ⟨145816966254047296137865507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194422621672063061517154009 145816966254047296137865507)
        ·
          refine ⟨218725449381070944206798261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145816966254047296137865507 218725449381070944206798261)
          ·
            refine ⟨20505510879475401019387337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218725449381070944206798261 20505510879475401019387337)
            ·
              refine ⟨15379133159606550764540503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20505510879475401019387337 15379133159606550764540503)
              ·
                refine ⟨23068699739409826146810755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15379133159606550764540503 23068699739409826146810755)
                ·
                  refine ⟨34603049609114739220216133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23068699739409826146810755 34603049609114739220216133)
                  ·
                    refine ⟨6488071801709013603790525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34603049609114739220216133 6488071801709013603790525)
                    ·
                      refine ⟨2433026925640880101421447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488071801709013603790525 2433026925640880101421447)
                      ·
                        rfl

theorem cell23_4738303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_4738303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738303 prefixEnd_4738303 := by exact prefixLift 4738303
  have htrace : WordTrace (prefixWord ++ tailWord_4738303) baseStart_4738303 baseEnd_4738303 := by
    simpa [prefixWord, tailWord_4738303, baseEnd_4738303] using wordTrace_append hprefix tailTrace_4738303
  have hstable : (prefixWord ++ tailWord_4738303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738303).length < 2 ^ (prefixWord ++ tailWord_4738303).sum := by decide
  have hdescent : baseEnd_4738303 < baseStart_4738303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738383 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 8, 4]
def baseStart_4738383 : Nat := 118140960795 + 4738383 * 2 ^ 59
def prefixEnd_4738383 : Nat := 4983230072969 + 3 ^ 40 * 4738383 * 2
def baseEnd_4738383 : Nat := 811022668031079929473693

theorem tailTrace_4738383 : CollatzResearch.WordTrace tailWord_4738383 prefixEnd_4738383 811022668031079929473693 := by
  unfold tailWord_4738383
  simp only [CollatzResearch.WordTrace]
  refine ⟨172823025992655117233715803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115215350661770078155810535 172823025992655117233715803)
  ·
    refine ⟨259234538988982675850573705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172823025992655117233715803 259234538988982675850573705)
    ·
      refine ⟨194425904241737006887930279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259234538988982675850573705 194425904241737006887930279)
      ·
        refine ⟨291638856362605510331895419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194425904241737006887930279 291638856362605510331895419)
        ·
          refine ⟨437458284543908265497843129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291638856362605510331895419 437458284543908265497843129)
          ·
            refine ⟨328093713407931199123382347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437458284543908265497843129 328093713407931199123382347)
            ·
              refine ⟨492140570111896798685073521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328093713407931199123382347 492140570111896798685073521)
              ·
                refine ⟨369105427583922599013805141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492140570111896798685073521 369105427583922599013805141)
                ·
                  refine ⟨4325454229499092957193029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 369105427583922599013805141 4325454229499092957193029)
                  ·
                    refine ⟨811022668031079929473693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325454229499092957193029 811022668031079929473693)
                    ·
                      rfl

theorem cell23_4738383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_4738383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738383 prefixEnd_4738383 := by exact prefixLift 4738383
  have htrace : WordTrace (prefixWord ++ tailWord_4738383) baseStart_4738383 baseEnd_4738383 := by
    simpa [prefixWord, tailWord_4738383, baseEnd_4738383] using wordTrace_append hprefix tailTrace_4738383
  have hstable : (prefixWord ++ tailWord_4738383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738383).length < 2 ^ (prefixWord ++ tailWord_4738383).sum := by decide
  have hdescent : baseEnd_4738383 < baseStart_4738383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738393 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_4738393 : Nat := 118140960795 + 4738393 * 2 ^ 59
def prefixEnd_4738393 : Nat := 4983230072969 + 3 ^ 40 * 4738393 * 2
def baseEnd_4738393 : Nat := 2433073138899784749296033

theorem tailTrace_4738393 : CollatzResearch.WordTrace tailWord_4738393 prefixEnd_4738393 2433073138899784749296033 := by
  unfold tailWord_4738393
  simp only [CollatzResearch.WordTrace]
  refine ⟨172823390722618888941579833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115215593815079259294386555 172823390722618888941579833)
  ·
    refine ⟨129617543041964166706184875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172823390722618888941579833 129617543041964166706184875)
    ·
      refine ⟨194426314562946250059277313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129617543041964166706184875 194426314562946250059277313)
      ·
        refine ⟨145819735922209687544457985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194426314562946250059277313 145819735922209687544457985)
        ·
          refine ⟨109364801941657265658343489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145819735922209687544457985 109364801941657265658343489)
          ·
            refine ⟨82023601456242949243757617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109364801941657265658343489 82023601456242949243757617)
            ·
              refine ⟨61517701092182211932818213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82023601456242949243757617 61517701092182211932818213)
              ·
                refine ⟨11534568954784164737403415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61517701092182211932818213 11534568954784164737403415)
                ·
                  refine ⟨17301853432176247106105123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11534568954784164737403415 17301853432176247106105123)
                  ·
                    refine ⟨25952780148264370659157685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17301853432176247106105123 25952780148264370659157685)
                    ·
                      refine ⟨2433073138899784749296033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25952780148264370659157685 2433073138899784749296033)
                      ·
                        rfl

theorem cell23_4738393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_4738393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738393 prefixEnd_4738393 := by exact prefixLift 4738393
  have htrace : WordTrace (prefixWord ++ tailWord_4738393) baseStart_4738393 baseEnd_4738393 := by
    simpa [prefixWord, tailWord_4738393, baseEnd_4738393] using wordTrace_append hprefix tailTrace_4738393
  have hstable : (prefixWord ++ tailWord_4738393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738393).length < 2 ^ (prefixWord ++ tailWord_4738393).sum := by decide
  have hdescent : baseEnd_4738393 < baseStart_4738393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738400 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 1, 6]
def baseStart_4738400 : Nat := 118140960795 + 4738400 * 2 ^ 59
def prefixEnd_4738400 : Nat := 4983230072969 + 3 ^ 40 * 4738400 * 2
def baseEnd_4738400 : Nat := 811025577754788740636167

theorem tailTrace_4738400 : CollatzResearch.WordTrace tailWord_4738400 prefixEnd_4738400 811025577754788740636167 := by
  unfold tailWord_4738400
  simp only [CollatzResearch.WordTrace]
  refine ⟨86411823016796764568542327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115215764022395686091389769 86411823016796764568542327)
  ·
    refine ⟨129617734525195146852813491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86411823016796764568542327 129617734525195146852813491)
    ·
      refine ⟨194426601787792720279220237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129617734525195146852813491 194426601787792720279220237)
      ·
        refine ⟨72909975670422270104707589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194426601787792720279220237 72909975670422270104707589)
        ·
          refine ⟨13670620438204175644632673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72909975670422270104707589 13670620438204175644632673)
          ·
            refine ⟨10252965328653131733474505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13670620438204175644632673 10252965328653131733474505)
            ·
              refine ⟨7689723996489848800105879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10252965328653131733474505 7689723996489848800105879)
              ·
                refine ⟨11534585994734773200158819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7689723996489848800105879 11534585994734773200158819)
                ·
                  refine ⟨17301878992102159800238229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11534585994734773200158819 17301878992102159800238229)
                  ·
                    refine ⟨811025577754788740636167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17301878992102159800238229 811025577754788740636167)
                    ·
                      rfl

theorem cell23_4738400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_4738400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738400 prefixEnd_4738400 := by exact prefixLift 4738400
  have htrace : WordTrace (prefixWord ++ tailWord_4738400) baseStart_4738400 baseEnd_4738400 := by
    simpa [prefixWord, tailWord_4738400, baseEnd_4738400] using wordTrace_append hprefix tailTrace_4738400
  have hstable : (prefixWord ++ tailWord_4738400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738400).length < 2 ^ (prefixWord ++ tailWord_4738400).sum := by decide
  have hdescent : baseEnd_4738400 < baseStart_4738400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738421 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_4738421 : Nat := 118140960795 + 4738421 * 2 ^ 59
def prefixEnd_4738421 : Nat := 4983230072969 + 3 ^ 40 * 4738421 * 2
def baseEnd_4738421 : Nat := 811029172119370213248635

theorem tailTrace_4738421 : CollatzResearch.WordTrace tailWord_4738421 prefixEnd_4738421 811029172119370213248635 := by
  unfold tailWord_4738421
  simp only [CollatzResearch.WordTrace]
  refine ⟨172824411966517449723599117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115216274644344966482399411 172824411966517449723599117)
  ·
    refine ⟨64809154487444043646349669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172824411966517449723599117 64809154487444043646349669)
    ·
      refine ⟨12151716466395758183690563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64809154487444043646349669 12151716466395758183690563)
      ·
        refine ⟨18227574699593637275535845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12151716466395758183690563 18227574699593637275535845)
        ·
          refine ⟨3417670256173806989162971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18227574699593637275535845 3417670256173806989162971)
          ·
            refine ⟨5126505384260710483744457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417670256173806989162971 5126505384260710483744457)
            ·
              refine ⟨3844879038195532862808343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126505384260710483744457 3844879038195532862808343)
              ·
                refine ⟨5767318557293299294212515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844879038195532862808343 5767318557293299294212515)
                ·
                  refine ⟨8650977835939948941318773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767318557293299294212515 8650977835939948941318773)
                  ·
                    refine ⟨811029172119370213248635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8650977835939948941318773 811029172119370213248635)
                    ·
                      rfl

theorem cell23_4738421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_4738421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738421 prefixEnd_4738421 := by exact prefixLift 4738421
  have htrace : WordTrace (prefixWord ++ tailWord_4738421) baseStart_4738421 baseEnd_4738421 := by
    simpa [prefixWord, tailWord_4738421, baseEnd_4738421] using wordTrace_append hprefix tailTrace_4738421
  have hstable : (prefixWord ++ tailWord_4738421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738421).length < 2 ^ (prefixWord ++ tailWord_4738421).sum := by decide
  have hdescent : baseEnd_4738421 < baseStart_4738421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738434 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4738434 : Nat := 118140960795 + 4738434 * 2 ^ 59
def prefixEnd_4738434 : Nat := 4983230072969 + 3 ^ 40 * 4738434 * 2
def baseEnd_4738434 : Nat := 811031397202206362961115

theorem tailTrace_4738434 : CollatzResearch.WordTrace tailWord_4738434 prefixEnd_4738434 811031397202206362961115 := by
  unfold tailWord_4738434
  simp only [CollatzResearch.WordTrace]
  refine ⟨43206221528867588235955589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115216590743646901962548237 43206221528867588235955589)
  ·
    refine ⟨8101166536662672794241673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43206221528867588235955589 8101166536662672794241673)
    ·
      refine ⟨6075874902497004595681255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101166536662672794241673 6075874902497004595681255)
      ·
        refine ⟨9113812353745506893521883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075874902497004595681255 9113812353745506893521883)
        ·
          refine ⟨13670718530618260340282825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9113812353745506893521883 13670718530618260340282825)
          ·
            refine ⟨10253038897963695255212119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13670718530618260340282825 10253038897963695255212119)
            ·
              refine ⟨15379558346945542882818179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10253038897963695255212119 15379558346945542882818179)
              ·
                refine ⟨23069337520418314324227269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15379558346945542882818179 23069337520418314324227269)
                ·
                  refine ⟨4325500785078433935792613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23069337520418314324227269 4325500785078433935792613)
                  ·
                    refine ⟨811031397202206362961115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325500785078433935792613 811031397202206362961115)
                    ·
                      rfl

theorem cell23_4738434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4738434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738434 prefixEnd_4738434 := by exact prefixLift 4738434
  have htrace : WordTrace (prefixWord ++ tailWord_4738434) baseStart_4738434 baseEnd_4738434 := by
    simpa [prefixWord, tailWord_4738434, baseEnd_4738434] using wordTrace_append hprefix tailTrace_4738434
  have hstable : (prefixWord ++ tailWord_4738434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738434).length < 2 ^ (prefixWord ++ tailWord_4738434).sum := by decide
  have hdescent : baseEnd_4738434 < baseStart_4738434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738457 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 3]
def baseStart_4738457 : Nat := 118140960795 + 4738457 * 2 ^ 59
def prefixEnd_4738457 : Nat := 4983230072969 + 3 ^ 40 * 4738457 * 2
def baseEnd_4738457 : Nat := 2433106001661672498895739

theorem tailTrace_4738457 : CollatzResearch.WordTrace tailWord_4738457 prefixEnd_4738457 2433106001661672498895739 := by
  unfold tailWord_4738457
  simp only [CollatzResearch.WordTrace]
  refine ⟨172825724994387027871909625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115217149996258018581273083 172825724994387027871909625)
  ·
    refine ⟨129619293745790270903932219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172825724994387027871909625 129619293745790270903932219)
    ·
      refine ⟨194428940618685406355898329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129619293745790270903932219 194428940618685406355898329)
      ·
        refine ⟨145821705464014054766923747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194428940618685406355898329 145821705464014054766923747)
        ·
          refine ⟨218732558196021082150385621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145821705464014054766923747 218732558196021082150385621)
          ·
            refine ⟨5126544332719244112899663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 218732558196021082150385621 5126544332719244112899663)
            ·
              refine ⟨7689816499078866169349495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126544332719244112899663 7689816499078866169349495)
              ·
                refine ⟨11534724748618299254024243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7689816499078866169349495 11534724748618299254024243)
                ·
                  refine ⟨17302087122927448881036365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11534724748618299254024243 17302087122927448881036365)
                  ·
                    refine ⟨6488282671097793330388637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17302087122927448881036365 6488282671097793330388637)
                    ·
                      refine ⟨2433106001661672498895739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488282671097793330388637 2433106001661672498895739)
                      ·
                        rfl

theorem cell23_4738457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_4738457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738457 prefixEnd_4738457 := by exact prefixLift 4738457
  have htrace : WordTrace (prefixWord ++ tailWord_4738457) baseStart_4738457 baseEnd_4738457 := by
    simpa [prefixWord, tailWord_4738457, baseEnd_4738457] using wordTrace_append hprefix tailTrace_4738457
  have hstable : (prefixWord ++ tailWord_4738457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738457).length < 2 ^ (prefixWord ++ tailWord_4738457).sum := by decide
  have hdescent : baseEnd_4738457 < baseStart_4738457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738510 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_4738510 : Nat := 118140960795 + 4738510 * 2 ^ 59
def prefixEnd_4738510 : Nat := 4983230072969 + 3 ^ 40 * 4738510 * 2
def baseEnd_4738510 : Nat := 2433133216136360791532995

theorem tailTrace_4738510 : CollatzResearch.WordTrace tailWord_4738510 prefixEnd_4738510 2433133216136360791532995 := by
  unfold tailWord_4738510
  simp only [CollatzResearch.WordTrace]
  refine ⟨21603457257899377240448623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115218438708796678615725989 21603457257899377240448623)
  ·
    refine ⟨32405185886849065860672935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21603457257899377240448623 32405185886849065860672935)
    ·
      refine ⟨48607778830273598791009403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32405185886849065860672935 48607778830273598791009403)
      ·
        refine ⟨72911668245410398186514105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48607778830273598791009403 72911668245410398186514105)
        ·
          refine ⟨54683751184057798639885579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72911668245410398186514105 54683751184057798639885579)
          ·
            refine ⟨82025626776086697959828369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54683751184057798639885579 82025626776086697959828369)
            ·
              refine ⟨61519220082065023469871277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82025626776086697959828369 61519220082065023469871277)
              ·
                refine ⟨23069707530774383801201729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61519220082065023469871277 23069707530774383801201729)
                ·
                  refine ⟨17302280648080787850901297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23069707530774383801201729 17302280648080787850901297)
                  ·
                    refine ⟨12976710486060590888175973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17302280648080787850901297 12976710486060590888175973)
                    ·
                      refine ⟨2433133216136360791532995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12976710486060590888175973 2433133216136360791532995)
                      ·
                        rfl

theorem cell23_4738510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_4738510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738510 prefixEnd_4738510 := by exact prefixLift 4738510
  have htrace : WordTrace (prefixWord ++ tailWord_4738510) baseStart_4738510 baseEnd_4738510 := by
    simpa [prefixWord, tailWord_4738510, baseEnd_4738510] using wordTrace_append hprefix tailTrace_4738510
  have hstable : (prefixWord ++ tailWord_4738510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738510).length < 2 ^ (prefixWord ++ tailWord_4738510).sum := by decide
  have hdescent : baseEnd_4738510 < baseStart_4738510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738518 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4738518 : Nat := 118140960795 + 4738518 * 2 ^ 59
def prefixEnd_4738518 : Nat := 4983230072969 + 3 ^ 40 * 4738518 * 2
def baseEnd_4738518 : Nat := 2433137323981596760232959

theorem tailTrace_4738518 : CollatzResearch.WordTrace tailWord_4738518 prefixEnd_4738518 2433137323981596760232959 := by
  unfold tailWord_4738518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801746865447877205617513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115218633231444023526586805 10801746865447877205617513)
  ·
    refine ⟨8101310149085907904213135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10801746865447877205617513 8101310149085907904213135)
    ·
      refine ⟨12151965223628861856319703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101310149085907904213135 12151965223628861856319703)
      ·
        refine ⟨18227947835443292784479555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12151965223628861856319703 18227947835443292784479555)
        ·
          refine ⟨27341921753164939176719333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18227947835443292784479555 27341921753164939176719333)
          ·
            refine ⟨5126610328718426095634875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27341921753164939176719333 5126610328718426095634875)
            ·
              refine ⟨7689915493077639143452313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126610328718426095634875 7689915493077639143452313)
              ·
                refine ⟨5767436619808229357589235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7689915493077639143452313 5767436619808229357589235)
                ·
                  refine ⟨8651154929712344036383853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767436619808229357589235 8651154929712344036383853)
                  ·
                    refine ⟨3244183098642129013643945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8651154929712344036383853 3244183098642129013643945)
                    ·
                      refine ⟨2433137323981596760232959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244183098642129013643945 2433137323981596760232959)
                      ·
                        rfl

theorem cell23_4738518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4738518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738518 prefixEnd_4738518 := by exact prefixLift 4738518
  have htrace : WordTrace (prefixWord ++ tailWord_4738518) baseStart_4738518 baseEnd_4738518 := by
    simpa [prefixWord, tailWord_4738518, baseEnd_4738518] using wordTrace_append hprefix tailTrace_4738518
  have hstable : (prefixWord ++ tailWord_4738518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738518).length < 2 ^ (prefixWord ++ tailWord_4738518).sum := by decide
  have hdescent : baseEnd_4738518 < baseStart_4738518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738557 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_4738557 : Nat := 118140960795 + 4738557 * 2 ^ 59
def prefixEnd_4738557 : Nat := 4983230072969 + 3 ^ 40 * 4738557 * 2
def baseEnd_4738557 : Nat := 2433157349727122107645279

theorem tailTrace_4738557 : CollatzResearch.WordTrace tailWord_4738557 prefixEnd_4738557 2433157349727122107645279 := by
  unfold tailWord_4738557
  simp only [CollatzResearch.WordTrace]
  refine ⟨172829372294024744950549925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115219581529349829967033283 172829372294024744950549925)
  ·
    refine ⟨32405507305129639678228111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172829372294024744950549925 32405507305129639678228111)
    ·
      refine ⟨48608260957694459517342167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32405507305129639678228111 48608260957694459517342167)
      ·
        refine ⟨72912391436541689276013251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48608260957694459517342167 72912391436541689276013251)
        ·
          refine ⟨109368587154812533914019877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72912391436541689276013251 109368587154812533914019877)
          ·
            refine ⟨20506610091527350108878727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109368587154812533914019877 20506610091527350108878727)
            ·
              refine ⟨30759915137291025163318091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20506610091527350108878727 30759915137291025163318091)
              ·
                refine ⟨46139872705936537744977137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30759915137291025163318091 46139872705936537744977137)
                ·
                  refine ⟨34604904529452403308732853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46139872705936537744977137 34604904529452403308732853)
                  ·
                    refine ⟨3244209799636162810193705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34604904529452403308732853 3244209799636162810193705)
                    ·
                      refine ⟨2433157349727122107645279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244209799636162810193705 2433157349727122107645279)
                      ·
                        rfl

theorem cell23_4738557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_4738557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738557 prefixEnd_4738557 := by exact prefixLift 4738557
  have htrace : WordTrace (prefixWord ++ tailWord_4738557) baseStart_4738557 baseEnd_4738557 := by
    simpa [prefixWord, tailWord_4738557, baseEnd_4738557] using wordTrace_append hprefix tailTrace_4738557
  have hstable : (prefixWord ++ tailWord_4738557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738557).length < 2 ^ (prefixWord ++ tailWord_4738557).sum := by decide
  have hdescent : baseEnd_4738557 < baseStart_4738557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738564 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4738564 : Nat := 118140960795 + 4738564 * 2 ^ 59
def prefixEnd_4738564 : Nat := 4983230072969 + 3 ^ 40 * 4738564 * 2
def baseEnd_4738564 : Nat := 2433160944091703580257747

theorem tailTrace_4738564 : CollatzResearch.WordTrace tailWord_4738564 prefixEnd_4738564 2433160944091703580257747 := by
  unfold tailWord_4738564
  simp only [CollatzResearch.WordTrace]
  refine ⟨86414813802499692573027373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115219751736666256764036497 86414813802499692573027373)
  ·
    refine ⟨32405555175937384714885265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86414813802499692573027373 32405555175937384714885265)
    ·
      refine ⟨24304166381953038536163949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32405555175937384714885265 24304166381953038536163949)
      ·
        refine ⟨9114062393232389451061481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24304166381953038536163949 9114062393232389451061481)
        ·
          refine ⟨6835546794924292088296111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9114062393232389451061481 6835546794924292088296111)
          ·
            refine ⟨10253320192386438132444167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6835546794924292088296111 10253320192386438132444167)
            ·
              refine ⟨15379980288579657198666251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10253320192386438132444167 15379980288579657198666251)
              ·
                refine ⟨23069970432869485797999377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15379980288579657198666251 23069970432869485797999377)
                ·
                  refine ⟨17302477824652114348499533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23069970432869485797999377 17302477824652114348499533)
                  ·
                    refine ⟨6488429184244542880687325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17302477824652114348499533 6488429184244542880687325)
                    ·
                      refine ⟨2433160944091703580257747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488429184244542880687325 2433160944091703580257747)
                      ·
                        rfl

theorem cell23_4738564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4738564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738564 prefixEnd_4738564 := by exact prefixLift 4738564
  have htrace : WordTrace (prefixWord ++ tailWord_4738564) baseStart_4738564 baseEnd_4738564 := by
    simpa [prefixWord, tailWord_4738564, baseEnd_4738564] using wordTrace_append hprefix tailTrace_4738564
  have hstable : (prefixWord ++ tailWord_4738564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738564).length < 2 ^ (prefixWord ++ tailWord_4738564).sum := by decide
  have hdescent : baseEnd_4738564 < baseStart_4738564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738584 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 2, 5]
def baseStart_4738584 : Nat := 118140960795 + 4738584 * 2 ^ 59
def prefixEnd_4738584 : Nat := 4983230072969 + 3 ^ 40 * 4738584 * 2
def baseEnd_4738584 : Nat := 811057071234931167335885

theorem tailTrace_4738584 : CollatzResearch.WordTrace tailWord_4738584 prefixEnd_4738584 811057071234931167335885 := by
  unfold tailWord_4738584
  simp only [CollatzResearch.WordTrace]
  refine ⟨86415178532463464280891403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115220238043284619041188537 86415178532463464280891403)
  ·
    refine ⟨129622767798695196421337105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86415178532463464280891403 129622767798695196421337105)
    ·
      refine ⟨97217075849021397316002829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129622767798695196421337105 97217075849021397316002829)
      ·
        refine ⟨36456403443383023993501061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97217075849021397316002829 36456403443383023993501061)
        ·
          refine ⟨6835575645634316998781449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36456403443383023993501061 6835575645634316998781449)
          ·
            refine ⟨5126681734225737749086087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6835575645634316998781449 5126681734225737749086087)
            ·
              refine ⟨7690022601338606623629131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126681734225737749086087 7690022601338606623629131)
              ·
                refine ⟨11535033902007909935443697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690022601338606623629131 11535033902007909935443697)
                ·
                  refine ⟨8651275426505932451582773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11535033902007909935443697 8651275426505932451582773)
                  ·
                    refine ⟨811057071234931167335885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8651275426505932451582773 811057071234931167335885)
                    ·
                      rfl

theorem cell23_4738584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_4738584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738584 prefixEnd_4738584 := by exact prefixLift 4738584
  have htrace : WordTrace (prefixWord ++ tailWord_4738584) baseStart_4738584 baseEnd_4738584 := by
    simpa [prefixWord, tailWord_4738584, baseEnd_4738584] using wordTrace_append hprefix tailTrace_4738584
  have hstable : (prefixWord ++ tailWord_4738584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738584).length < 2 ^ (prefixWord ++ tailWord_4738584).sum := by decide
  have hdescent : baseEnd_4738584 < baseStart_4738584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738657 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 1, 5]
def baseStart_4738657 : Nat := 118140960795 + 4738657 * 2 ^ 59
def prefixEnd_4738657 : Nat := 4983230072969 + 3 ^ 40 * 4738657 * 2
def baseEnd_4738657 : Nat := 811069565930857238798273

theorem tailTrace_4738657 : CollatzResearch.WordTrace tailWord_4738657 prefixEnd_4738657 811069565930857238798273 := by
  unfold tailWord_4738657
  simp only [CollatzResearch.WordTrace]
  refine ⟨172833019593662462029190225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115222013062441641352793483 172833019593662462029190225)
  ·
    refine ⟨129624764695246846521892669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172833019593662462029190225 129624764695246846521892669)
    ·
      refine ⟨48609286760717567445709751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129624764695246846521892669 48609286760717567445709751)
      ·
        refine ⟨72913930141076351168564627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48609286760717567445709751 72913930141076351168564627)
        ·
          refine ⟨109370895211614526752846941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72913930141076351168564627 109370895211614526752846941)
          ·
            refine ⟨41014085704355447532317603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109370895211614526752846941 41014085704355447532317603)
            ·
              refine ⟨61521128556533171298476405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41014085704355447532317603 61521128556533171298476405)
              ·
                refine ⟨5767605802174984809232163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61521128556533171298476405 5767605802174984809232163)
                ·
                  refine ⟨8651408703262477213848245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767605802174984809232163 8651408703262477213848245)
                  ·
                    refine ⟨811069565930857238798273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8651408703262477213848245 811069565930857238798273)
                    ·
                      rfl

theorem cell23_4738657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_4738657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738657 prefixEnd_4738657 := by exact prefixLift 4738657
  have htrace : WordTrace (prefixWord ++ tailWord_4738657) baseStart_4738657 baseEnd_4738657 := by
    simpa [prefixWord, tailWord_4738657, baseEnd_4738657] using wordTrace_append hprefix tailTrace_4738657
  have hstable : (prefixWord ++ tailWord_4738657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738657).length < 2 ^ (prefixWord ++ tailWord_4738657).sum := by decide
  have hdescent : baseEnd_4738657 < baseStart_4738657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738700 : List Nat := [2, 2, 1, 2, 1, 1, 3, 11]
def baseStart_4738700 : Nat := 118140960795 + 4738700 * 2 ^ 59
def prefixEnd_4738700 : Nat := 4983230072969 + 3 ^ 40 * 4738700 * 2
def baseEnd_4738700 : Nat := 90119658424470927709523

theorem tailTrace_4738700 : CollatzResearch.WordTrace tailWord_4738700 prefixEnd_4738700 90119658424470927709523 := by
  unfold tailWord_4738700
  simp only [CollatzResearch.WordTrace]
  refine ⟨86417293966253340186502777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115223058621671120248670369 86417293966253340186502777)
  ·
    refine ⟨64812970474690005139877083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86417293966253340186502777 64812970474690005139877083)
    ·
      refine ⟨97219455712035007709815625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64812970474690005139877083 97219455712035007709815625)
      ·
        refine ⟨72914591784026255782361719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97219455712035007709815625 72914591784026255782361719)
        ·
          refine ⟨109371887676039383673542579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72914591784026255782361719 109371887676039383673542579)
          ·
            refine ⟨164057831514059075510313869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109371887676039383673542579 164057831514059075510313869)
            ·
              refine ⟨61521686817772153316367701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164057831514059075510313869 61521686817772153316367701)
              ·
                refine ⟨90119658424470927709523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61521686817772153316367701 90119658424470927709523)
                ·
                  rfl

theorem cell23_4738700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 11].length) (baseStart_4738700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738700 prefixEnd_4738700 := by exact prefixLift 4738700
  have htrace : WordTrace (prefixWord ++ tailWord_4738700) baseStart_4738700 baseEnd_4738700 := by
    simpa [prefixWord, tailWord_4738700, baseEnd_4738700] using wordTrace_append hprefix tailTrace_4738700
  have hstable : (prefixWord ++ tailWord_4738700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738700).length < 2 ^ (prefixWord ++ tailWord_4738700).sum := by decide
  have hdescent : baseEnd_4738700 < baseStart_4738700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738708 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_4738708 : Nat := 118140960795 + 4738708 * 2 ^ 59
def prefixEnd_4738708 : Nat := 4983230072969 + 3 ^ 40 * 4738708 * 2
def baseEnd_4738708 : Nat := 811078295101983672285695

theorem tailTrace_4738708 : CollatzResearch.WordTrace tailWord_4738708 prefixEnd_4738708 811078295101983672285695 := by
  unfold tailWord_4738708
  simp only [CollatzResearch.WordTrace]
  refine ⟨86417439858238848869648389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115223253144318465159531185 86417439858238848869648389)
  ·
    refine ⟨16203269973419784163059073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86417439858238848869648389 16203269973419784163059073)
    ·
      refine ⟨12152452480064838122294305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16203269973419784163059073 12152452480064838122294305)
      ·
        refine ⟨9114339360048628591720729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12152452480064838122294305 9114339360048628591720729)
        ·
          refine ⟨6835754520036471443790547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9114339360048628591720729 6835754520036471443790547)
          ·
            refine ⟨10253631780054707165685821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6835754520036471443790547 10253631780054707165685821)
            ·
              refine ⟨3845111917520515187132183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10253631780054707165685821 3845111917520515187132183)
              ·
                refine ⟨5767667876280772780698275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845111917520515187132183 5767667876280772780698275)
                ·
                  refine ⟨8651501814421159171047413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767667876280772780698275 8651501814421159171047413)
                  ·
                    refine ⟨811078295101983672285695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8651501814421159171047413 811078295101983672285695)
                    ·
                      rfl

theorem cell23_4738708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_4738708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738708 prefixEnd_4738708 := by exact prefixLift 4738708
  have htrace : WordTrace (prefixWord ++ tailWord_4738708) baseStart_4738708 baseEnd_4738708 := by
    simpa [prefixWord, tailWord_4738708, baseEnd_4738708] using wordTrace_append hprefix tailTrace_4738708
  have hstable : (prefixWord ++ tailWord_4738708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738708).length < 2 ^ (prefixWord ++ tailWord_4738708).sum := by decide
  have hdescent : baseEnd_4738708 < baseStart_4738708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738711 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 1, 1, 4]
def baseStart_4738711 : Nat := 118140960795 + 4738711 * 2 ^ 59
def prefixEnd_4738711 : Nat := 4983230072969 + 3 ^ 40 * 4738711 * 2
def baseEnd_4738711 : Nat := 2433236425747914505119571

theorem tailTrace_4738711 : CollatzResearch.WordTrace tailWord_4738711 prefixEnd_4738711 2433236425747914505119571 := by
  unfold tailWord_4738711
  simp only [CollatzResearch.WordTrace]
  refine ⟨172834989135466829251655987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115223326090311219501103991 172834989135466829251655987)
  ·
    refine ⟨259252483703200243877483981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172834989135466829251655987 259252483703200243877483981)
    ·
      refine ⟨97219681388700091454056493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259252483703200243877483981 97219681388700091454056493)
      ·
        refine ⟨36457380520762534295271185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97219681388700091454056493 36457380520762534295271185)
        ·
          refine ⟨27343035390571900721453389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36457380520762534295271185 27343035390571900721453389)
          ·
            refine ⟨10253638271464462770545021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27343035390571900721453389 10253638271464462770545021)
            ·
              refine ⟨3845114351799173538954383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10253638271464462770545021 3845114351799173538954383)
              ·
                refine ⟨5767671527698760308431575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845114351799173538954383 5767671527698760308431575)
                ·
                  refine ⟨8651507291548140462647363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767671527698760308431575 8651507291548140462647363)
                  ·
                    refine ⟨12977260937322210693971045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8651507291548140462647363 12977260937322210693971045)
                    ·
                      refine ⟨2433236425747914505119571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12977260937322210693971045 2433236425747914505119571)
                      ·
                        rfl

theorem cell23_4738711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_4738711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738711 prefixEnd_4738711 := by exact prefixLift 4738711
  have htrace : WordTrace (prefixWord ++ tailWord_4738711) baseStart_4738711 baseEnd_4738711 := by
    simpa [prefixWord, tailWord_4738711, baseEnd_4738711] using wordTrace_append hprefix tailTrace_4738711
  have hstable : (prefixWord ++ tailWord_4738711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738711).length < 2 ^ (prefixWord ++ tailWord_4738711).sum := by decide
  have hdescent : baseEnd_4738711 < baseStart_4738711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738721 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 2, 4]
def baseStart_4738721 : Nat := 118140960795 + 4738721 * 2 ^ 59
def prefixEnd_4738721 : Nat := 4983230072969 + 3 ^ 40 * 4738721 * 2
def baseEnd_4738721 : Nat := 811080520184819821998175

theorem tailTrace_4738721 : CollatzResearch.WordTrace tailWord_4738721 prefixEnd_4738721 811080520184819821998175 := by
  unfold tailWord_4738721
  simp only [CollatzResearch.WordTrace]
  refine ⟨172835353865430600959520017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115223569243620400639680011 172835353865430600959520017)
  ·
    refine ⟨129626515399072950719640013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172835353865430600959520017 129626515399072950719640013)
    ·
      refine ⟨48609943274652356519865005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129626515399072950719640013 48609943274652356519865005)
      ·
        refine ⟨18228728727994633694949377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48609943274652356519865005 18228728727994633694949377)
        ·
          refine ⟨13671546545995975271212033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18228728727994633694949377 13671546545995975271212033)
          ·
            refine ⟨10253659909496981453409025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13671546545995975271212033 10253659909496981453409025)
            ·
              refine ⟨7690244932122736090056769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10253659909496981453409025 7690244932122736090056769)
              ·
                refine ⟨5767683699092052067542577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7690244932122736090056769 5767683699092052067542577)
                ·
                  refine ⟨4325762774319039050656933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5767683699092052067542577 4325762774319039050656933)
                  ·
                    refine ⟨811080520184819821998175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325762774319039050656933 811080520184819821998175)
                    ·
                      rfl

theorem cell23_4738721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_4738721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738721 prefixEnd_4738721 := by exact prefixLift 4738721
  have htrace : WordTrace (prefixWord ++ tailWord_4738721) baseStart_4738721 baseEnd_4738721 := by
    simpa [prefixWord, tailWord_4738721, baseEnd_4738721] using wordTrace_append hprefix tailTrace_4738721
  have hstable : (prefixWord ++ tailWord_4738721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738721).length < 2 ^ (prefixWord ++ tailWord_4738721).sum := by decide
  have hdescent : baseEnd_4738721 < baseStart_4738721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738741 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_4738741 : Nat := 118140960795 + 4738741 * 2 ^ 59
def prefixEnd_4738741 : Nat := 4983230072969 + 3 ^ 40 * 4738741 * 2
def baseEnd_4738741 : Nat := 2433251830167549387744433

theorem tailTrace_4738741 : CollatzResearch.WordTrace tailWord_4738741 prefixEnd_4738741 2433251830167549387744433 := by
  unfold tailWord_4738741
  simp only [CollatzResearch.WordTrace]
  refine ⟨172836083325358144375248077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115224055550238762916832051 172836083325358144375248077)
  ·
    refine ⟨64813531247009304140718029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172836083325358144375248077 64813531247009304140718029)
    ·
      refine ⟨24305074217628489052769261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64813531247009304140718029 24305074217628489052769261)
      ·
        refine ⟨9114402831610683394788473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24305074217628489052769261 9114402831610683394788473)
        ·
          refine ⟨6835802123708012546091355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9114402831610683394788473 6835802123708012546091355)
          ·
            refine ⟨10253703185562018819137033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6835802123708012546091355 10253703185562018819137033)
            ·
              refine ⟨7690277389171514114352775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10253703185562018819137033 7690277389171514114352775)
              ·
                refine ⟨11535416083757271171529163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690277389171514114352775 11535416083757271171529163)
                ·
                  refine ⟨17303124125635906757293745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11535416083757271171529163 17303124125635906757293745)
                  ·
                    refine ⟨12977343094226930067970309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17303124125635906757293745 12977343094226930067970309)
                    ·
                      refine ⟨2433251830167549387744433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12977343094226930067970309 2433251830167549387744433)
                      ·
                        rfl

theorem cell23_4738741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_4738741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738741 prefixEnd_4738741 := by exact prefixLift 4738741
  have htrace : WordTrace (prefixWord ++ tailWord_4738741) baseStart_4738741 baseEnd_4738741 := by
    simpa [prefixWord, tailWord_4738741, baseEnd_4738741] using wordTrace_append hprefix tailTrace_4738741
  have hstable : (prefixWord ++ tailWord_4738741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738741).length < 2 ^ (prefixWord ++ tailWord_4738741).sum := by decide
  have hdescent : baseEnd_4738741 < baseStart_4738741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738758 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4738758 : Nat := 118140960795 + 4738758 * 2 ^ 59
def prefixEnd_4738758 : Nat := 4983230072969 + 3 ^ 40 * 4738758 * 2
def baseEnd_4738758 : Nat := 2433260559338675821231855

theorem tailTrace_4738758 : CollatzResearch.WordTrace tailWord_4738758 prefixEnd_4738758 2433260559338675821231855 := by
  unfold tailWord_4738758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401146980196767383706779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115224468910864370852411285 5401146980196767383706779)
  ·
    refine ⟨8101720470295151075560169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5401146980196767383706779 8101720470295151075560169)
    ·
      refine ⟨6076290352721363306670127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101720470295151075560169 6076290352721363306670127)
      ·
        refine ⟨9114435529082044960005191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076290352721363306670127 9114435529082044960005191)
        ·
          refine ⟨13671653293623067440007787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9114435529082044960005191 13671653293623067440007787)
          ·
            refine ⟨20507479940434601160011681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13671653293623067440007787 20507479940434601160011681)
            ·
              refine ⟨15380609955325950870008761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20507479940434601160011681 15380609955325950870008761)
              ·
                refine ⟨11535457466494463152506571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15380609955325950870008761 11535457466494463152506571)
                ·
                  refine ⟨17303186199741694728759857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11535457466494463152506571 17303186199741694728759857)
                  ·
                    refine ⟨12977389649806271046569893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17303186199741694728759857 12977389649806271046569893)
                    ·
                      refine ⟨2433260559338675821231855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12977389649806271046569893 2433260559338675821231855)
                      ·
                        rfl

theorem cell23_4738758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4738758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738758 prefixEnd_4738758 := by exact prefixLift 4738758
  have htrace : WordTrace (prefixWord ++ tailWord_4738758) baseStart_4738758 baseEnd_4738758 := by
    simpa [prefixWord, tailWord_4738758, baseEnd_4738758] using wordTrace_append hprefix tailTrace_4738758
  have hstable : (prefixWord ++ tailWord_4738758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738758).length < 2 ^ (prefixWord ++ tailWord_4738758).sum := by decide
  have hdescent : baseEnd_4738758 < baseStart_4738758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738765 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4738765 : Nat := 118140960795 + 4738765 * 2 ^ 59
def prefixEnd_4738765 : Nat := 4983230072969 + 3 ^ 40 * 4738765 * 2
def baseEnd_4738765 : Nat := 2433264153703257293844323

theorem tailTrace_4738765 : CollatzResearch.WordTrace tailWord_4738765 prefixEnd_4738765 2433264153703257293844323 := by
  unfold tailWord_4738765
  simp only [CollatzResearch.WordTrace]
  refine ⟨172836958677271196474121749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115224639118180797649414499 172836958677271196474121749)
  ·
    refine ⟨8101732437997087334724457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172836958677271196474121749 8101732437997087334724457)
    ·
      refine ⟨6076299328497815501043343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101732437997087334724457 6076299328497815501043343)
      ·
        refine ⟨9114448992746723251565015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076299328497815501043343 9114448992746723251565015)
        ·
          refine ⟨13671673489120084877347523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9114448992746723251565015 13671673489120084877347523)
          ·
            refine ⟨20507510233680127316021285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13671673489120084877347523 20507510233680127316021285)
            ·
              refine ⟨3845158168815023871753991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20507510233680127316021285 3845158168815023871753991)
              ·
                refine ⟨5767737253222535807630987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845158168815023871753991 5767737253222535807630987)
                ·
                  refine ⟨8651605879833803711446481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767737253222535807630987 8651605879833803711446481)
                  ·
                    refine ⟨6488704409875352783584861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8651605879833803711446481 6488704409875352783584861)
                    ·
                      refine ⟨2433264153703257293844323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488704409875352783584861 2433264153703257293844323)
                      ·
                        rfl

theorem cell23_4738765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4738765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738765 prefixEnd_4738765 := by exact prefixLift 4738765
  have htrace : WordTrace (prefixWord ++ tailWord_4738765) baseStart_4738765 baseEnd_4738765 := by
    simpa [prefixWord, tailWord_4738765, baseEnd_4738765] using wordTrace_append hprefix tailTrace_4738765
  have hstable : (prefixWord ++ tailWord_4738765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738765).length < 2 ^ (prefixWord ++ tailWord_4738765).sum := by decide
  have hdescent : baseEnd_4738765 < baseStart_4738765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738777 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_4738777 : Nat := 118140960795 + 4738777 * 2 ^ 59
def prefixEnd_4738777 : Nat := 4983230072969 + 3 ^ 40 * 4738777 * 2
def baseEnd_4738777 : Nat := 811090105157037082298089

theorem tailTrace_4738777 : CollatzResearch.WordTrace tailWord_4738777 prefixEnd_4738777 811090105157037082298089 := by
  unfold tailWord_4738777
  simp only [CollatzResearch.WordTrace]
  refine ⟨172837396353227722523558585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115224930902151815015705723 172837396353227722523558585)
  ·
    refine ⟨129628047264920791892668939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172837396353227722523558585 129628047264920791892668939)
    ·
      refine ⟨194442070897381187839003409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129628047264920791892668939 194442070897381187839003409)
      ·
        refine ⟨145831553173035890879252557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194442070897381187839003409 145831553173035890879252557)
        ·
          refine ⟨54686832439888459079719709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145831553173035890879252557 54686832439888459079719709)
          ·
            refine ⟨20507562164958172154894891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54686832439888459079719709 20507562164958172154894891)
            ·
              refine ⟨30761343247437258232342337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20507562164958172154894891 30761343247437258232342337)
              ·
                refine ⟨23071007435577943674256753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30761343247437258232342337 23071007435577943674256753)
                ·
                  refine ⟨17303255576683457755692565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23071007435577943674256753 17303255576683457755692565)
                  ·
                    refine ⟨811090105157037082298089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17303255576683457755692565 811090105157037082298089)
                    ·
                      rfl

theorem cell23_4738777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_4738777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738777 prefixEnd_4738777 := by exact prefixLift 4738777
  have htrace : WordTrace (prefixWord ++ tailWord_4738777) baseStart_4738777 baseEnd_4738777 := by
    simpa [prefixWord, tailWord_4738777, baseEnd_4738777] using wordTrace_append hprefix tailTrace_4738777
  have hstable : (prefixWord ++ tailWord_4738777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738777).length < 2 ^ (prefixWord ++ tailWord_4738777).sum := by decide
  have hdescent : baseEnd_4738777 < baseStart_4738777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738778 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_4738778 : Nat := 118140960795 + 4738778 * 2 ^ 59
def prefixEnd_4738778 : Nat := 4983230072969 + 3 ^ 40 * 4738778 * 2
def baseEnd_4738778 : Nat := 2433270828951765742981763

theorem tailTrace_4738778 : CollatzResearch.WordTrace tailWord_4738778 prefixEnd_4738778 2433270828951765742981763 := by
  unfold tailWord_4738778
  simp only [CollatzResearch.WordTrace]
  refine ⟨43209358206556024923586247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115224955217482733129563325 43209358206556024923586247)
  ·
    refine ⟨64814037309834037385379371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43209358206556024923586247 64814037309834037385379371)
    ·
      refine ⟨97221055964751056078069057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64814037309834037385379371 97221055964751056078069057)
      ·
        refine ⟨72915791973563292058551793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97221055964751056078069057 72915791973563292058551793)
        ·
          refine ⟨54686843980172469043913845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72915791973563292058551793 54686843980172469043913845)
          ·
            refine ⟨5126891623141168972866923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54686843980172469043913845 5126891623141168972866923)
            ·
              refine ⟨7690337434711753459300385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126891623141168972866923 7690337434711753459300385)
              ·
                refine ⟨5767753076033815094475289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7690337434711753459300385 5767753076033815094475289)
                ·
                  refine ⟨4325814807025361320856467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5767753076033815094475289 4325814807025361320856467)
                  ·
                    refine ⟨6488722210538041981284701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4325814807025361320856467 6488722210538041981284701)
                    ·
                      refine ⟨2433270828951765742981763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488722210538041981284701 2433270828951765742981763)
                      ·
                        rfl

theorem cell23_4738778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_4738778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738778 prefixEnd_4738778 := by exact prefixLift 4738778
  have htrace : WordTrace (prefixWord ++ tailWord_4738778) baseStart_4738778 baseEnd_4738778 := by
    simpa [prefixWord, tailWord_4738778, baseEnd_4738778] using wordTrace_append hprefix tailTrace_4738778
  have hstable : (prefixWord ++ tailWord_4738778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738778).length < 2 ^ (prefixWord ++ tailWord_4738778).sum := by decide
  have hdescent : baseEnd_4738778 < baseStart_4738778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738784 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 3, 4, 2]
def baseStart_4738784 : Nat := 118140960795 + 4738784 * 2 ^ 59
def prefixEnd_4738784 : Nat := 4983230072969 + 3 ^ 40 * 4738784 * 2
def baseEnd_4738784 : Nat := 2433273909835692719506735

theorem tailTrace_4738784 : CollatzResearch.WordTrace tailWord_4738784 prefixEnd_4738784 2433273909835692719506735 := by
  unfold tailWord_4738784
  simp only [CollatzResearch.WordTrace]
  refine ⟨86418825832101181359531703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115225101109468241812708937 86418825832101181359531703)
  ·
    refine ⟨129628238748151772039297555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86418825832101181359531703 129628238748151772039297555)
    ·
      refine ⟨194442358122227658058946333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129628238748151772039297555 194442358122227658058946333)
      ·
        refine ⟨72915884295835371772104875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194442358122227658058946333 72915884295835371772104875)
        ·
          refine ⟨109373826443753057658157313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72915884295835371772104875 109373826443753057658157313)
          ·
            refine ⟨82030369832814793243617985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109373826443753057658157313 82030369832814793243617985)
            ·
              refine ⟨61522777374611094932713489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82030369832814793243617985 61522777374611094932713489)
              ·
                refine ⟨46142083030958321199535117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61522777374611094932713489 46142083030958321199535117)
                ·
                  refine ⟨17303281136609370449825669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46142083030958321199535117 17303281136609370449825669)
                  ·
                    refine ⟨3244365213114256959342313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17303281136609370449825669 3244365213114256959342313)
                    ·
                      refine ⟨2433273909835692719506735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244365213114256959342313 2433273909835692719506735)
                      ·
                        rfl

theorem cell23_4738784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_4738784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738784 prefixEnd_4738784 := by exact prefixLift 4738784
  have htrace : WordTrace (prefixWord ++ tailWord_4738784) baseStart_4738784 baseEnd_4738784 := by
    simpa [prefixWord, tailWord_4738784, baseEnd_4738784] using wordTrace_append hprefix tailTrace_4738784
  have hstable : (prefixWord ++ tailWord_4738784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738784).length < 2 ^ (prefixWord ++ tailWord_4738784).sum := by decide
  have hdescent : baseEnd_4738784 < baseStart_4738784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738801 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 1, 4, 2]
def baseStart_4738801 : Nat := 118140960795 + 4738801 * 2 ^ 59
def prefixEnd_4738801 : Nat := 4983230072969 + 3 ^ 40 * 4738801 * 2
def baseEnd_4738801 : Nat := 2433282639006819152994157

theorem tailTrace_4738801 : CollatzResearch.WordTrace tailWord_4738801 prefixEnd_4738801 2433282639006819152994157 := by
  unfold tailWord_4738801
  simp only [CollatzResearch.WordTrace]
  refine ⟨172838271705140774622432257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115225514470093849748288171 172838271705140774622432257)
  ·
    refine ⟨129628703778855580966824193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172838271705140774622432257 129628703778855580966824193)
    ·
      refine ⟨97221527834141685725118145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129628703778855580966824193 97221527834141685725118145)
      ·
        refine ⟨72916145875606264293838609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97221527834141685725118145 72916145875606264293838609)
        ·
          refine ⟨54687109406704698220378957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72916145875606264293838609 54687109406704698220378957)
          ·
            refine ⟨20507666027514261832642109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54687109406704698220378957 20507666027514261832642109)
            ·
              refine ⟨7690374760317848187240791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20507666027514261832642109 7690374760317848187240791)
              ·
                refine ⟨11535562140476772280861187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690374760317848187240791 11535562140476772280861187)
                ·
                  refine ⟨17303343210715158421291781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11535562140476772280861187 17303343210715158421291781)
                  ·
                    refine ⟨3244376852009092203992209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17303343210715158421291781 3244376852009092203992209)
                    ·
                      refine ⟨2433282639006819152994157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244376852009092203992209 2433282639006819152994157)
                      ·
                        rfl

theorem cell23_4738801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_4738801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738801 prefixEnd_4738801 := by exact prefixLift 4738801
  have htrace : WordTrace (prefixWord ++ tailWord_4738801) baseStart_4738801 baseEnd_4738801 := by
    simpa [prefixWord, tailWord_4738801, baseEnd_4738801] using wordTrace_append hprefix tailTrace_4738801
  have hstable : (prefixWord ++ tailWord_4738801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738801).length < 2 ^ (prefixWord ++ tailWord_4738801).sum := by decide
  have hdescent : baseEnd_4738801 < baseStart_4738801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738807 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 7]
def baseStart_4738807 : Nat := 118140960795 + 4738807 * 2 ^ 59
def prefixEnd_4738807 : Nat := 4983230072969 + 3 ^ 40 * 4738807 * 2
def baseEnd_4738807 : Nat := 270365079987860681057681

theorem tailTrace_4738807 : CollatzResearch.WordTrace tailWord_4738807 prefixEnd_4738807 270365079987860681057681 := by
  unfold tailWord_4738807
  simp only [CollatzResearch.WordTrace]
  refine ⟨172838490543119037647150675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115225660362079358431433783 172838490543119037647150675)
  ·
    refine ⟨259257735814678556470726013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172838490543119037647150675 259257735814678556470726013)
    ·
      refine ⟨97221650930504458676522255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259257735814678556470726013 97221650930504458676522255)
      ·
        refine ⟨145832476395756688014783383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97221650930504458676522255 145832476395756688014783383)
        ·
          refine ⟨218748714593635032022175075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145832476395756688014783383 218748714593635032022175075)
          ·
            refine ⟨328123071890452548033262613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218748714593635032022175075 328123071890452548033262613)
            ·
              refine ⟨15380768994864963189059185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 328123071890452548033262613 15380768994864963189059185)
              ·
                refine ⟨11535576746148722391794389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15380768994864963189059185 11535576746148722391794389)
                ·
                  refine ⟨270365079987860681057681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11535576746148722391794389 270365079987860681057681)
                  ·
                    rfl

theorem cell23_4738807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 7].length) (baseStart_4738807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738807 prefixEnd_4738807 := by exact prefixLift 4738807
  have htrace : WordTrace (prefixWord ++ tailWord_4738807) baseStart_4738807 baseEnd_4738807 := by
    simpa [prefixWord, tailWord_4738807, baseEnd_4738807] using wordTrace_append hprefix tailTrace_4738807
  have hstable : (prefixWord ++ tailWord_4738807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738807).length < 2 ^ (prefixWord ++ tailWord_4738807).sum := by decide
  have hdescent : baseEnd_4738807 < baseStart_4738807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738818 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_4738818 : Nat := 118140960795 + 4738818 * 2 ^ 59
def prefixEnd_4738818 : Nat := 4983230072969 + 3 ^ 40 * 4738818 * 2
def baseEnd_4738818 : Nat := 2433291368177945586481579

theorem tailTrace_4738818 : CollatzResearch.WordTrace tailWord_4738818 prefixEnd_4738818 2433291368177945586481579 := by
  unfold tailWord_4738818
  simp only [CollatzResearch.WordTrace]
  refine ⟨43209722936519796631450277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115225927830719457683867405 43209722936519796631450277)
  ·
    refine ⟨8101823050597461868396927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43209722936519796631450277 8101823050597461868396927)
    ·
      refine ⟨12152734575896192802595391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101823050597461868396927 12152734575896192802595391)
      ·
        refine ⟨18229101863844289203893087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12152734575896192802595391 18229101863844289203893087)
        ·
          refine ⟨27343652795766433805839631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18229101863844289203893087 27343652795766433805839631)
          ·
            refine ⟨41015479193649650708759447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27343652795766433805839631 41015479193649650708759447)
            ·
              refine ⟨61523218790474476063139171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41015479193649650708759447 61523218790474476063139171)
              ·
                refine ⟨92284828185711714094708757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61523218790474476063139171 92284828185711714094708757)
                ·
                  refine ⟨4325851321205236598189473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92284828185711714094708757 4325851321205236598189473)
                  ·
                    refine ⟨3244388490903927448642105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4325851321205236598189473 3244388490903927448642105)
                    ·
                      refine ⟨2433291368177945586481579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244388490903927448642105 2433291368177945586481579)
                      ·
                        rfl

theorem cell23_4738818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_4738818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738818 prefixEnd_4738818 := by exact prefixLift 4738818
  have htrace : WordTrace (prefixWord ++ tailWord_4738818) baseStart_4738818 baseEnd_4738818 := by
    simpa [prefixWord, tailWord_4738818, baseEnd_4738818] using wordTrace_append hprefix tailTrace_4738818
  have hstable : (prefixWord ++ tailWord_4738818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738818).length < 2 ^ (prefixWord ++ tailWord_4738818).sum := by decide
  have hdescent : baseEnd_4738818 < baseStart_4738818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738846 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4738846 : Nat := 118140960795 + 4738846 * 2 ^ 59
def prefixEnd_4738846 : Nat := 4983230072969 + 3 ^ 40 * 4738846 * 2
def baseEnd_4738846 : Nat := 2433305745636271476931451

theorem tailTrace_4738846 : CollatzResearch.WordTrace tailWord_4738846 prefixEnd_4738846 2433305745636271476931451 := by
  unfold tailWord_4738846
  simp only [CollatzResearch.WordTrace]
  refine ⟨21604989123747218413477549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115226608659985164871880261 21604989123747218413477549)
  ·
    refine ⟨8101870921405206905054081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21604989123747218413477549 8101870921405206905054081)
    ·
      refine ⟨6076403191053905178790561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101870921405206905054081 6076403191053905178790561)
      ·
        refine ⟨4557302393290428884092921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6076403191053905178790561 4557302393290428884092921)
        ·
          refine ⟨3417976794967821663069691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557302393290428884092921 3417976794967821663069691)
          ·
            refine ⟨5126965192451732494604537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417976794967821663069691 5126965192451732494604537)
            ·
              refine ⟨3845223894338799370953403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126965192451732494604537 3845223894338799370953403)
              ·
                refine ⟨5767835841508199056430105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845223894338799370953403 5767835841508199056430105)
                ·
                  refine ⟨4325876881131149292322579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5767835841508199056430105 4325876881131149292322579)
                  ·
                    refine ⟨6488815321696723938483869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4325876881131149292322579 6488815321696723938483869)
                    ·
                      refine ⟨2433305745636271476931451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488815321696723938483869 2433305745636271476931451)
                      ·
                        rfl

theorem cell23_4738846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4738846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738846 prefixEnd_4738846 := by exact prefixLift 4738846
  have htrace : WordTrace (prefixWord ++ tailWord_4738846) baseStart_4738846 baseEnd_4738846 := by
    simpa [prefixWord, tailWord_4738846, baseEnd_4738846] using wordTrace_append hprefix tailTrace_4738846
  have hstable : (prefixWord ++ tailWord_4738846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738846).length < 2 ^ (prefixWord ++ tailWord_4738846).sum := by decide
  have hdescent : baseEnd_4738846 < baseStart_4738846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738852 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_4738852 : Nat := 118140960795 + 4738852 * 2 ^ 59
def prefixEnd_4738852 : Nat := 4983230072969 + 3 ^ 40 * 4738852 * 2
def baseEnd_4738852 : Nat := 2433308826520198453456423

theorem tailTrace_4738852 : CollatzResearch.WordTrace tailWord_4738852 prefixEnd_4738852 2433308826520198453456423 := by
  unfold tailWord_4738852
  simp only [CollatzResearch.WordTrace]
  refine ⟨86420065913978005166269405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115226754551970673555025873 86420065913978005166269405)
  ·
    refine ⟨32407524717741751937351027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86420065913978005166269405 32407524717741751937351027)
    ·
      refine ⟨48611287076612627906026541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32407524717741751937351027 48611287076612627906026541)
      ·
        refine ⟨18229232653729735464759953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48611287076612627906026541 18229232653729735464759953)
        ·
          refine ⟨13671924490297301598569965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18229232653729735464759953 13671924490297301598569965)
          ·
            refine ⟨5126971683861488099463737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13671924490297301598569965 5126971683861488099463737)
            ·
              refine ⟨3845228762896116074597803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126971683861488099463737 3845228762896116074597803)
              ·
                refine ⟨5767843144344174111896705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845228762896116074597803 5767843144344174111896705)
                ·
                  refine ⟨4325882358258130583922529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5767843144344174111896705 4325882358258130583922529)
                  ·
                    refine ⟨3244411768693597937941897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4325882358258130583922529 3244411768693597937941897)
                    ·
                      refine ⟨2433308826520198453456423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244411768693597937941897 2433308826520198453456423)
                      ·
                        rfl

theorem cell23_4738852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_4738852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738852 prefixEnd_4738852 := by exact prefixLift 4738852
  have htrace : WordTrace (prefixWord ++ tailWord_4738852) baseStart_4738852 baseEnd_4738852 := by
    simpa [prefixWord, tailWord_4738852, baseEnd_4738852] using wordTrace_append hprefix tailTrace_4738852
  have hstable : (prefixWord ++ tailWord_4738852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738852).length < 2 ^ (prefixWord ++ tailWord_4738852).sum := by decide
  have hdescent : baseEnd_4738852 < baseStart_4738852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738894 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_4738894 : Nat := 118140960795 + 4738894 * 2 ^ 59
def prefixEnd_4738894 : Nat := 4983230072969 + 3 ^ 40 * 4738894 * 2
def baseEnd_4738894 : Nat := 2433330392707687289131229

theorem tailTrace_4738894 : CollatzResearch.WordTrace tailWord_4738894 prefixEnd_4738894 2433330392707687289131229 := by
  unfold tailWord_4738894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21605207961725481438195967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115227775795869234337045157 21605207961725481438195967)
  ·
    refine ⟨32407811942588222157293951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21605207961725481438195967 32407811942588222157293951)
    ·
      refine ⟨48611717913882333235940927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32407811942588222157293951 48611717913882333235940927)
      ·
        refine ⟨72917576870823499853911391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48611717913882333235940927 72917576870823499853911391)
        ·
          refine ⟨109376365306235249780867087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72917576870823499853911391 109376365306235249780867087)
          ·
            refine ⟨164064547959352874671300631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109376365306235249780867087 164064547959352874671300631)
            ·
              refine ⟨246096821939029312006950947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164064547959352874671300631 246096821939029312006950947)
              ·
                refine ⟨369145232908543968010426421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246096821939029312006950947 369145232908543968010426421)
                ·
                  refine ⟨34607365585175997000977477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 369145232908543968010426421 34607365585175997000977477)
                  ·
                    refine ⟨6488881047220499437683277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34607365585175997000977477 6488881047220499437683277)
                    ·
                      refine ⟨2433330392707687289131229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488881047220499437683277 2433330392707687289131229)
                      ·
                        rfl

theorem cell23_4738894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_4738894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738894 prefixEnd_4738894 := by exact prefixLift 4738894
  have htrace : WordTrace (prefixWord ++ tailWord_4738894) baseStart_4738894 baseEnd_4738894 := by
    simpa [prefixWord, tailWord_4738894, baseEnd_4738894] using wordTrace_append hprefix tailTrace_4738894
  have hstable : (prefixWord ++ tailWord_4738894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738894).length < 2 ^ (prefixWord ++ tailWord_4738894).sum := by decide
  have hdescent : baseEnd_4738894 < baseStart_4738894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4738941 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_4738941 : Nat := 118140960795 + 4738941 * 2 ^ 59
def prefixEnd_4738941 : Nat := 4983230072969 + 3 ^ 40 * 4738941 * 2
def baseEnd_4738941 : Nat := 2433354526298448605243513

theorem tailTrace_4738941 : CollatzResearch.WordTrace tailWord_4738941 prefixEnd_4738941 2433354526298448605243513 := by
  unfold tailWord_4738941
  simp only [CollatzResearch.WordTrace]
  refine ⟨172843377924633578532528677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115228918616422385688352451 172843377924633578532528677)
  ·
    refine ⟨32408133360868795974849127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172843377924633578532528677 32408133360868795974849127)
    ·
      refine ⟨48612200041303193962273691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32408133360868795974849127 48612200041303193962273691)
      ·
        refine ⟨72918300061954790943410537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48612200041303193962273691 72918300061954790943410537)
        ·
          refine ⟨54688725046466093207557903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72918300061954790943410537 54688725046466093207557903)
          ·
            refine ⟨82033087569699139811336855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54688725046466093207557903 82033087569699139811336855)
            ·
              refine ⟨123049631354548709717005283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82033087569699139811336855 123049631354548709717005283)
              ·
                refine ⟨184574447031823064575507925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123049631354548709717005283 184574447031823064575507925)
                ·
                  refine ⟨4325963602308353075988467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184574447031823064575507925 4325963602308353075988467)
                  ·
                    refine ⟨6488945403462529613982701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4325963602308353075988467 6488945403462529613982701)
                    ·
                      refine ⟨2433354526298448605243513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6488945403462529613982701 2433354526298448605243513)
                      ·
                        rfl

theorem cell23_4738941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_4738941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4738941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4738941 prefixEnd_4738941 := by exact prefixLift 4738941
  have htrace : WordTrace (prefixWord ++ tailWord_4738941) baseStart_4738941 baseEnd_4738941 := by
    simpa [prefixWord, tailWord_4738941, baseEnd_4738941] using wordTrace_append hprefix tailTrace_4738941
  have hstable : (prefixWord ++ tailWord_4738941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4738941).length < 2 ^ (prefixWord ++ tailWord_4738941).sum := by decide
  have hdescent : baseEnd_4738941 < baseStart_4738941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4738941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739001 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4739001 : Nat := 118140960795 + 4739001 * 2 ^ 59
def prefixEnd_4739001 : Nat := 4983230072969 + 3 ^ 40 * 4739001 * 2
def baseEnd_4739001 : Nat := 2433385335137718370493237

theorem tailTrace_4739001 : CollatzResearch.WordTrace tailWord_4739001 prefixEnd_4739001 2433385335137718370493237 := by
  unfold tailWord_4739001
  simp only [CollatzResearch.WordTrace]
  refine ⟨172845566304416208779712857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115230377536277472519808571 172845566304416208779712857)
  ·
    refine ⟨129634174728312156584784643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172845566304416208779712857 129634174728312156584784643)
    ·
      refine ⟨194451262092468234877176965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129634174728312156584784643 194451262092468234877176965)
      ·
        refine ⟨36459611642337794039470681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194451262092468234877176965 36459611642337794039470681)
        ·
          refine ⟨27344708731753345529603011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36459611642337794039470681 27344708731753345529603011)
          ·
            refine ⟨41017063097630018294404517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27344708731753345529603011 41017063097630018294404517)
            ·
              refine ⟨7690699330805628430200847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41017063097630018294404517 7690699330805628430200847)
              ·
                refine ⟨11536048996208442645301271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690699330805628430200847 11536048996208442645301271)
                ·
                  refine ⟨17304073494312663967951907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11536048996208442645301271 17304073494312663967951907)
                  ·
                    refine ⟨25956110241468995951927861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17304073494312663967951907 25956110241468995951927861)
                    ·
                      refine ⟨2433385335137718370493237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25956110241468995951927861 2433385335137718370493237)
                      ·
                        rfl

theorem cell23_4739001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4739001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739001 prefixEnd_4739001 := by exact prefixLift 4739001
  have htrace : WordTrace (prefixWord ++ tailWord_4739001) baseStart_4739001 baseEnd_4739001 := by
    simpa [prefixWord, tailWord_4739001, baseEnd_4739001] using wordTrace_append hprefix tailTrace_4739001
  have hstable : (prefixWord ++ tailWord_4739001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739001).length < 2 ^ (prefixWord ++ tailWord_4739001).sum := by decide
  have hdescent : baseEnd_4739001 < baseStart_4739001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739031 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_4739031 : Nat := 118140960795 + 4739031 * 2 ^ 59
def prefixEnd_4739031 : Nat := 4983230072969 + 3 ^ 40 * 4739031 * 2
def baseEnd_4739031 : Nat := 2433400739557353253118099

theorem tailTrace_4739031 : CollatzResearch.WordTrace tailWord_4739031 prefixEnd_4739031 2433400739557353253118099 := by
  unfold tailWord_4739031
  simp only [CollatzResearch.WordTrace]
  refine ⟨172846660494307523903304947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115231106996205015935536631 172846660494307523903304947)
  ·
    refine ⟨259269990741461285854957421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172846660494307523903304947 259269990741461285854957421)
    ·
      refine ⟨97226246528047982195609033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259269990741461285854957421 97226246528047982195609033)
      ·
        refine ⟨72919684896035986646706775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97226246528047982195609033 72919684896035986646706775)
        ·
          refine ⟨109379527344053979970060163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72919684896035986646706775 109379527344053979970060163)
          ·
            refine ⟨164069291016080969955090245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109379527344053979970060163 164069291016080969955090245)
            ·
              refine ⟨30762992065515181866579421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164069291016080969955090245 30762992065515181866579421)
              ·
                refine ⟨11536122024568193199967283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30762992065515181866579421 11536122024568193199967283)
                ·
                  refine ⟨17304183036852289799950925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11536122024568193199967283 17304183036852289799950925)
                  ·
                    refine ⟨6489068638819608674981597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17304183036852289799950925 6489068638819608674981597)
                    ·
                      refine ⟨2433400739557353253118099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489068638819608674981597 2433400739557353253118099)
                      ·
                        rfl

theorem cell23_4739031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_4739031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739031 prefixEnd_4739031 := by exact prefixLift 4739031
  have htrace : WordTrace (prefixWord ++ tailWord_4739031) baseStart_4739031 baseEnd_4739031 := by
    simpa [prefixWord, tailWord_4739031, baseEnd_4739031] using wordTrace_append hprefix tailTrace_4739031
  have hstable : (prefixWord ++ tailWord_4739031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739031).length < 2 ^ (prefixWord ++ tailWord_4739031).sum := by decide
  have hdescent : baseEnd_4739031 < baseStart_4739031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739065 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 3]
def baseStart_4739065 : Nat := 118140960795 + 4739065 * 2 ^ 59
def prefixEnd_4739065 : Nat := 4983230072969 + 3 ^ 40 * 4739065 * 2
def baseEnd_4739065 : Nat := 2433418197899606120092943

theorem tailTrace_4739065 : CollatzResearch.WordTrace tailWord_4739065 prefixEnd_4739065 2433418197899606120092943 := by
  unfold tailWord_4739065
  simp only [CollatzResearch.WordTrace]
  refine ⟨172847900576184347710042649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115231933717456231806695099 172847900576184347710042649)
  ·
    refine ⟨129635925432138260782531987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172847900576184347710042649 129635925432138260782531987)
    ·
      refine ⟨194453888148207391173797981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129635925432138260782531987 194453888148207391173797981)
      ·
        refine ⟨72920208055577771690174243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194453888148207391173797981 72920208055577771690174243)
        ·
          refine ⟨109380312083366657535261365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72920208055577771690174243 109380312083366657535261365)
          ·
            refine ⟨10254404257815624143930753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109380312083366657535261365 10254404257815624143930753)
            ·
              refine ⟨7690803193361718107948065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10254404257815624143930753 7690803193361718107948065)
              ·
                refine ⟨5768102395021288580961049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7690803193361718107948065 5768102395021288580961049)
                ·
                  refine ⟨4326076796265966435720787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768102395021288580961049 4326076796265966435720787)
                  ·
                    refine ⟨6489115194398949653581181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4326076796265966435720787 6489115194398949653581181)
                    ·
                      refine ⟨2433418197899606120092943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489115194398949653581181 2433418197899606120092943)
                      ·
                        rfl

theorem cell23_4739065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_4739065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739065 prefixEnd_4739065 := by exact prefixLift 4739065
  have htrace : WordTrace (prefixWord ++ tailWord_4739065) baseStart_4739065 baseEnd_4739065 := by
    simpa [prefixWord, tailWord_4739065, baseEnd_4739065] using wordTrace_append hprefix tailTrace_4739065
  have hstable : (prefixWord ++ tailWord_4739065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739065).length < 2 ^ (prefixWord ++ tailWord_4739065).sum := by decide
  have hdescent : baseEnd_4739065 < baseStart_4739065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739118 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4739118 : Nat := 118140960795 + 4739118 * 2 ^ 59
def prefixEnd_4739118 : Nat := 4983230072969 + 3 ^ 40 * 4739118 * 2
def baseEnd_4739118 : Nat := 2433445412374294412730199

theorem tailTrace_4739118 : CollatzResearch.WordTrace tailWord_4739118 prefixEnd_4739118 2433445412374294412730199 := by
  unfold tailWord_4739118
  simp only [CollatzResearch.WordTrace]
  refine ⟨21606229205624042220215251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115233222429994891841148005 21606229205624042220215251)
  ·
    refine ⟨32409343808436063330322877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21606229205624042220215251 32409343808436063330322877)
    ·
      refine ⟨12153503928163523748871079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32409343808436063330322877 12153503928163523748871079)
      ·
        refine ⟨18230255892245285623306619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12153503928163523748871079 18230255892245285623306619)
        ·
          refine ⟨27345383838367928434959929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18230255892245285623306619 27345383838367928434959929)
          ·
            refine ⟨20509037878775946326219947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27345383838367928434959929 20509037878775946326219947)
            ·
              refine ⟨30763556818163919489329921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20509037878775946326219947 30763556818163919489329921)
              ·
                refine ⟨23072667613622939616997441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30763556818163919489329921 23072667613622939616997441)
                ·
                  refine ⟨17304500710217204712748081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23072667613622939616997441 17304500710217204712748081)
                  ·
                    refine ⟨12978375532662903534561061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17304500710217204712748081 12978375532662903534561061)
                    ·
                      refine ⟨2433445412374294412730199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12978375532662903534561061 2433445412374294412730199)
                      ·
                        rfl

theorem cell23_4739118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4739118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739118 prefixEnd_4739118 := by exact prefixLift 4739118
  have htrace : WordTrace (prefixWord ++ tailWord_4739118) baseStart_4739118 baseEnd_4739118 := by
    simpa [prefixWord, tailWord_4739118, baseEnd_4739118] using wordTrace_append hprefix tailTrace_4739118
  have hstable : (prefixWord ++ tailWord_4739118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739118).length < 2 ^ (prefixWord ++ tailWord_4739118).sum := by decide
  have hdescent : baseEnd_4739118 < baseStart_4739118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739122 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_4739122 : Nat := 118140960795 + 4739122 * 2 ^ 59
def prefixEnd_4739122 : Nat := 4983230072969 + 3 ^ 40 * 4739122 * 2
def baseEnd_4739122 : Nat := 2433447466296912397080181

theorem tailTrace_4739122 : CollatzResearch.WordTrace tailWord_4739122 prefixEnd_4739122 2433447466296912397080181 := by
  unfold tailWord_4739122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43212494884244461611216905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115233319691318564296578413 43212494884244461611216905)
  ·
    refine ⟨32409371163183346208412679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43212494884244461611216905 32409371163183346208412679)
    ·
      refine ⟨48614056744775019312619019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32409371163183346208412679 48614056744775019312619019)
      ·
        refine ⟨72921085117162528968928529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48614056744775019312619019 72921085117162528968928529)
        ·
          refine ⟨54690813837871896726696397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72921085117162528968928529 54690813837871896726696397)
          ·
            refine ⟨20509055189201961272511149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54690813837871896726696397 20509055189201961272511149)
            ·
              refine ⟨7690895695950735477191681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20509055189201961272511149 7690895695950735477191681)
              ·
                refine ⟨5768171771963051607893761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7690895695950735477191681 5768171771963051607893761)
                ·
                  refine ⟨4326128828972288705920321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768171771963051607893761 4326128828972288705920321)
                  ·
                    refine ⟨3244596621729216529440241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326128828972288705920321 3244596621729216529440241)
                    ·
                      refine ⟨2433447466296912397080181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244596621729216529440241 2433447466296912397080181)
                      ·
                        rfl

theorem cell23_4739122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_4739122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739122 prefixEnd_4739122 := by exact prefixLift 4739122
  have htrace : WordTrace (prefixWord ++ tailWord_4739122) baseStart_4739122 baseEnd_4739122 := by
    simpa [prefixWord, tailWord_4739122, baseEnd_4739122] using wordTrace_append hprefix tailTrace_4739122
  have hstable : (prefixWord ++ tailWord_4739122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739122).length < 2 ^ (prefixWord ++ tailWord_4739122).sum := by decide
  have hdescent : baseEnd_4739122 < baseStart_4739122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739128 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 7]
def baseStart_4739128 : Nat := 118140960795 + 4739128 * 2 ^ 59
def prefixEnd_4739128 : Nat := 4983230072969 + 3 ^ 40 * 4739128 * 2
def baseEnd_4739128 : Nat := 270383394131204374845017

theorem tailTrace_4739128 : CollatzResearch.WordTrace tailWord_4739128 prefixEnd_4739128 270383394131204374845017 := by
  unfold tailWord_4739128
  simp only [CollatzResearch.WordTrace]
  refine ⟨86425099187478054734793019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115233465583304072979724025 86425099187478054734793019)
  ·
    refine ⟨129637648781217082102189529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86425099187478054734793019 129637648781217082102189529)
    ·
      refine ⟨97228236585912811576642147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129637648781217082102189529 97228236585912811576642147)
      ·
        refine ⟨145842354878869217364963221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97228236585912811576642147 145842354878869217364963221)
        ·
          refine ⟨6836360384946994563982651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145842354878869217364963221 6836360384946994563982651)
          ·
            refine ⟨10254540577420491845973977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836360384946994563982651 10254540577420491845973977)
            ·
              refine ⟨7690905433065368884480483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10254540577420491845973977 7690905433065368884480483)
              ·
                refine ⟨11536358149598053326720725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690905433065368884480483 11536358149598053326720725)
                ·
                  refine ⟨270383394131204374845017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11536358149598053326720725 270383394131204374845017)
                  ·
                    rfl

theorem cell23_4739128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 7].length) (baseStart_4739128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739128 prefixEnd_4739128 := by exact prefixLift 4739128
  have htrace : WordTrace (prefixWord ++ tailWord_4739128) baseStart_4739128 baseEnd_4739128 := by
    simpa [prefixWord, tailWord_4739128, baseEnd_4739128] using wordTrace_append hprefix tailTrace_4739128
  have hstable : (prefixWord ++ tailWord_4739128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739128).length < 2 ^ (prefixWord ++ tailWord_4739128).sum := by decide
  have hdescent : baseEnd_4739128 < baseStart_4739128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739148 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 2, 5, 2]
def baseStart_4739148 : Nat := 118140960795 + 4739148 * 2 ^ 59
def prefixEnd_4739148 : Nat := 4983230072969 + 3 ^ 40 * 4739148 * 2
def baseEnd_4739148 : Nat := 2433460816793929295355061

theorem tailTrace_4739148 : CollatzResearch.WordTrace tailWord_4739148 prefixEnd_4739148 2433460816793929295355061 := by
  unfold tailWord_4739148
  simp only [CollatzResearch.WordTrace]
  refine ⟨86425463917441826442657049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115233951889922435256876065 86425463917441826442657049)
  ·
    refine ⟨64819097938081369831992787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86425463917441826442657049 64819097938081369831992787)
    ·
      refine ⟨97228646907122054747989181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64819097938081369831992787 97228646907122054747989181)
      ·
        refine ⟨36460742590170770530495943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97228646907122054747989181 36460742590170770530495943)
        ·
          refine ⟨54691113885256155795743915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36460742590170770530495943 54691113885256155795743915)
          ·
            refine ⟨82036670827884233693615873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54691113885256155795743915 82036670827884233693615873)
            ·
              refine ⟨61527503120913175270211905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82036670827884233693615873 61527503120913175270211905)
              ·
                refine ⟨46145627340684881452658929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61527503120913175270211905 46145627340684881452658929)
                ·
                  refine ⟨34609220505513661089494197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46145627340684881452658929 34609220505513661089494197)
                  ·
                    refine ⟨3244614422391905727140081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34609220505513661089494197 3244614422391905727140081)
                    ·
                      refine ⟨2433460816793929295355061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244614422391905727140081 2433460816793929295355061)
                      ·
                        rfl

theorem cell23_4739148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_4739148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739148 prefixEnd_4739148 := by exact prefixLift 4739148
  have htrace : WordTrace (prefixWord ++ tailWord_4739148) baseStart_4739148 baseEnd_4739148 := by
    simpa [prefixWord, tailWord_4739148, baseEnd_4739148] using wordTrace_append hprefix tailTrace_4739148
  have hstable : (prefixWord ++ tailWord_4739148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739148).length < 2 ^ (prefixWord ++ tailWord_4739148).sum := by decide
  have hdescent : baseEnd_4739148 < baseStart_4739148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739161 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_4739161 : Nat := 118140960795 + 4739161 * 2 ^ 59
def prefixEnd_4739161 : Nat := 4983230072969 + 3 ^ 40 * 4739161 * 2
def baseEnd_4739161 : Nat := 2433467492042437744492501

theorem tailTrace_4739161 : CollatzResearch.WordTrace tailWord_4739161 prefixEnd_4739161 2433467492042437744492501 := by
  unfold tailWord_4739161
  simp only [CollatzResearch.WordTrace]
  refine ⟨172851401983836556105537337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115234267989224370737024891 172851401983836556105537337)
  ·
    refine ⟨129638551487877417079153003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172851401983836556105537337 129638551487877417079153003)
    ·
      refine ⟨194457827231816125618729505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129638551487877417079153003 194457827231816125618729505)
      ·
        refine ⟨145843370423862094214047129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194457827231816125618729505 145843370423862094214047129)
        ·
          refine ⟨109382527817896570660535347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145843370423862094214047129 109382527817896570660535347)
          ·
            refine ⟨164073791726844855990803021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109382527817896570660535347 164073791726844855990803021)
            ·
              refine ⟨61527671897566820996551133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164073791726844855990803021 61527671897566820996551133)
              ·
                refine ⟨23072876961587557873706675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61527671897566820996551133 23072876961587557873706675)
                ·
                  refine ⟨34609315442381336810560013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23072876961587557873706675 34609315442381336810560013)
                  ·
                    refine ⟨12978493290893001303960005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34609315442381336810560013 12978493290893001303960005)
                    ·
                      refine ⟨2433467492042437744492501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12978493290893001303960005 2433467492042437744492501)
                      ·
                        rfl

theorem cell23_4739161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_4739161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739161 prefixEnd_4739161 := by exact prefixLift 4739161
  have htrace : WordTrace (prefixWord ++ tailWord_4739161) baseStart_4739161 baseEnd_4739161 := by
    simpa [prefixWord, tailWord_4739161, baseEnd_4739161] using wordTrace_append hprefix tailTrace_4739161
  have hstable : (prefixWord ++ tailWord_4739161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739161).length < 2 ^ (prefixWord ++ tailWord_4739161).sum := by decide
  have hdescent : baseEnd_4739161 < baseStart_4739161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739239 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4739239 : Nat := 118140960795 + 4739239 * 2 ^ 59
def prefixEnd_4739239 : Nat := 4983230072969 + 3 ^ 40 * 4739239 * 2
def baseEnd_4739239 : Nat := 811169181177829479772381

theorem tailTrace_4739239 : CollatzResearch.WordTrace tailWord_4739239 prefixEnd_4739239 811169181177829479772381 := by
  unfold tailWord_4739239
  simp only [CollatzResearch.WordTrace]
  refine ⟨172854246877553975426876771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115236164585035983617917847 172854246877553975426876771)
  ·
    refine ⟨259281370316330963140315157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172854246877553975426876771 259281370316330963140315157)
    ·
      refine ⟨12153814233578013897202273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 259281370316330963140315157 12153814233578013897202273)
      ·
        refine ⟨9115360675183510422901705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12153814233578013897202273 9115360675183510422901705)
        ·
          refine ⟨6836520506387632817176279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9115360675183510422901705 6836520506387632817176279)
          ·
            refine ⟨10254780759581449225764419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836520506387632817176279 10254780759581449225764419)
            ·
              refine ⟨15382171139372173838646629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10254780759581449225764419 15382171139372173838646629)
              ·
                refine ⟨2884157088632282594746243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15382171139372173838646629 2884157088632282594746243)
                ·
                  refine ⟨4326235632948423892119365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884157088632282594746243 4326235632948423892119365)
                  ·
                    refine ⟨811169181177829479772381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4326235632948423892119365 811169181177829479772381)
                    ·
                      rfl

theorem cell23_4739239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4739239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739239 prefixEnd_4739239 := by exact prefixLift 4739239
  have htrace : WordTrace (prefixWord ++ tailWord_4739239) baseStart_4739239 baseEnd_4739239 := by
    simpa [prefixWord, tailWord_4739239, baseEnd_4739239] using wordTrace_append hprefix tailTrace_4739239
  have hstable : (prefixWord ++ tailWord_4739239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739239).length < 2 ^ (prefixWord ++ tailWord_4739239).sum := by decide
  have hdescent : baseEnd_4739239 < baseStart_4739239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739266 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_4739266 : Nat := 118140960795 + 4739266 * 2 ^ 59
def prefixEnd_4739266 : Nat := 4983230072969 + 3 ^ 40 * 4739266 * 2
def baseEnd_4739266 : Nat := 2433521407511159833679519

theorem tailTrace_4739266 : CollatzResearch.WordTrace tailWord_4739266 prefixEnd_4739266 2433521407511159833679519 := by
  unfold tailWord_4739266
  simp only [CollatzResearch.WordTrace]
  refine ⟨43213807912114039759527413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115236821098970772692073101 43213807912114039759527413)
  ·
    refine ⟨4051294491760691227455695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43213807912114039759527413 4051294491760691227455695)
    ·
      refine ⟨6076941737641036841183543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051294491760691227455695 6076941737641036841183543)
      ·
        refine ⟨9115412606461555261775315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076941737641036841183543 9115412606461555261775315)
        ·
          refine ⟨13673118909692332892662973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9115412606461555261775315 13673118909692332892662973)
          ·
            refine ⟨5127419591134624834748615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13673118909692332892662973 5127419591134624834748615)
            ·
              refine ⟨7691129386701937252122923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127419591134624834748615 7691129386701937252122923)
              ·
                refine ⟨11536694080052905878184385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7691129386701937252122923 11536694080052905878184385)
                ·
                  refine ⟨8652520560039679408638289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11536694080052905878184385 8652520560039679408638289)
                  ·
                    refine ⟨6489390420029759556478717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8652520560039679408638289 6489390420029759556478717)
                    ·
                      refine ⟨2433521407511159833679519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489390420029759556478717 2433521407511159833679519)
                      ·
                        rfl

theorem cell23_4739266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_4739266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739266 prefixEnd_4739266 := by exact prefixLift 4739266
  have htrace : WordTrace (prefixWord ++ tailWord_4739266) baseStart_4739266 baseEnd_4739266 := by
    simpa [prefixWord, tailWord_4739266, baseEnd_4739266] using wordTrace_append hprefix tailTrace_4739266
  have hstable : (prefixWord ++ tailWord_4739266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739266).length < 2 ^ (prefixWord ++ tailWord_4739266).sum := by decide
  have hdescent : baseEnd_4739266 < baseStart_4739266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739282 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_4739282 : Nat := 118140960795 + 4739282 * 2 ^ 59
def prefixEnd_4739282 : Nat := 4983230072969 + 3 ^ 40 * 4739282 * 2
def baseEnd_4739282 : Nat := 811176541067210590359815

theorem tailTrace_4739282 : CollatzResearch.WordTrace tailWord_4739282 prefixEnd_4739282 811176541067210590359815 := by
  unfold tailWord_4739282
  simp only [CollatzResearch.WordTrace]
  refine ⟨43213953804099548442673025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115237210144265462513794733 43213953804099548442673025)
  ·
    refine ⟨32410465353074661332004769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43213953804099548442673025 32410465353074661332004769)
    ·
      refine ⟨24307849014805995999003577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32410465353074661332004769 24307849014805995999003577)
      ·
        refine ⟨18230886761104496999252683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24307849014805995999003577 18230886761104496999252683)
        ·
          refine ⟨27346330141656745498879025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18230886761104496999252683 27346330141656745498879025)
          ·
            refine ⟨20509747606242559124159269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27346330141656745498879025 20509747606242559124159269)
            ·
              refine ⟨3845577676170479835779863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20509747606242559124159269 3845577676170479835779863)
              ·
                refine ⟨5768366514255719753669795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845577676170479835779863 5768366514255719753669795)
                ·
                  refine ⟨8652549771383579630504693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768366514255719753669795 8652549771383579630504693)
                  ·
                    refine ⟨811176541067210590359815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8652549771383579630504693 811176541067210590359815)
                    ·
                      rfl

theorem cell23_4739282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_4739282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739282 prefixEnd_4739282 := by exact prefixLift 4739282
  have htrace : WordTrace (prefixWord ++ tailWord_4739282) baseStart_4739282 baseEnd_4739282 := by
    simpa [prefixWord, tailWord_4739282, baseEnd_4739282] using wordTrace_append hprefix tailTrace_4739282
  have hstable : (prefixWord ++ tailWord_4739282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739282).length < 2 ^ (prefixWord ++ tailWord_4739282).sum := by decide
  have hdescent : baseEnd_4739282 < baseStart_4739282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739322 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_4739322 : Nat := 118140960795 + 4739322 * 2 ^ 59
def prefixEnd_4739322 : Nat := 4983230072969 + 3 ^ 40 * 4739322 * 2
def baseEnd_4739322 : Nat := 2433550162427811614579261

theorem tailTrace_4739322 : CollatzResearch.WordTrace tailWord_4739322 prefixEnd_4739322 2433550162427811614579261 := by
  unfold tailWord_4739322
  simp only [CollatzResearch.WordTrace]
  refine ⟨43214318534063320150537055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115238182757502187068098813 43214318534063320150537055)
  ·
    refine ⟨64821477801094980225805583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43214318534063320150537055 64821477801094980225805583)
    ·
      refine ⟨97232216701642470338708375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64821477801094980225805583 97232216701642470338708375)
      ·
        refine ⟨145848325052463705508062563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97232216701642470338708375 145848325052463705508062563)
        ·
          refine ⟨218772487578695558262093845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145848325052463705508062563 218772487578695558262093845)
          ·
            refine ⟨10254960355251354293535649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 218772487578695558262093845 10254960355251354293535649)
            ·
              refine ⟨7691220266438515720151737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10254960355251354293535649 7691220266438515720151737)
              ·
                refine ⟨5768415199828886790113803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7691220266438515720151737 5768415199828886790113803)
                ·
                  refine ⟨8652622799743330185170705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768415199828886790113803 8652622799743330185170705)
                  ·
                    refine ⟨6489467099807497638878029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8652622799743330185170705 6489467099807497638878029)
                    ·
                      refine ⟨2433550162427811614579261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489467099807497638878029 2433550162427811614579261)
                      ·
                        rfl

theorem cell23_4739322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_4739322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739322 prefixEnd_4739322 := by exact prefixLift 4739322
  have htrace : WordTrace (prefixWord ++ tailWord_4739322) baseStart_4739322 baseEnd_4739322 := by
    simpa [prefixWord, tailWord_4739322, baseEnd_4739322] using wordTrace_append hprefix tailTrace_4739322
  have hstable : (prefixWord ++ tailWord_4739322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739322).length < 2 ^ (prefixWord ++ tailWord_4739322).sum := by decide
  have hdescent : baseEnd_4739322 < baseStart_4739322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739336 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_4739336 : Nat := 118140960795 + 4739336 * 2 ^ 59
def prefixEnd_4739336 : Nat := 4983230072969 + 3 ^ 40 * 4739336 * 2
def baseEnd_4739336 : Nat := 2433557351156974559804197

theorem tailTrace_4739336 : CollatzResearch.WordTrace tailWord_4739336 prefixEnd_4739336 2433557351156974559804197 := by
  unfold tailWord_4739336
  simp only [CollatzResearch.WordTrace]
  refine ⟨86428892379101280496578931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115238523172135040662105241 86428892379101280496578931)
  ·
    refine ⟨129643338568651920744868397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86428892379101280496578931 129643338568651920744868397)
    ·
      refine ⟨48616251963244470279325649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129643338568651920744868397 48616251963244470279325649)
      ·
        refine ⟨36462188972433352709494237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48616251963244470279325649 36462188972433352709494237)
        ·
          refine ⟨13673320864662507266060339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36462188972433352709494237 13673320864662507266060339)
          ·
            refine ⟨20509981296993760899090509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13673320864662507266060339 20509981296993760899090509)
            ·
              refine ⟨7691242986372660337158941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20509981296993760899090509 7691242986372660337158941)
              ·
                refine ⟨2884216119889747626434603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7691242986372660337158941 2884216119889747626434603)
                ·
                  refine ⟨4326324179834621439651905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884216119889747626434603 4326324179834621439651905)
                  ·
                    refine ⟨3244743134875966079738929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326324179834621439651905 3244743134875966079738929)
                    ·
                      refine ⟨2433557351156974559804197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244743134875966079738929 2433557351156974559804197)
                      ·
                        rfl

theorem cell23_4739336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_4739336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739336 prefixEnd_4739336 := by exact prefixLift 4739336
  have htrace : WordTrace (prefixWord ++ tailWord_4739336) baseStart_4739336 baseEnd_4739336 := by
    simpa [prefixWord, tailWord_4739336, baseEnd_4739336] using wordTrace_append hprefix tailTrace_4739336
  have hstable : (prefixWord ++ tailWord_4739336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739336).length < 2 ^ (prefixWord ++ tailWord_4739336).sum := by decide
  have hdescent : baseEnd_4739336 < baseStart_4739336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739352 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_4739352 : Nat := 118140960795 + 4739352 * 2 ^ 59
def prefixEnd_4739352 : Nat := 4983230072969 + 3 ^ 40 * 4739352 * 2
def baseEnd_4739352 : Nat := 2433565566847446497204123

theorem tailTrace_4739352 : CollatzResearch.WordTrace tailWord_4739352 prefixEnd_4739352 2433565566847446497204123 := by
  unfold tailWord_4739352
  simp only [CollatzResearch.WordTrace]
  refine ⟨86429184163072297862870155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115238912217429730483826873 86429184163072297862870155)
  ·
    refine ⟨129643776244608446794305233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86429184163072297862870155 129643776244608446794305233)
    ·
      refine ⟨97232832183456335095728925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129643776244608446794305233 97232832183456335095728925)
      ·
        refine ⟨36462312068796125660898347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97232832183456335095728925 36462312068796125660898347)
        ·
          refine ⟨54693468103194188491347521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36462312068796125660898347 54693468103194188491347521)
          ·
            refine ⟨41020101077395641368510641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54693468103194188491347521 41020101077395641368510641)
            ·
              refine ⟨30765075808046731026382981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41020101077395641368510641 30765075808046731026382981)
              ·
                refine ⟨5768451714008762067446809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30765075808046731026382981 5768451714008762067446809)
                ·
                  refine ⟨4326338785506571550585107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768451714008762067446809 4326338785506571550585107)
                  ·
                    refine ⟨6489508178259857325877661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4326338785506571550585107 6489508178259857325877661)
                    ·
                      refine ⟨2433565566847446497204123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489508178259857325877661 2433565566847446497204123)
                      ·
                        rfl

theorem cell23_4739352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_4739352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739352 prefixEnd_4739352 := by exact prefixLift 4739352
  have htrace : WordTrace (prefixWord ++ tailWord_4739352) baseStart_4739352 baseEnd_4739352 := by
    simpa [prefixWord, tailWord_4739352, baseEnd_4739352] using wordTrace_append hprefix tailTrace_4739352
  have hstable : (prefixWord ++ tailWord_4739352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739352).length < 2 ^ (prefixWord ++ tailWord_4739352).sum := by decide
  have hdescent : baseEnd_4739352 < baseStart_4739352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739373 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4739373 : Nat := 118140960795 + 4739373 * 2 ^ 59
def prefixEnd_4739373 : Nat := 4983230072969 + 3 ^ 40 * 4739373 * 2
def baseEnd_4739373 : Nat := 2433576349941190915041527

theorem tailTrace_4739373 : CollatzResearch.WordTrace tailWord_4739373 prefixEnd_4739373 2433576349941190915041527 := by
  unfold tailWord_4739373
  simp only [CollatzResearch.WordTrace]
  refine ⟨172859134259068516312254773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115239422839379010874836515 172859134259068516312254773)
  ·
    refine ⟨16205543836787673404273885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172859134259068516312254773 16205543836787673404273885)
    ·
      refine ⟨6077078938795377526602707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16205543836787673404273885 6077078938795377526602707)
      ·
        refine ⟨9115618408193066289904061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6077078938795377526602707 9115618408193066289904061)
        ·
          refine ⟨3418356903072399858714023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9115618408193066289904061 3418356903072399858714023)
          ·
            refine ⟨5127535354608599788071035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418356903072399858714023 5127535354608599788071035)
            ·
              refine ⟨7691303031912899682106553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127535354608599788071035 7691303031912899682106553)
              ·
                refine ⟨5768477273934674761579915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7691303031912899682106553 5768477273934674761579915)
                ·
                  refine ⟨8652715910902012142369873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768477273934674761579915 8652715910902012142369873)
                  ·
                    refine ⟨6489536933176509106777405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8652715910902012142369873 6489536933176509106777405)
                    ·
                      refine ⟨2433576349941190915041527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489536933176509106777405 2433576349941190915041527)
                      ·
                        rfl

theorem cell23_4739373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4739373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739373 prefixEnd_4739373 := by exact prefixLift 4739373
  have htrace : WordTrace (prefixWord ++ tailWord_4739373) baseStart_4739373 baseEnd_4739373 := by
    simpa [prefixWord, tailWord_4739373, baseEnd_4739373] using wordTrace_append hprefix tailTrace_4739373
  have hstable : (prefixWord ++ tailWord_4739373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739373).length < 2 ^ (prefixWord ++ tailWord_4739373).sum := by decide
  have hdescent : baseEnd_4739373 < baseStart_4739373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739392 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 4, 2, 2]
def baseStart_4739392 : Nat := 118140960795 + 4739392 * 2 ^ 59
def prefixEnd_4739392 : Nat := 4983230072969 + 3 ^ 40 * 4739392 * 2
def baseEnd_4739392 : Nat := 2433586106073626340703939

theorem tailTrace_4739392 : CollatzResearch.WordTrace tailWord_4739392 prefixEnd_4739392 2433586106073626340703939 := by
  unfold tailWord_4739392
  simp only [CollatzResearch.WordTrace]
  refine ⟨86429913622999841278598215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115239884830666455038130953 86429913622999841278598215)
  ·
    refine ⟨129644870434499761917897323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86429913622999841278598215 129644870434499761917897323)
    ·
      refine ⟨194467305651749642876845985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129644870434499761917897323 194467305651749642876845985)
      ·
        refine ⟨145850479238812232157634489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194467305651749642876845985 145850479238812232157634489)
        ·
          refine ⟨109387859429109174118225867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145850479238812232157634489 109387859429109174118225867)
          ·
            refine ⟨164081789143663761177338801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109387859429109174118225867 164081789143663761177338801)
            ·
              refine ⟨123061341857747820883004101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164081789143663761177338801 123061341857747820883004101)
              ·
                refine ⟨23074001598327716415563269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123061341857747820883004101 23074001598327716415563269)
                ·
                  refine ⟨4326375299686446827918113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23074001598327716415563269 4326375299686446827918113)
                  ·
                    refine ⟨3244781474764835120938585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326375299686446827918113 3244781474764835120938585)
                    ·
                      refine ⟨2433586106073626340703939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244781474764835120938585 2433586106073626340703939)
                      ·
                        rfl

theorem cell23_4739392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_4739392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739392 prefixEnd_4739392 := by exact prefixLift 4739392
  have htrace : WordTrace (prefixWord ++ tailWord_4739392) baseStart_4739392 baseEnd_4739392 := by
    simpa [prefixWord, tailWord_4739392, baseEnd_4739392] using wordTrace_append hprefix tailTrace_4739392
  have hstable : (prefixWord ++ tailWord_4739392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739392).length < 2 ^ (prefixWord ++ tailWord_4739392).sum := by decide
  have hdescent : baseEnd_4739392 < baseStart_4739392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739409 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 2, 2, 2]
def baseStart_4739409 : Nat := 118140960795 + 4739409 * 2 ^ 59
def prefixEnd_4739409 : Nat := 4983230072969 + 3 ^ 40 * 4739409 * 2
def baseEnd_4739409 : Nat := 2433594835244752774191361

theorem tailTrace_4739409 : CollatzResearch.WordTrace tailWord_4739409 prefixEnd_4739409 2433594835244752774191361 := by
  unfold tailWord_4739409
  simp only [CollatzResearch.WordTrace]
  refine ⟨172860447286938094460565281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115240298191292062973710187 172860447286938094460565281)
  ·
    refine ⟨129645335465203570845423961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172860447286938094460565281 129645335465203570845423961)
    ·
      refine ⟨97234001598902678134067971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129645335465203570845423961 97234001598902678134067971)
      ·
        refine ⟨145851002398354017201101957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97234001598902678134067971 145851002398354017201101957)
        ·
          refine ⟨27347062949691378225206617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145851002398354017201101957 27347062949691378225206617)
          ·
            refine ⟨20510297212268533668904963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27347062949691378225206617 20510297212268533668904963)
            ·
              refine ⟨30765445818402800503357445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20510297212268533668904963 30765445818402800503357445)
              ·
                refine ⟨5768521090950525094379521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30765445818402800503357445 5768521090950525094379521)
                ·
                  refine ⟨4326390818212893820784641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768521090950525094379521 4326390818212893820784641)
                  ·
                    refine ⟨3244793113659670365588481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326390818212893820784641 3244793113659670365588481)
                    ·
                      refine ⟨2433594835244752774191361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244793113659670365588481 2433594835244752774191361)
                      ·
                        rfl

theorem cell23_4739409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_4739409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739409 prefixEnd_4739409 := by exact prefixLift 4739409
  have htrace : WordTrace (prefixWord ++ tailWord_4739409) baseStart_4739409 baseEnd_4739409 := by
    simpa [prefixWord, tailWord_4739409, baseEnd_4739409] using wordTrace_append hprefix tailTrace_4739409
  have hstable : (prefixWord ++ tailWord_4739409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739409).length < 2 ^ (prefixWord ++ tailWord_4739409).sum := by decide
  have hdescent : baseEnd_4739409 < baseStart_4739409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739418 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_4739418 : Nat := 118140960795 + 4739418 * 2 ^ 59
def prefixEnd_4739418 : Nat := 4983230072969 + 3 ^ 40 * 4739418 * 2
def baseEnd_4739418 : Nat := 2433599456570643238978819

theorem tailTrace_4739418 : CollatzResearch.WordTrace tailWord_4739418 prefixEnd_4739418 2433599456570643238978819 := by
  unfold tailWord_4739418
  simp only [CollatzResearch.WordTrace]
  refine ⟨43215193885976372249410727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115240517029270325998428605 43215193885976372249410727)
  ·
    refine ⟨64822790828964558374116091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43215193885976372249410727 64822790828964558374116091)
    ·
      refine ⟨97234186243446837561174137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64822790828964558374116091 97234186243446837561174137)
      ·
        refine ⟨72925639682585128170880603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97234186243446837561174137 72925639682585128170880603)
        ·
          refine ⟨109388459523877692256320905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72925639682585128170880603 109388459523877692256320905)
          ·
            refine ⟨82041344642908269192240679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109388459523877692256320905 82041344642908269192240679)
            ·
              refine ⟨123062016964362403788361019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82041344642908269192240679 123062016964362403788361019)
              ·
                refine ⟨184593025446543605682541529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123062016964362403788361019 184593025446543605682541529)
                ·
                  refine ⟨138444769084907704261906147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184593025446543605682541529 138444769084907704261906147)
                  ·
                    refine ⟨207667153627361556392859221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138444769084907704261906147 207667153627361556392859221)
                    ·
                      refine ⟨2433599456570643238978819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 207667153627361556392859221 2433599456570643238978819)
                      ·
                        rfl

theorem cell23_4739418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_4739418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739418 prefixEnd_4739418 := by exact prefixLift 4739418
  have htrace : WordTrace (prefixWord ++ tailWord_4739418) baseStart_4739418 baseEnd_4739418 := by
    simpa [prefixWord, tailWord_4739418, baseEnd_4739418] using wordTrace_append hprefix tailTrace_4739418
  have hstable : (prefixWord ++ tailWord_4739418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739418).length < 2 ^ (prefixWord ++ tailWord_4739418).sum := by decide
  have hdescent : baseEnd_4739418 < baseStart_4739418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739426 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_4739426 : Nat := 118140960795 + 4739426 * 2 ^ 59
def prefixEnd_4739426 : Nat := 4983230072969 + 3 ^ 40 * 4739426 * 2
def baseEnd_4739426 : Nat := 2433603564415879207678783

theorem tailTrace_4739426 : CollatzResearch.WordTrace tailWord_4739426 prefixEnd_4739426 2433603564415879207678783 := by
  unfold tailWord_4739426
  simp only [CollatzResearch.WordTrace]
  refine ⟨43215266831969126590983533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115240711551917670909289421 43215266831969126590983533)
  ·
    refine ⟨16205725061988422471618825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43215266831969126590983533 16205725061988422471618825)
    ·
      refine ⟨12154293796491316853714119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16205725061988422471618825 12154293796491316853714119)
      ·
        refine ⟨18231440694736975280571179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12154293796491316853714119 18231440694736975280571179)
        ·
          refine ⟨27347161042105462920856769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18231440694736975280571179 27347161042105462920856769)
          ·
            refine ⟨20510370781579097190642577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27347161042105462920856769 20510370781579097190642577)
            ·
              refine ⟨15382778086184322892981933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20510370781579097190642577 15382778086184322892981933)
              ·
                refine ⟨5768541782319121084868225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15382778086184322892981933 5768541782319121084868225)
                ·
                  refine ⟨4326406336739340813651169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768541782319121084868225 4326406336739340813651169)
                  ·
                    refine ⟨3244804752554505610238377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326406336739340813651169 3244804752554505610238377)
                    ·
                      refine ⟨2433603564415879207678783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244804752554505610238377 2433603564415879207678783)
                      ·
                        rfl

theorem cell23_4739426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_4739426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739426 prefixEnd_4739426 := by exact prefixLift 4739426
  have htrace : WordTrace (prefixWord ++ tailWord_4739426) baseStart_4739426 baseEnd_4739426 := by
    simpa [prefixWord, tailWord_4739426, baseEnd_4739426] using wordTrace_append hprefix tailTrace_4739426
  have hstable : (prefixWord ++ tailWord_4739426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739426).length < 2 ^ (prefixWord ++ tailWord_4739426).sum := by decide
  have hdescent : baseEnd_4739426 < baseStart_4739426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739492 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_4739492 : Nat := 118140960795 + 4739492 * 2 ^ 59
def prefixEnd_4739492 : Nat := 4983230072969 + 3 ^ 40 * 4739492 * 2
def baseEnd_4739492 : Nat := 811212484713025316484493

theorem tailTrace_4739492 : CollatzResearch.WordTrace tailWord_4739492 prefixEnd_4739492 811212484713025316484493 := by
  unfold tailWord_4739492
  simp only [CollatzResearch.WordTrace]
  refine ⟨86431737272818699817918365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115242316363758266423891153 86431737272818699817918365)
  ·
    refine ⟨32411901477307012431719387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86431737272818699817918365 32411901477307012431719387)
    ·
      refine ⟨48617852215960518647579081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32411901477307012431719387 48617852215960518647579081)
      ·
        refine ⟨36463389161970388985684311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48617852215960518647579081 36463389161970388985684311)
        ·
          refine ⟨54695083742955583478526467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36463389161970388985684311 54695083742955583478526467)
          ·
            refine ⟨82042625614433375217789701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54695083742955583478526467 82042625614433375217789701)
            ·
              refine ⟨15382992302706257853335569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82042625614433375217789701 15382992302706257853335569)
              ·
                refine ⟨11537244227029693390001677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15382992302706257853335569 11537244227029693390001677)
                ·
                  refine ⟨4326466585136135021250629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11537244227029693390001677 4326466585136135021250629)
                  ·
                    refine ⟨811212484713025316484493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4326466585136135021250629 811212484713025316484493)
                    ·
                      rfl

theorem cell23_4739492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_4739492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739492 prefixEnd_4739492 := by exact prefixLift 4739492
  have htrace : WordTrace (prefixWord ++ tailWord_4739492) baseStart_4739492 baseEnd_4739492 := by
    simpa [prefixWord, tailWord_4739492, baseEnd_4739492] using wordTrace_append hprefix tailTrace_4739492
  have hstable : (prefixWord ++ tailWord_4739492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739492).length < 2 ^ (prefixWord ++ tailWord_4739492).sum := by decide
  have hdescent : baseEnd_4739492 < baseStart_4739492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739505 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 8]
def baseStart_4739505 : Nat := 118140960795 + 4739505 * 2 ^ 59
def prefixEnd_4739505 : Nat := 4983230072969 + 3 ^ 40 * 4739505 * 2
def baseEnd_4739505 : Nat := 270404903265287155398991

theorem tailTrace_4739505 : CollatzResearch.WordTrace tailWord_4739505 prefixEnd_4739505 270404903265287155398991 := by
  unfold tailWord_4739505
  simp only [CollatzResearch.WordTrace]
  refine ⟨172863948694590302856059969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115242632463060201904039979 172863948694590302856059969)
  ·
    refine ⟨129647961520942727142044977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172863948694590302856059969 129647961520942727142044977)
    ·
      refine ⟨97235971140707045356533733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129647961520942727142044977 97235971140707045356533733)
      ·
        refine ⟨18231744588882571004350075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97235971140707045356533733 18231744588882571004350075)
        ·
          refine ⟨27347616883323856506525113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18231744588882571004350075 27347616883323856506525113)
          ·
            refine ⟨20510712662492892379893835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27347616883323856506525113 20510712662492892379893835)
            ·
              refine ⟨30766068993739338569840753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20510712662492892379893835 30766068993739338569840753)
              ·
                refine ⟨23074551745304503927380565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30766068993739338569840753 23074551745304503927380565)
                ·
                  refine ⟨270404903265287155398991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23074551745304503927380565 270404903265287155398991)
                  ·
                    rfl

theorem cell23_4739505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_4739505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739505 prefixEnd_4739505 := by exact prefixLift 4739505
  have htrace : WordTrace (prefixWord ++ tailWord_4739505) baseStart_4739505 baseEnd_4739505 := by
    simpa [prefixWord, tailWord_4739505, baseEnd_4739505] using wordTrace_append hprefix tailTrace_4739505
  have hstable : (prefixWord ++ tailWord_4739505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739505).length < 2 ^ (prefixWord ++ tailWord_4739505).sum := by decide
  have hdescent : baseEnd_4739505 < baseStart_4739505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739535 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 3, 5]
def baseStart_4739535 : Nat := 118140960795 + 4739535 * 2 ^ 59
def prefixEnd_4739535 : Nat := 4983230072969 + 3 ^ 40 * 4739535 * 2
def baseEnd_4739535 : Nat := 811219844602406427071927

theorem tailTrace_4739535 : CollatzResearch.WordTrace tailWord_4739535 prefixEnd_4739535 811219844602406427071927 := by
  unfold tailWord_4739535
  simp only [CollatzResearch.WordTrace]
  refine ⟨172865042884481617979652059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115243361922987745319768039 172865042884481617979652059)
  ·
    refine ⟨259297564326722426969478089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172865042884481617979652059 259297564326722426969478089)
    ·
      refine ⟨194473173245041820227108567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259297564326722426969478089 194473173245041820227108567)
      ·
        refine ⟨291709759867562730340662851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194473173245041820227108567 291709759867562730340662851)
        ·
          refine ⟨437564639801344095510994277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291709759867562730340662851 437564639801344095510994277)
          ·
            refine ⟨82043369962752017908311427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 437564639801344095510994277 82043369962752017908311427)
            ·
              refine ⟨123065054944128026862467141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82043369962752017908311427 123065054944128026862467141)
              ·
                refine ⟨23074697802024005036712589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123065054944128026862467141 23074697802024005036712589)
                ·
                  refine ⟨8653011675759001888767221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23074697802024005036712589 8653011675759001888767221)
                  ·
                    refine ⟨811219844602406427071927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8653011675759001888767221 811219844602406427071927)
                    ·
                      rfl

theorem cell23_4739535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_4739535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739535 prefixEnd_4739535 := by exact prefixLift 4739535
  have htrace : WordTrace (prefixWord ++ tailWord_4739535) baseStart_4739535 baseEnd_4739535 := by
    simpa [prefixWord, tailWord_4739535, baseEnd_4739535] using wordTrace_append hprefix tailTrace_4739535
  have hstable : (prefixWord ++ tailWord_4739535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739535).length < 2 ^ (prefixWord ++ tailWord_4739535).sum := by decide
  have hdescent : baseEnd_4739535 < baseStart_4739535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739549 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4739549 : Nat := 118140960795 + 4739549 * 2 ^ 59
def prefixEnd_4739549 : Nat := 4983230072969 + 3 ^ 40 * 4739549 * 2
def baseEnd_4739549 : Nat := 2433666722536382226440717

theorem tailTrace_4739549 : CollatzResearch.WordTrace tailWord_4739549 prefixEnd_4739549 2433666722536382226440717 := by
  unfold tailWord_4739549
  simp only [CollatzResearch.WordTrace]
  refine ⟨172865553506430898370661701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115243702337620598913774467 172865553506430898370661701)
  ·
    refine ⟨32412291282455793444499069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172865553506430898370661701 32412291282455793444499069)
    ·
      refine ⟨12154609230920922541687151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32412291282455793444499069 12154609230920922541687151)
      ·
        refine ⟨18231913846381383812530727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12154609230920922541687151 18231913846381383812530727)
        ·
          refine ⟨27347870769572075718796091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18231913846381383812530727 27347870769572075718796091)
          ·
            refine ⟨41021806154358113578194137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27347870769572075718796091 41021806154358113578194137)
            ·
              refine ⟨30766354615768585183645603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41021806154358113578194137 30766354615768585183645603)
              ·
                refine ⟨46149531923652877775468405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30766354615768585183645603 46149531923652877775468405)
                ·
                  refine ⟨4326518617842457291450163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46149531923652877775468405 4326518617842457291450163)
                  ·
                    refine ⟨6489777926763685937175245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4326518617842457291450163 6489777926763685937175245)
                    ·
                      refine ⟨2433666722536382226440717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489777926763685937175245 2433666722536382226440717)
                      ·
                        rfl

theorem cell23_4739549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4739549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739549 prefixEnd_4739549 := by exact prefixLift 4739549
  have htrace : WordTrace (prefixWord ++ tailWord_4739549) baseStart_4739549 baseEnd_4739549 := by
    simpa [prefixWord, tailWord_4739549, baseEnd_4739549] using wordTrace_append hprefix tailTrace_4739549
  have hstable : (prefixWord ++ tailWord_4739549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739549).length < 2 ^ (prefixWord ++ tailWord_4739549).sum := by decide
  have hdescent : baseEnd_4739549 < baseStart_4739549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739569 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 1, 5]
def baseStart_4739569 : Nat := 118140960795 + 4739569 * 2 ^ 59
def prefixEnd_4739569 : Nat := 4983230072969 + 3 ^ 40 * 4739569 * 2
def baseEnd_4739569 : Nat := 811225664049824049396875

theorem tailTrace_4739569 : CollatzResearch.WordTrace tailWord_4739569 prefixEnd_4739569 811225664049824049396875 := by
  unfold tailWord_4739569
  simp only [CollatzResearch.WordTrace]
  refine ⟨172866282966358441786389761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115244188644238961190926507 172866282966358441786389761)
  ·
    refine ⟨129649712224768831339792321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172866282966358441786389761 129649712224768831339792321)
    ·
      refine ⟨97237284168576623504844241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129649712224768831339792321 97237284168576623504844241)
      ·
        refine ⟨72927963126432467628633181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97237284168576623504844241 72927963126432467628633181)
        ·
          refine ⟨27347986172412175360737443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72927963126432467628633181 27347986172412175360737443)
          ·
            refine ⟨41021979258618263041106165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27347986172412175360737443 41021979258618263041106165)
            ·
              refine ⟨3845810555495462160103703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41021979258618263041106165 3845810555495462160103703)
              ·
                refine ⟨5768715833243193240155555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845810555495462160103703 5768715833243193240155555)
                ·
                  refine ⟨8653073749864789860233333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768715833243193240155555 8653073749864789860233333)
                  ·
                    refine ⟨811225664049824049396875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8653073749864789860233333 811225664049824049396875)
                    ·
                      rfl

theorem cell23_4739569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_4739569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739569 prefixEnd_4739569 := by exact prefixLift 4739569
  have htrace : WordTrace (prefixWord ++ tailWord_4739569) baseStart_4739569 baseEnd_4739569 := by
    simpa [prefixWord, tailWord_4739569, baseEnd_4739569] using wordTrace_append hprefix tailTrace_4739569
  have hstable : (prefixWord ++ tailWord_4739569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739569).length < 2 ^ (prefixWord ++ tailWord_4739569).sum := by decide
  have hdescent : baseEnd_4739569 < baseStart_4739569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739620 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_4739620 : Nat := 118140960795 + 4739620 * 2 ^ 59
def prefixEnd_4739620 : Nat := 4983230072969 + 3 ^ 40 * 4739620 * 2
def baseEnd_4739620 : Nat := 811234393220950482884297

theorem tailTrace_4739620 : CollatzResearch.WordTrace tailWord_4739620 prefixEnd_4739620 811234393220950482884297 := by
  unfold tailWord_4739620
  simp only [CollatzResearch.WordTrace]
  refine ⟨86434071544586838748248157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115245428726115784997664209 86434071544586838748248157)
  ·
    refine ⟨32412776829220064530593059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86434071544586838748248157 32412776829220064530593059)
    ·
      refine ⟨48619165243830096795889589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32412776829220064530593059 48619165243830096795889589)
      ·
        refine ⟨4558046741609071574614649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48619165243830096795889589 4558046741609071574614649)
        ·
          refine ⟨3418535056206803680960987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4558046741609071574614649 3418535056206803680960987)
          ·
            refine ⟨5127802584310205521441481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418535056206803680960987 5127802584310205521441481)
            ·
              refine ⟨3845851938232654141081111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5127802584310205521441481 3845851938232654141081111)
              ·
                refine ⟨5768777907348981211621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845851938232654141081111 5768777907348981211621667)
                ·
                  refine ⟨8653166861023471817432501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768777907348981211621667 8653166861023471817432501)
                  ·
                    refine ⟨811234393220950482884297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8653166861023471817432501 811234393220950482884297)
                    ·
                      rfl

theorem cell23_4739620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_4739620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739620 prefixEnd_4739620 := by exact prefixLift 4739620
  have htrace : WordTrace (prefixWord ++ tailWord_4739620) baseStart_4739620 baseEnd_4739620 := by
    simpa [prefixWord, tailWord_4739620, baseEnd_4739620] using wordTrace_append hprefix tailTrace_4739620
  have hstable : (prefixWord ++ tailWord_4739620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739620).length < 2 ^ (prefixWord ++ tailWord_4739620).sum := by decide
  have hdescent : baseEnd_4739620 < baseStart_4739620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739623 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4739623 : Nat := 118140960795 + 4739623 * 2 ^ 59
def prefixEnd_4739623 : Nat := 4983230072969 + 3 ^ 40 * 4739623 * 2
def baseEnd_4739623 : Nat := 2433704720104814936915377

theorem tailTrace_4739623 : CollatzResearch.WordTrace tailWord_4739623 prefixEnd_4739623 2433704720104814936915377 := by
  unfold tailWord_4739623
  simp only [CollatzResearch.WordTrace]
  refine ⟨172868252508162809008855523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115245501672108539339237015 172868252508162809008855523)
  ·
    refine ⟨259302378762244213513283285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172868252508162809008855523 259302378762244213513283285)
    ·
      refine ⟨6077399502240098754217577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 259302378762244213513283285 6077399502240098754217577)
      ·
        refine ⟨4558049626680074065663183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6077399502240098754217577 4558049626680074065663183)
        ·
          refine ⟨6837074440020111098494775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558049626680074065663183 6837074440020111098494775)
          ·
            refine ⟨10255611660030166647742163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6837074440020111098494775 10255611660030166647742163)
            ·
              refine ⟨15383417490045249971613245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10255611660030166647742163 15383417490045249971613245)
              ·
                refine ⟨5768781558766968739354967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15383417490045249971613245 5768781558766968739354967)
                ·
                  refine ⟨8653172338150453109032451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768781558766968739354967 8653172338150453109032451)
                  ·
                    refine ⟨12979758507225679663548677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8653172338150453109032451 12979758507225679663548677)
                    ·
                      refine ⟨2433704720104814936915377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12979758507225679663548677 2433704720104814936915377)
                      ·
                        rfl

theorem cell23_4739623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4739623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739623 prefixEnd_4739623 := by exact prefixLift 4739623
  have htrace : WordTrace (prefixWord ++ tailWord_4739623) baseStart_4739623 baseEnd_4739623 := by
    simpa [prefixWord, tailWord_4739623, baseEnd_4739623] using wordTrace_append hprefix tailTrace_4739623
  have hstable : (prefixWord ++ tailWord_4739623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739623).length < 2 ^ (prefixWord ++ tailWord_4739623).sum := by decide
  have hdescent : baseEnd_4739623 < baseStart_4739623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739626 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4739626 : Nat := 118140960795 + 4739626 * 2 ^ 59
def prefixEnd_4739626 : Nat := 4983230072969 + 3 ^ 40 * 4739626 * 2
def baseEnd_4739626 : Nat := 2433706260546778425177863

theorem tailTrace_4739626 : CollatzResearch.WordTrace tailWord_4739626 prefixEnd_4739626 2433706260546778425177863 := by
  unfold tailWord_4739626
  simp only [CollatzResearch.WordTrace]
  refine ⟨43217090481787985130303683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115245574618101293680809821 43217090481787985130303683)
  ·
    refine ⟨64825635722681977695455525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43217090481787985130303683 64825635722681977695455525)
    ·
      refine ⟨12154806698002870817897911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64825635722681977695455525 12154806698002870817897911)
      ·
        refine ⟨18232210047004306226846867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12154806698002870817897911 18232210047004306226846867)
        ·
          refine ⟨27348315070506459340270301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18232210047004306226846867 27348315070506459340270301)
          ·
            refine ⟨10255618151439922252601363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27348315070506459340270301 10255618151439922252601363)
            ·
              refine ⟨15383427227159883378902045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10255618151439922252601363 15383427227159883378902045)
              ·
                refine ⟨5768785210184956267088267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15383427227159883378902045 5768785210184956267088267)
                ·
                  refine ⟨8653177815277434400632401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768785210184956267088267 8653177815277434400632401)
                  ·
                    refine ⟨6489883361458075800474301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8653177815277434400632401 6489883361458075800474301)
                    ·
                      refine ⟨2433706260546778425177863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489883361458075800474301 2433706260546778425177863)
                      ·
                        rfl

theorem cell23_4739626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4739626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739626 prefixEnd_4739626 := by exact prefixLift 4739626
  have htrace : WordTrace (prefixWord ++ tailWord_4739626) baseStart_4739626 baseEnd_4739626 := by
    simpa [prefixWord, tailWord_4739626, baseEnd_4739626] using wordTrace_append hprefix tailTrace_4739626
  have hstable : (prefixWord ++ tailWord_4739626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739626).length < 2 ^ (prefixWord ++ tailWord_4739626).sum := by decide
  have hdescent : baseEnd_4739626 < baseStart_4739626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739639 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_4739639 : Nat := 118140960795 + 4739639 * 2 ^ 59
def prefixEnd_4739639 : Nat := 4983230072969 + 3 ^ 40 * 4739639 * 2
def baseEnd_4739639 : Nat := 2433712935795286874315303

theorem tailTrace_4739639 : CollatzResearch.WordTrace tailWord_4739639 prefixEnd_4739639 2433712935795286874315303 := by
  unfold tailWord_4739639
  simp only [CollatzResearch.WordTrace]
  refine ⟨172868836076104843741437971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115245890717403229160958647 172868836076104843741437971)
  ·
    refine ⟨259303254114157265612156957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172868836076104843741437971 259303254114157265612156957)
    ·
      refine ⟨97238720292808974604558859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259303254114157265612156957 97238720292808974604558859)
      ·
        refine ⟨145858080439213461906838289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97238720292808974604558859 145858080439213461906838289)
        ·
          refine ⟨109393560329410096430128717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145858080439213461906838289 109393560329410096430128717)
          ·
            refine ⟨41022585123528786161298269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109393560329410096430128717 41022585123528786161298269)
            ·
              refine ⟨15383469421323294810486851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41022585123528786161298269 15383469421323294810486851)
              ·
                refine ⟨23075204131984942215730277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15383469421323294810486851 23075204131984942215730277)
                ·
                  refine ⟨4326600774747176665449427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23075204131984942215730277 4326600774747176665449427)
                  ·
                    refine ⟨6489901162120764998174141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4326600774747176665449427 6489901162120764998174141)
                    ·
                      refine ⟨2433712935795286874315303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6489901162120764998174141 2433712935795286874315303)
                      ·
                        rfl

theorem cell23_4739639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_4739639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739639 prefixEnd_4739639 := by exact prefixLift 4739639
  have htrace : WordTrace (prefixWord ++ tailWord_4739639) baseStart_4739639 baseEnd_4739639 := by
    simpa [prefixWord, tailWord_4739639, baseEnd_4739639] using wordTrace_append hprefix tailTrace_4739639
  have hstable : (prefixWord ++ tailWord_4739639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739639).length < 2 ^ (prefixWord ++ tailWord_4739639).sum := by decide
  have hdescent : baseEnd_4739639 < baseStart_4739639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739662 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_4739662 : Nat := 118140960795 + 4739662 * 2 ^ 59
def prefixEnd_4739662 : Nat := 4983230072969 + 3 ^ 40 * 4739662 * 2
def baseEnd_4739662 : Nat := 2433724745850340284327697

theorem tailTrace_4739662 : CollatzResearch.WordTrace tailWord_4739662 prefixEnd_4739662 2433724745850340284327697 := by
  unfold tailWord_4739662
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608709369377689833690655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115246449970014345779683493 21608709369377689833690655)
  ·
    refine ⟨32413064054066534750535983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21608709369377689833690655 32413064054066534750535983)
    ·
      refine ⟨48619596081099802125803975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32413064054066534750535983 48619596081099802125803975)
      ·
        refine ⟨72929394121649703188705963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48619596081099802125803975 72929394121649703188705963)
        ·
          refine ⟨109394091182474554783058945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72929394121649703188705963 109394091182474554783058945)
          ·
            refine ⟨82045568386855916087294209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109394091182474554783058945 82045568386855916087294209)
            ·
              refine ⟨61534176290141937065470657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82045568386855916087294209 61534176290141937065470657)
              ·
                refine ⟨46150632217606452799102993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61534176290141937065470657 46150632217606452799102993)
                ·
                  refine ⟨34612974163204839599327245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46150632217606452799102993 34612974163204839599327245)
                  ·
                    refine ⟨12979865311201814849747717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34612974163204839599327245 12979865311201814849747717)
                    ·
                      refine ⟨2433724745850340284327697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12979865311201814849747717 2433724745850340284327697)
                      ·
                        rfl

theorem cell23_4739662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_4739662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739662 prefixEnd_4739662 := by exact prefixLift 4739662
  have htrace : WordTrace (prefixWord ++ tailWord_4739662) baseStart_4739662 baseEnd_4739662 := by
    simpa [prefixWord, tailWord_4739662, baseEnd_4739662] using wordTrace_append hprefix tailTrace_4739662
  have hstable : (prefixWord ++ tailWord_4739662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739662).length < 2 ^ (prefixWord ++ tailWord_4739662).sum := by decide
  have hdescent : baseEnd_4739662 < baseStart_4739662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739679 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 1, 4, 2]
def baseStart_4739679 : Nat := 118140960795 + 4739679 * 2 ^ 59
def prefixEnd_4739679 : Nat := 4983230072969 + 3 ^ 40 * 4739679 * 2
def baseEnd_4739679 : Nat := 2433733475021466717815119

theorem tailTrace_4739679 : CollatzResearch.WordTrace tailWord_4739679 prefixEnd_4739679 2433733475021466717815119 := by
  unfold tailWord_4739679
  simp only [CollatzResearch.WordTrace]
  refine ⟨172870294995959930572894091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115246863330639953715262727 172870294995959930572894091)
  ·
    refine ⟨259305442493939895859341137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172870294995959930572894091 259305442493939895859341137)
    ·
      refine ⟨194479081870454921894505853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259305442493939895859341137 194479081870454921894505853)
      ·
        refine ⟨72929655701420595710439695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194479081870454921894505853 72929655701420595710439695)
        ·
          refine ⟨109394483552130893565659543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72929655701420595710439695 109394483552130893565659543)
          ·
            refine ⟨164091725328196340348489315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109394483552130893565659543 164091725328196340348489315)
            ·
              refine ⟨246137587992294510522733973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164091725328196340348489315 246137587992294510522733973)
              ·
                refine ⟨11537699437138805180753155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 246137587992294510522733973 11537699437138805180753155)
                ·
                  refine ⟨17306549155708207771129733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11537699437138805180753155 17306549155708207771129733)
                  ·
                    refine ⟨3244977966695288957086825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17306549155708207771129733 3244977966695288957086825)
                    ·
                      refine ⟨2433733475021466717815119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3244977966695288957086825 2433733475021466717815119)
                      ·
                        rfl

theorem cell23_4739679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_4739679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739679 prefixEnd_4739679 := by exact prefixLift 4739679
  have htrace : WordTrace (prefixWord ++ tailWord_4739679) baseStart_4739679 baseEnd_4739679 := by
    simpa [prefixWord, tailWord_4739679, baseEnd_4739679] using wordTrace_append hprefix tailTrace_4739679
  have hstable : (prefixWord ++ tailWord_4739679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739679).length < 2 ^ (prefixWord ++ tailWord_4739679).sum := by decide
  have hdescent : baseEnd_4739679 < baseStart_4739679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739692 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_4739692 : Nat := 118140960795 + 4739692 * 2 ^ 59
def prefixEnd_4739692 : Nat := 4983230072969 + 3 ^ 40 * 4739692 * 2
def baseEnd_4739692 : Nat := 2433740150269975166952559

theorem tailTrace_4739692 : CollatzResearch.WordTrace tailWord_4739692 prefixEnd_4739692 2433740150269975166952559 := by
  unfold tailWord_4739692
  simp only [CollatzResearch.WordTrace]
  refine ⟨86435384572456416896558665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115247179429941889195411553 86435384572456416896558665)
  ·
    refine ⟨64826538429342312672418999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86435384572456416896558665 64826538429342312672418999)
    ·
      refine ⟨97239807644013469008628499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64826538429342312672418999 97239807644013469008628499)
      ·
        refine ⟨145859711466020203512942749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97239807644013469008628499 145859711466020203512942749)
        ·
          refine ⟨54697391799757576317353531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145859711466020203512942749 54697391799757576317353531)
          ·
            refine ⟨82046087699636364476030297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54697391799757576317353531 82046087699636364476030297)
            ·
              refine ⟨61534565774727273357022723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82046087699636364476030297 61534565774727273357022723)
              ·
                refine ⟨92301848662090910035534085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61534565774727273357022723 92301848662090910035534085)
                ·
                  refine ⟨17306596624142045631662641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92301848662090910035534085 17306596624142045631662641)
                  ·
                    refine ⟨12979947468106534223746981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17306596624142045631662641 12979947468106534223746981)
                    ·
                      refine ⟨2433740150269975166952559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12979947468106534223746981 2433740150269975166952559)
                      ·
                        rfl

theorem cell23_4739692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_4739692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739692 prefixEnd_4739692 := by exact prefixLift 4739692
  have htrace : WordTrace (prefixWord ++ tailWord_4739692) baseStart_4739692 baseEnd_4739692 := by
    simpa [prefixWord, tailWord_4739692, baseEnd_4739692] using wordTrace_append hprefix tailTrace_4739692
  have hstable : (prefixWord ++ tailWord_4739692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739692).length < 2 ^ (prefixWord ++ tailWord_4739692).sum := by decide
  have hdescent : baseEnd_4739692 < baseStart_4739692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739713 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_4739713 : Nat := 118140960795 + 4739713 * 2 ^ 59
def prefixEnd_4739713 : Nat := 4983230072969 + 3 ^ 40 * 4739713 * 2
def baseEnd_4739713 : Nat := 2433750933363719584789963

theorem tailTrace_4739713 : CollatzResearch.WordTrace tailWord_4739713 prefixEnd_4739713 2433750933363719584789963 := by
  unfold tailWord_4739713
  simp only [CollatzResearch.WordTrace]
  refine ⟨172871535077836754379631793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115247690051891169586421195 172871535077836754379631793)
  ·
    refine ⟨129653651308377565784723845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172871535077836754379631793 129653651308377565784723845)
    ·
      refine ⟨24310059620320793584635721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129653651308377565784723845 24310059620320793584635721)
      ·
        refine ⟨18232544715240595188476791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24310059620320793584635721 18232544715240595188476791)
        ·
          refine ⟨27348817072860892782715187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18232544715240595188476791 27348817072860892782715187)
          ·
            refine ⟨41023225609291339174072781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27348817072860892782715187 41023225609291339174072781)
            ·
              refine ⟨15383709603484252190277293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41023225609291339174072781 15383709603484252190277293)
              ·
                refine ⟨5768891101306594571353985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15383709603484252190277293 5768891101306594571353985)
                ·
                  refine ⟨4326668325979945928515489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768891101306594571353985 4326668325979945928515489)
                  ·
                    refine ⟨3245001244484959446386617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326668325979945928515489 3245001244484959446386617)
                    ·
                      refine ⟨2433750933363719584789963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245001244484959446386617 2433750933363719584789963)
                      ·
                        rfl

theorem cell23_4739713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_4739713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739713 prefixEnd_4739713 := by exact prefixLift 4739713
  have htrace : WordTrace (prefixWord ++ tailWord_4739713) baseStart_4739713 baseEnd_4739713 := by
    simpa [prefixWord, tailWord_4739713, baseEnd_4739713] using wordTrace_append hprefix tailTrace_4739713
  have hstable : (prefixWord ++ tailWord_4739713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739713).length < 2 ^ (prefixWord ++ tailWord_4739713).sum := by decide
  have hdescent : baseEnd_4739713 < baseStart_4739713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739762 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_4739762 : Nat := 118140960795 + 4739762 * 2 ^ 59
def prefixEnd_4739762 : Nat := 4983230072969 + 3 ^ 40 * 4739762 * 2
def baseEnd_4739762 : Nat := 811258697971929964359079

theorem tailTrace_4739762 : CollatzResearch.WordTrace tailWord_4739762 prefixEnd_4739762 811258697971929964359079 := by
  unfold tailWord_4739762
  simp only [CollatzResearch.WordTrace]
  refine ⟨43218330563664808937041385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115248881503106157165443693 43218330563664808937041385)
  ·
    refine ⟨32413747922748606702781039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43218330563664808937041385 32413747922748606702781039)
    ·
      refine ⟨48620621884122910054171559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32413747922748606702781039 48620621884122910054171559)
      ·
        refine ⟨72930932826184365081257339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48620621884122910054171559 72930932826184365081257339)
        ·
          refine ⟨109396399239276547621886009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72930932826184365081257339 109396399239276547621886009)
          ·
            refine ⟨82047299429457410716414507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109396399239276547621886009 82047299429457410716414507)
            ·
              refine ⟨123070949144186116074621761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82047299429457410716414507 123070949144186116074621761)
              ·
                refine ⟨92303211858139587055966321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123070949144186116074621761 92303211858139587055966321)
                ·
                  refine ⟨69227408893604690291974741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92303211858139587055966321 69227408893604690291974741)
                  ·
                    refine ⟨811258697971929964359079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69227408893604690291974741 811258697971929964359079)
                    ·
                      rfl

theorem cell23_4739762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_4739762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739762 prefixEnd_4739762 := by exact prefixLift 4739762
  have htrace : WordTrace (prefixWord ++ tailWord_4739762) baseStart_4739762 baseEnd_4739762 := by
    simpa [prefixWord, tailWord_4739762, baseEnd_4739762] using wordTrace_append hprefix tailTrace_4739762
  have hstable : (prefixWord ++ tailWord_4739762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739762).length < 2 ^ (prefixWord ++ tailWord_4739762).sum := by decide
  have hdescent : baseEnd_4739762 < baseStart_4739762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739786 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_4739786 : Nat := 118140960795 + 4739786 * 2 ^ 59
def prefixEnd_4739786 : Nat := 4983230072969 + 3 ^ 40 * 4739786 * 2
def baseEnd_4739786 : Nat := 2433788417451497799177127

theorem tailTrace_4739786 : CollatzResearch.WordTrace tailWord_4739786 prefixEnd_4739786 2433788417451497799177127 := by
  unfold tailWord_4739786
  simp only [CollatzResearch.WordTrace]
  refine ⟨43218549401643071961759803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115249465071048191898026141 43218549401643071961759803)
  ·
    refine ⟨64827824102464607942639705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43218549401643071961759803 64827824102464607942639705)
    ·
      refine ⟨48620868076848455956979779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64827824102464607942639705 48620868076848455956979779)
      ·
        refine ⟨72931302115272683935469669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48620868076848455956979779 72931302115272683935469669)
        ·
          refine ⟨13674619146613628237900563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72931302115272683935469669 13674619146613628237900563)
          ·
            refine ⟨20511928719920442356850845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13674619146613628237900563 20511928719920442356850845)
            ·
              refine ⟨7691973269970165883819067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20511928719920442356850845 7691973269970165883819067)
              ·
                refine ⟨11537959904955248825728601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7691973269970165883819067 11537959904955248825728601)
                ·
                  refine ⟨8653469928716436619296451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11537959904955248825728601 8653469928716436619296451)
                  ·
                    refine ⟨12980204893074654928944677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8653469928716436619296451 12980204893074654928944677)
                    ·
                      refine ⟨2433788417451497799177127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12980204893074654928944677 2433788417451497799177127)
                      ·
                        rfl

theorem cell23_4739786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_4739786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739786 prefixEnd_4739786 := by exact prefixLift 4739786
  have htrace : WordTrace (prefixWord ++ tailWord_4739786) baseStart_4739786 baseEnd_4739786 := by
    simpa [prefixWord, tailWord_4739786, baseEnd_4739786] using wordTrace_append hprefix tailTrace_4739786
  have hstable : (prefixWord ++ tailWord_4739786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739786).length < 2 ^ (prefixWord ++ tailWord_4739786).sum := by decide
  have hdescent : baseEnd_4739786 < baseStart_4739786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739809 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 8]
def baseStart_4739809 : Nat := 118140960795 + 4739809 * 2 ^ 59
def prefixEnd_4739809 : Nat := 4983230072969 + 3 ^ 40 * 4739809 * 2
def baseEnd_4739809 : Nat := 270422247500727912132169

theorem tailTrace_4739809 : CollatzResearch.WordTrace tailWord_4739809 prefixEnd_4739809 270422247500727912132169 := by
  unfold tailWord_4739809
  simp only [CollatzResearch.WordTrace]
  refine ⟨172875036485488962775126481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115250024323659308516750987 172875036485488962775126481)
  ·
    refine ⟨129656277364116722081344861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172875036485488962775126481 129656277364116722081344861)
    ·
      refine ⟨48621104011543770780504323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129656277364116722081344861 48621104011543770780504323)
      ·
        refine ⟨72931656017315656170756485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48621104011543770780504323 72931656017315656170756485)
        ·
          refine ⟨13674685503246685532016841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72931656017315656170756485 13674685503246685532016841)
          ·
            refine ⟨10256014127435014149012631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13674685503246685532016841 10256014127435014149012631)
            ·
              refine ⟨15384021191152521223518947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10256014127435014149012631 15384021191152521223518947)
              ·
                refine ⟨23076031786728781835278421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15384021191152521223518947 23076031786728781835278421)
                ·
                  refine ⟨270422247500727912132169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23076031786728781835278421 270422247500727912132169)
                  ·
                    rfl

theorem cell23_4739809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_4739809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739809 prefixEnd_4739809 := by exact prefixLift 4739809
  have htrace : WordTrace (prefixWord ++ tailWord_4739809) baseStart_4739809 baseEnd_4739809 := by
    simpa [prefixWord, tailWord_4739809, baseEnd_4739809] using wordTrace_append hprefix tailTrace_4739809
  have hstable : (prefixWord ++ tailWord_4739809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739809).length < 2 ^ (prefixWord ++ tailWord_4739809).sum := by decide
  have hdescent : baseEnd_4739809 < baseStart_4739809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739813 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_4739813 : Nat := 118140960795 + 4739813 * 2 ^ 59
def prefixEnd_4739813 : Nat := 4983230072969 + 3 ^ 40 * 4739813 * 2
def baseEnd_4739813 : Nat := 811267427143056397846501

theorem tailTrace_4739813 : CollatzResearch.WordTrace tailWord_4739813 prefixEnd_4739813 811267427143056397846501 := by
  unfold tailWord_4739813
  simp only [CollatzResearch.WordTrace]
  refine ⟨172875182377474471458272093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115250121584982980972181395 172875182377474471458272093)
  ·
    refine ⟨64828193391552926796852035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172875182377474471458272093 64828193391552926796852035)
    ·
      refine ⟨97242290087329390195278053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64828193391552926796852035 97242290087329390195278053)
      ·
        refine ⟨18232929391374260661614635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97242290087329390195278053 18232929391374260661614635)
        ·
          refine ⟨27349394087061390992421953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18232929391374260661614635 27349394087061390992421953)
          ·
            refine ⟨20512045565296043244316465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27349394087061390992421953 20512045565296043244316465)
            ·
              refine ⟨15384034173972032433237349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20512045565296043244316465 15384034173972032433237349)
              ·
                refine ⟨2884506407619756081232003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15384034173972032433237349 2884506407619756081232003)
                ·
                  refine ⟨4326759611429634121848005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884506407619756081232003 4326759611429634121848005)
                  ·
                    refine ⟨811267427143056397846501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4326759611429634121848005 811267427143056397846501)
                    ·
                      rfl

theorem cell23_4739813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_4739813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739813 prefixEnd_4739813 := by exact prefixLift 4739813
  have htrace : WordTrace (prefixWord ++ tailWord_4739813) baseStart_4739813 baseEnd_4739813 := by
    simpa [prefixWord, tailWord_4739813, baseEnd_4739813] using wordTrace_append hprefix tailTrace_4739813
  have hstable : (prefixWord ++ tailWord_4739813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739813).length < 2 ^ (prefixWord ++ tailWord_4739813).sum := by decide
  have hdescent : baseEnd_4739813 < baseStart_4739813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739889 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_4739889 : Nat := 118140960795 + 4739889 * 2 ^ 59
def prefixEnd_4739889 : Nat := 4983230072969 + 3 ^ 40 * 4739889 * 2
def baseEnd_4739889 : Nat := 2433841305958910896189153

theorem tailTrace_4739889 : CollatzResearch.WordTrace tailWord_4739889 prefixEnd_4739889 2433841305958910896189153 := by
  unfold tailWord_4739889
  simp only [CollatzResearch.WordTrace]
  refine ⟨172877954325199136438038721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115251969550132757625359147 172877954325199136438038721)
  ·
    refine ⟨129658465743899352328529041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172877954325199136438038721 129658465743899352328529041)
    ·
      refine ⟨97243849307924514246396781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129658465743899352328529041 97243849307924514246396781)
      ·
        refine ⟨36466443490471692842398793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97243849307924514246396781 36466443490471692842398793)
        ·
          refine ⟨27349832617853769631799095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36466443490471692842398793 27349832617853769631799095)
          ·
            refine ⟨41024748926780654447698643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27349832617853769631799095 41024748926780654447698643)
            ·
              refine ⟨61537123390170981671547965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41024748926780654447698643 61537123390170981671547965)
              ·
                refine ⟨23076421271314118126830487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61537123390170981671547965 23076421271314118126830487)
                ·
                  refine ⟨34614631906971177190245731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23076421271314118126830487 34614631906971177190245731)
                  ·
                    refine ⟨51921947860456765785368597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34614631906971177190245731 51921947860456765785368597)
                    ·
                      refine ⟨2433841305958910896189153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51921947860456765785368597 2433841305958910896189153)
                      ·
                        rfl

theorem cell23_4739889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_4739889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739889 prefixEnd_4739889 := by exact prefixLift 4739889
  have htrace : WordTrace (prefixWord ++ tailWord_4739889) baseStart_4739889 baseEnd_4739889 := by
    simpa [prefixWord, tailWord_4739889, baseEnd_4739889] using wordTrace_append hprefix tailTrace_4739889
  have hstable : (prefixWord ++ tailWord_4739889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739889).length < 2 ^ (prefixWord ++ tailWord_4739889).sum := by decide
  have hdescent : baseEnd_4739889 < baseStart_4739889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739893 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_4739893 : Nat := 118140960795 + 4739893 * 2 ^ 59
def prefixEnd_4739893 : Nat := 4983230072969 + 3 ^ 40 * 4739893 * 2
def baseEnd_4739893 : Nat := 2433843359881528880539135

theorem tailTrace_4739893 : CollatzResearch.WordTrace tailWord_4739893 prefixEnd_4739893 2433843359881528880539135 := by
  unfold tailWord_4739893
  simp only [CollatzResearch.WordTrace]
  refine ⟨172878100217184645121184333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115252066811456430080789555 172878100217184645121184333)
  ·
    refine ⟨64829287581444241920444125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172878100217184645121184333 64829287581444241920444125)
    ·
      refine ⟨24310982843041590720166547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64829287581444241920444125 24310982843041590720166547)
      ·
        refine ⟨36466474264562386080249821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24310982843041590720166547 36466474264562386080249821)
        ·
          refine ⟨13674927849210894780093683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36466474264562386080249821 13674927849210894780093683)
          ·
            refine ⟨20512391773816342170140525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13674927849210894780093683 20512391773816342170140525)
            ·
              refine ⟨7692146915181128313802697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20512391773816342170140525 7692146915181128313802697)
              ·
                refine ⟨5769110186385846235352023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7692146915181128313802697 5769110186385846235352023)
                ·
                  refine ⟨8653665279578769353028035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5769110186385846235352023 8653665279578769353028035)
                  ·
                    refine ⟨12980497919368154029542053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8653665279578769353028035 12980497919368154029542053)
                    ·
                      refine ⟨2433843359881528880539135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12980497919368154029542053 2433843359881528880539135)
                      ·
                        rfl

theorem cell23_4739893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_4739893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739893 prefixEnd_4739893 := by exact prefixLift 4739893
  have htrace : WordTrace (prefixWord ++ tailWord_4739893) baseStart_4739893 baseEnd_4739893 := by
    simpa [prefixWord, tailWord_4739893, baseEnd_4739893] using wordTrace_append hprefix tailTrace_4739893
  have hstable : (prefixWord ++ tailWord_4739893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739893).length < 2 ^ (prefixWord ++ tailWord_4739893).sum := by decide
  have hdescent : baseEnd_4739893 < baseStart_4739893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739896 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_4739896 : Nat := 118140960795 + 4739896 * 2 ^ 59
def prefixEnd_4739896 : Nat := 4983230072969 + 3 ^ 40 * 4739896 * 2
def baseEnd_4739896 : Nat := 2433844900323492368801621

theorem tailTrace_4739896 : CollatzResearch.WordTrace tailWord_4739896 prefixEnd_4739896 2433844900323492368801621 := by
  unfold tailWord_4739896
  simp only [CollatzResearch.WordTrace]
  refine ⟨86439104818086888316771771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115252139757449184422362361 86439104818086888316771771)
  ·
    refine ⟨129658657227130332475157657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86439104818086888316771771 129658657227130332475157657)
    ·
      refine ⟨97243992920347749356368243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129658657227130332475157657 97243992920347749356368243)
      ·
        refine ⟨145865989380521624034552365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97243992920347749356368243 145865989380521624034552365)
        ·
          refine ⟨54699746017695609012957137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145865989380521624034552365 54699746017695609012957137)
          ·
            refine ⟨41024809513271706759717853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54699746017695609012957137 41024809513271706759717853)
            ·
              refine ⟨15384303567476890034894195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41024809513271706759717853 15384303567476890034894195)
              ·
                refine ⟨23076455351215335052341293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15384303567476890034894195 23076455351215335052341293)
                ·
                  refine ⟨8653670756705750644627985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23076455351215335052341293 8653670756705750644627985)
                  ·
                    refine ⟨6490253067529312983470989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8653670756705750644627985 6490253067529312983470989)
                    ·
                      refine ⟨2433844900323492368801621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6490253067529312983470989 2433844900323492368801621)
                      ·
                        rfl

theorem cell23_4739896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_4739896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739896 prefixEnd_4739896 := by exact prefixLift 4739896
  have htrace : WordTrace (prefixWord ++ tailWord_4739896) baseStart_4739896 baseEnd_4739896 := by
    simpa [prefixWord, tailWord_4739896, baseEnd_4739896] using wordTrace_append hprefix tailTrace_4739896
  have hstable : (prefixWord ++ tailWord_4739896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739896).length < 2 ^ (prefixWord ++ tailWord_4739896).sum := by decide
  have hdescent : baseEnd_4739896 < baseStart_4739896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739927 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 1, 2, 2]
def baseStart_4739927 : Nat := 118140960795 + 4739927 * 2 ^ 59
def prefixEnd_4739927 : Nat := 4983230072969 + 3 ^ 40 * 4739927 * 2
def baseEnd_4739927 : Nat := 2433860818223781747513979

theorem tailTrace_4739927 : CollatzResearch.WordTrace tailWord_4739927 prefixEnd_4739927 2433860818223781747513979 := by
  unfold tailWord_4739927
  simp only [CollatzResearch.WordTrace]
  refine ⟨172879340299061468927922035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115252893532707645951948023 172879340299061468927922035)
  ·
    refine ⟨259319010448592203391883053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172879340299061468927922035 259319010448592203391883053)
    ·
      refine ⟨97244628918222076271956145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259319010448592203391883053 97244628918222076271956145)
      ·
        refine ⟨72933471688666557203967109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97244628918222076271956145 72933471688666557203967109)
        ·
          refine ⟨13675025941624979475743833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72933471688666557203967109 13675025941624979475743833)
          ·
            refine ⟨10256269456218734606807875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13675025941624979475743833 10256269456218734606807875)
            ·
              refine ⟨15384404184328101910211813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10256269456218734606807875 15384404184328101910211813)
              ·
                refine ⟨2884575784561519108164715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15384404184328101910211813 2884575784561519108164715)
                ·
                  refine ⟨4326863676842278662247073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884575784561519108164715 4326863676842278662247073)
                  ·
                    refine ⟨3245147757631708996685305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326863676842278662247073 3245147757631708996685305)
                    ·
                      refine ⟨2433860818223781747513979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245147757631708996685305 2433860818223781747513979)
                      ·
                        rfl

theorem cell23_4739927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_4739927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739927 prefixEnd_4739927 := by exact prefixLift 4739927
  have htrace : WordTrace (prefixWord ++ tailWord_4739927) baseStart_4739927 baseEnd_4739927 := by
    simpa [prefixWord, tailWord_4739927, baseEnd_4739927] using wordTrace_append hprefix tailTrace_4739927
  have hstable : (prefixWord ++ tailWord_4739927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739927).length < 2 ^ (prefixWord ++ tailWord_4739927).sum := by decide
  have hdescent : baseEnd_4739927 < baseStart_4739927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739929 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_4739929 : Nat := 118140960795 + 4739929 * 2 ^ 59
def prefixEnd_4739929 : Nat := 4983230072969 + 3 ^ 40 * 4739929 * 2
def baseEnd_4739929 : Nat := 811287281728363579896323

theorem tailTrace_4739929 : CollatzResearch.WordTrace tailWord_4739929 prefixEnd_4739929 811287281728363579896323 := by
  unfold tailWord_4739929
  simp only [CollatzResearch.WordTrace]
  refine ⟨172879413245054223269494841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115252942163369482179663227 172879413245054223269494841)
  ·
    refine ⟨129659559933790667452121131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172879413245054223269494841 129659559933790667452121131)
    ·
      refine ⟨194489339900686001178181697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129659559933790667452121131 194489339900686001178181697)
      ·
        refine ⟨145867004925514500883636273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194489339900686001178181697 145867004925514500883636273)
        ·
          refine ⟨109400253694135875662727205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145867004925514500883636273 109400253694135875662727205)
          ·
            refine ⟨20512547567650476686761351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109400253694135875662727205 20512547567650476686761351)
            ·
              refine ⟨30768821351475715030142027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20512547567650476686761351 30768821351475715030142027)
              ·
                refine ⟨46153232027213572545213041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30768821351475715030142027 46153232027213572545213041)
                ·
                  refine ⟨34614924020410179408909781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46153232027213572545213041 34614924020410179408909781)
                  ·
                    refine ⟨811287281728363579896323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34614924020410179408909781 811287281728363579896323)
                    ·
                      rfl

theorem cell23_4739929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_4739929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739929 prefixEnd_4739929 := by exact prefixLift 4739929
  have htrace : WordTrace (prefixWord ++ tailWord_4739929) baseStart_4739929 baseEnd_4739929 := by
    simpa [prefixWord, tailWord_4739929, baseEnd_4739929] using wordTrace_append hprefix tailTrace_4739929
  have hstable : (prefixWord ++ tailWord_4739929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739929).length < 2 ^ (prefixWord ++ tailWord_4739929).sum := by decide
  have hdescent : baseEnd_4739929 < baseStart_4739929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739943 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_4739943 : Nat := 118140960795 + 4739943 * 2 ^ 59
def prefixEnd_4739943 : Nat := 4983230072969 + 3 ^ 40 * 4739943 * 2
def baseEnd_4739943 : Nat := 2433869033914253684913905

theorem tailTrace_4739943 : CollatzResearch.WordTrace tailWord_4739943 prefixEnd_4739943 2433869033914253684913905 := by
  unfold tailWord_4739943
  simp only [CollatzResearch.WordTrace]
  refine ⟨172879923867003503660504483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115253282578002335773669655 172879923867003503660504483)
  ·
    refine ⟨259319885800505255490756725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172879923867003503660504483 259319885800505255490756725)
    ·
      refine ⟨24311239293797367702258443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259319885800505255490756725 24311239293797367702258443)
      ·
        refine ⟨36466858940696051553387665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24311239293797367702258443 36466858940696051553387665)
        ·
          refine ⟨27350144205522038665040749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36466858940696051553387665 27350144205522038665040749)
          ·
            refine ⟨10256304077070764499390281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27350144205522038665040749 10256304077070764499390281)
            ·
              refine ⟨7692228057803073374542711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10256304077070764499390281 7692228057803073374542711)
              ·
                refine ⟨11538342086704610061814067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692228057803073374542711 11538342086704610061814067)
                ·
                  refine ⟨17307513130056915092721101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11538342086704610061814067 17307513130056915092721101)
                  ·
                    refine ⟨6490317423771343159770413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17307513130056915092721101 6490317423771343159770413)
                    ·
                      refine ⟨2433869033914253684913905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6490317423771343159770413 2433869033914253684913905)
                      ·
                        rfl

theorem cell23_4739943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_4739943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739943 prefixEnd_4739943 := by exact prefixLift 4739943
  have htrace : WordTrace (prefixWord ++ tailWord_4739943) baseStart_4739943 baseEnd_4739943 := by
    simpa [prefixWord, tailWord_4739943, baseEnd_4739943] using wordTrace_append hprefix tailTrace_4739943
  have hstable : (prefixWord ++ tailWord_4739943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739943).length < 2 ^ (prefixWord ++ tailWord_4739943).sum := by decide
  have hdescent : baseEnd_4739943 < baseStart_4739943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739953 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 3, 3, 2]
def baseStart_4739953 : Nat := 118140960795 + 4739953 * 2 ^ 59
def prefixEnd_4739953 : Nat := 4983230072969 + 3 ^ 40 * 4739953 * 2
def baseEnd_4739953 : Nat := 2433874168720798645788859

theorem tailTrace_4739953 : CollatzResearch.WordTrace tailWord_4739953 prefixEnd_4739953 2433874168720798645788859 := by
  unfold tailWord_4739953
  simp only [CollatzResearch.WordTrace]
  refine ⟨172880288596967275368368513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115253525731311516912245675 172880288596967275368368513)
  ·
    refine ⟨129660216447725456526276385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172880288596967275368368513 129660216447725456526276385)
    ·
      refine ⟨97245162335794092394707289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129660216447725456526276385 97245162335794092394707289)
      ·
        refine ⟨72933871751845569296030467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97245162335794092394707289 72933871751845569296030467)
        ·
          refine ⟨109400807627768353944045701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72933871751845569296030467 109400807627768353944045701)
          ·
            refine ⟨20512651430206566364508569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109400807627768353944045701 20512651430206566364508569)
            ·
              refine ⟨15384488572654924773381427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20512651430206566364508569 15384488572654924773381427)
              ·
                refine ⟨23076732858982387160072141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15384488572654924773381427 23076732858982387160072141)
                ·
                  refine ⟨8653774822118395185027053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23076732858982387160072141 8653774822118395185027053)
                  ·
                    refine ⟨3245165558294398194385145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8653774822118395185027053 3245165558294398194385145)
                    ·
                      refine ⟨2433874168720798645788859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245165558294398194385145 2433874168720798645788859)
                      ·
                        rfl

theorem cell23_4739953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_4739953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739953 prefixEnd_4739953 := by exact prefixLift 4739953
  have htrace : WordTrace (prefixWord ++ tailWord_4739953) baseStart_4739953 baseEnd_4739953 := by
    simpa [prefixWord, tailWord_4739953, baseEnd_4739953] using wordTrace_append hprefix tailTrace_4739953
  have hstable : (prefixWord ++ tailWord_4739953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739953).length < 2 ^ (prefixWord ++ tailWord_4739953).sum := by decide
  have hdescent : baseEnd_4739953 < baseStart_4739953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4739976 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_4739976 : Nat := 118140960795 + 4739976 * 2 ^ 59
def prefixEnd_4739976 : Nat := 4983230072969 + 3 ^ 40 * 4739976 * 2
def baseEnd_4739976 : Nat := 811295326258617351933751

theorem tailTrace_4739976 : CollatzResearch.WordTrace tailWord_4739976 prefixEnd_4739976 811295326258617351933751 := by
  unfold tailWord_4739976
  simp only [CollatzResearch.WordTrace]
  refine ⟨86440563737941975148227891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115254084983922633530970521 86440563737941975148227891)
  ·
    refine ⟨129660845606912962722341837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86440563737941975148227891 129660845606912962722341837)
    ·
      refine ⟨48622817102592361020878189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129660845606912962722341837 48622817102592361020878189)
      ·
        refine ⟨18233556413472135382829321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48622817102592361020878189 18233556413472135382829321)
        ·
          refine ⟨13675167310104101537121991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18233556413472135382829321 13675167310104101537121991)
          ·
            refine ⟨20512750965156152305682987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13675167310104101537121991 20512750965156152305682987)
            ·
              refine ⟨30769126447734228458524481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20512750965156152305682987 30769126447734228458524481)
              ·
                refine ⟨23076844835800671343893361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30769126447734228458524481 23076844835800671343893361)
                ·
                  refine ⟨17307633626850503507920021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23076844835800671343893361 17307633626850503507920021)
                  ·
                    refine ⟨811295326258617351933751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17307633626850503507920021 811295326258617351933751)
                    ·
                      rfl

theorem cell23_4739976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_4739976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4739976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4739976 prefixEnd_4739976 := by exact prefixLift 4739976
  have htrace : WordTrace (prefixWord ++ tailWord_4739976) baseStart_4739976 baseEnd_4739976 := by
    simpa [prefixWord, tailWord_4739976, baseEnd_4739976] using wordTrace_append hprefix tailTrace_4739976
  have hstable : (prefixWord ++ tailWord_4739976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4739976).length < 2 ^ (prefixWord ++ tailWord_4739976).sum := by decide
  have hdescent : baseEnd_4739976 < baseStart_4739976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4739976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740000 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 2, 2, 2]
def baseStart_4740000 : Nat := 118140960795 + 4740000 * 2 ^ 59
def prefixEnd_4740000 : Nat := 4983230072969 + 3 ^ 40 * 4740000 * 2
def baseEnd_4740000 : Nat := 2433898302311559961901143

theorem tailTrace_4740000 : CollatzResearch.WordTrace tailWord_4740000 prefixEnd_4740000 2433898302311559961901143 := by
  unfold tailWord_4740000
  simp only [CollatzResearch.WordTrace]
  refine ⟨86441001413898501197664727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115254668551864668263552969 86441001413898501197664727)
  ·
    refine ⟨129661502120847751796497091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86441001413898501197664727 129661502120847751796497091)
    ·
      refine ⟨194492253181271627694745637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129661502120847751796497091 194492253181271627694745637)
      ·
        refine ⟨36467297471488430192764807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194492253181271627694745637 36467297471488430192764807)
        ·
          refine ⟨54700946207232645289147211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36467297471488430192764807 54700946207232645289147211)
          ·
            refine ⟨82051419310848967933720817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54700946207232645289147211 82051419310848967933720817)
            ·
              refine ⟨61538564483136725950290613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82051419310848967933720817 61538564483136725950290613)
              ·
                refine ⟨5769240420294068057839745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61538564483136725950290613 5769240420294068057839745)
                ·
                  refine ⟨4326930315220551043379809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5769240420294068057839745 4326930315220551043379809)
                  ·
                    refine ⟨3245197736415413282534857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326930315220551043379809 3245197736415413282534857)
                    ·
                      refine ⟨2433898302311559961901143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245197736415413282534857 2433898302311559961901143)
                      ·
                        rfl

theorem cell23_4740000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_4740000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740000 prefixEnd_4740000 := by exact prefixLift 4740000
  have htrace : WordTrace (prefixWord ++ tailWord_4740000) baseStart_4740000 baseEnd_4740000 := by
    simpa [prefixWord, tailWord_4740000, baseEnd_4740000] using wordTrace_append hprefix tailTrace_4740000
  have hstable : (prefixWord ++ tailWord_4740000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740000).length < 2 ^ (prefixWord ++ tailWord_4740000).sum := by decide
  have hdescent : baseEnd_4740000 < baseStart_4740000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740020 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4740020 : Nat := 118140960795 + 4740020 * 2 ^ 59
def prefixEnd_4740020 : Nat := 4983230072969 + 3 ^ 40 * 4740020 * 2
def baseEnd_4740020 : Nat := 2433908571924649883651051

theorem tailTrace_4740020 : CollatzResearch.WordTrace tailWord_4740020 prefixEnd_4740020 2433908571924649883651051 := by
  unfold tailWord_4740020
  simp only [CollatzResearch.WordTrace]
  refine ⟨86441366143862272905528757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115255154858483030540705009 86441366143862272905528757)
  ·
    refine ⟨8103878075987088084893321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86441366143862272905528757 8103878075987088084893321)
    ·
      refine ⟨6077908556990316063669991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8103878075987088084893321 6077908556990316063669991)
      ·
        refine ⟨9116862835485474095504987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6077908556990316063669991 9116862835485474095504987)
        ·
          refine ⟨13675294253228211143257481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9116862835485474095504987 13675294253228211143257481)
          ·
            refine ⟨10256470689921158357443111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13675294253228211143257481 10256470689921158357443111)
            ·
              refine ⟨15384706034881737536164667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10256470689921158357443111 15384706034881737536164667)
              ·
                refine ⟨23077059052322606304247001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15384706034881737536164667 23077059052322606304247001)
                ·
                  refine ⟨17307794289241954728185251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23077059052322606304247001 17307794289241954728185251)
                  ·
                    refine ⟨25961691433862932092277877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17307794289241954728185251 25961691433862932092277877)
                    ·
                      refine ⟨2433908571924649883651051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25961691433862932092277877 2433908571924649883651051)
                      ·
                        rfl

theorem cell23_4740020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4740020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740020 prefixEnd_4740020 := by exact prefixLift 4740020
  have htrace : WordTrace (prefixWord ++ tailWord_4740020) baseStart_4740020 baseEnd_4740020 := by
    simpa [prefixWord, tailWord_4740020, baseEnd_4740020] using wordTrace_append hprefix tailTrace_4740020
  have hstable : (prefixWord ++ tailWord_4740020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740020).length < 2 ^ (prefixWord ++ tailWord_4740020).sum := by decide
  have hdescent : baseEnd_4740020 < baseStart_4740020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740023 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 5]
def baseStart_4740023 : Nat := 118140960795 + 4740023 * 2 ^ 59
def prefixEnd_4740023 : Nat := 4983230072969 + 3 ^ 40 * 4740023 * 2
def baseEnd_4740023 : Nat := 270434456929623707990393

theorem tailTrace_4740023 : CollatzResearch.WordTrace tailWord_4740023 prefixEnd_4740023 270434456929623707990393 := by
  unfold tailWord_4740023
  simp only [CollatzResearch.WordTrace]
  refine ⟨172882841706713677323416723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115255227804475784882277815 172882841706713677323416723)
  ·
    refine ⟨259324262560070515985125085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172882841706713677323416723 259324262560070515985125085)
    ·
      refine ⟨97246598460026443494421907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259324262560070515985125085 97246598460026443494421907)
      ·
        refine ⟨145869897690039665241632861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97246598460026443494421907 145869897690039665241632861)
        ·
          refine ⟨54701211633764874465612323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145869897690039665241632861 54701211633764874465612323)
          ·
            refine ⟨82051817450647311698418485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54701211633764874465612323 82051817450647311698418485)
            ·
              refine ⟨7692357885998185471726733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82051817450647311698418485 7692357885998185471726733)
              ·
                refine ⟨2884634207249319551897525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7692357885998185471726733 2884634207249319551897525)
                ·
                  refine ⟨270434456929623707990393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2884634207249319551897525 270434456929623707990393)
                  ·
                    rfl

theorem cell23_4740023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 5].length) (baseStart_4740023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740023 prefixEnd_4740023 := by exact prefixLift 4740023
  have htrace : WordTrace (prefixWord ++ tailWord_4740023) baseStart_4740023 baseEnd_4740023 := by
    simpa [prefixWord, tailWord_4740023, baseEnd_4740023] using wordTrace_append hprefix tailTrace_4740023
  have hstable : (prefixWord ++ tailWord_4740023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740023).length < 2 ^ (prefixWord ++ tailWord_4740023).sum := by decide
  have hdescent : baseEnd_4740023 < baseStart_4740023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740040 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 7]
def baseStart_4740040 : Nat := 118140960795 + 4740040 * 2 ^ 59
def prefixEnd_4740040 : Nat := 4983230072969 + 3 ^ 40 * 4740040 * 2
def baseEnd_4740040 : Nat := 270435426837526645044551

theorem tailTrace_4740040 : CollatzResearch.WordTrace tailWord_4740040 prefixEnd_4740040 270435426837526645044551 := by
  unfold tailWord_4740040
  simp only [CollatzResearch.WordTrace]
  refine ⟨86441730873826044613392787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115255641165101392817857049 86441730873826044613392787)
  ·
    refine ⟨129662596310739066920089181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86441730873826044613392787 129662596310739066920089181)
    ·
      refine ⟨48623473616527150095033443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129662596310739066920089181 48623473616527150095033443)
      ·
        refine ⟨72935210424790725142550165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48623473616527150095033443 72935210424790725142550165)
        ·
          refine ⟨3418837988662065241057039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72935210424790725142550165 3418837988662065241057039)
          ·
            refine ⟨5128256982993097861585559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418837988662065241057039 5128256982993097861585559)
            ·
              refine ⟨7692385474489646792378339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5128256982993097861585559 7692385474489646792378339)
              ·
                refine ⟨11538578211734470188567509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692385474489646792378339 11538578211734470188567509)
                ·
                  refine ⟨270435426837526645044551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11538578211734470188567509 270435426837526645044551)
                  ·
                    rfl

theorem cell23_4740040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 7].length) (baseStart_4740040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740040 prefixEnd_4740040 := by exact prefixLift 4740040
  have htrace : WordTrace (prefixWord ++ tailWord_4740040) baseStart_4740040 baseEnd_4740040 := by
    simpa [prefixWord, tailWord_4740040, baseEnd_4740040] using wordTrace_append hprefix tailTrace_4740040
  have hstable : (prefixWord ++ tailWord_4740040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740040).length < 2 ^ (prefixWord ++ tailWord_4740040).sum := by decide
  have hdescent : baseEnd_4740040 < baseStart_4740040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740045 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4740045 : Nat := 118140960795 + 4740045 * 2 ^ 59
def prefixEnd_4740045 : Nat := 4983230072969 + 3 ^ 40 * 4740045 * 2
def baseEnd_4740045 : Nat := 2433921408941012285838437

theorem tailTrace_4740045 : CollatzResearch.WordTrace tailWord_4740045 prefixEnd_4740045 2433921408941012285838437 := by
  unfold tailWord_4740045
  simp only [CollatzResearch.WordTrace]
  refine ⟨172883644112633975080717589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115255762741755983387145059 172883644112633975080717589)
  ·
    refine ⟨8103920817779717581908637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172883644112633975080717589 8103920817779717581908637)
    ·
      refine ⟨3038970306667394093215739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8103920817779717581908637 3038970306667394093215739)
      ·
        refine ⟨4558455460001091139823609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038970306667394093215739 4558455460001091139823609)
        ·
          refine ⟨3418841595000818354867707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4558455460001091139823609 3418841595000818354867707)
          ·
            refine ⟨5128262392501227532301561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418841595000818354867707 5128262392501227532301561)
            ·
              refine ⟨3846196794375920649226171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5128262392501227532301561 3846196794375920649226171)
              ·
                refine ⟨5769295191563880973839257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846196794375920649226171 5769295191563880973839257)
                ·
                  refine ⟨4326971393672910730379443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5769295191563880973839257 4326971393672910730379443)
                  ·
                    refine ⟨6490457090509366095569165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4326971393672910730379443 6490457090509366095569165)
                    ·
                      refine ⟨2433921408941012285838437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6490457090509366095569165 2433921408941012285838437)
                      ·
                        rfl

theorem cell23_4740045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4740045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740045 prefixEnd_4740045 := by exact prefixLift 4740045
  have htrace : WordTrace (prefixWord ++ tailWord_4740045) baseStart_4740045 baseEnd_4740045 := by
    simpa [prefixWord, tailWord_4740045, baseEnd_4740045] using wordTrace_append hprefix tailTrace_4740045
  have hstable : (prefixWord ++ tailWord_4740045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740045).length < 2 ^ (prefixWord ++ tailWord_4740045).sum := by decide
  have hdescent : baseEnd_4740045 < baseStart_4740045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740046 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_4740046 : Nat := 118140960795 + 4740046 * 2 ^ 59
def prefixEnd_4740046 : Nat := 4983230072969 + 3 ^ 40 * 4740046 * 2
def baseEnd_4740046 : Nat := 2433921922421666781925931

theorem tailTrace_4740046 : CollatzResearch.WordTrace tailWord_4740046 prefixEnd_4740046 2433921922421666781925931 := by
  unfold tailWord_4740046
  simp only [CollatzResearch.WordTrace]
  refine ⟨21610460073203794031437999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115255787057086901501002661 21610460073203794031437999)
  ·
    refine ⟨32415690109805691047156999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21610460073203794031437999 32415690109805691047156999)
    ·
      refine ⟨48623535164708536570735499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32415690109805691047156999 48623535164708536570735499)
      ·
        refine ⟨72935302747062804856103249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48623535164708536570735499 72935302747062804856103249)
        ·
          refine ⟨54701477060297103642077437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72935302747062804856103249 54701477060297103642077437)
          ·
            refine ⟨20513053897611413865779039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54701477060297103642077437 20513053897611413865779039)
            ·
              refine ⟨30769580846417120798668559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20513053897611413865779039 30769580846417120798668559)
              ·
                refine ⟨46154371269625681198002839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30769580846417120798668559 46154371269625681198002839)
                ·
                  refine ⟨69231556904438521797004259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46154371269625681198002839 69231556904438521797004259)
                  ·
                    refine ⟨103847335356657782695506389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69231556904438521797004259 103847335356657782695506389)
                    ·
                      refine ⟨2433921922421666781925931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103847335356657782695506389 2433921922421666781925931)
                      ·
                        rfl

theorem cell23_4740046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_4740046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740046 prefixEnd_4740046 := by exact prefixLift 4740046
  have htrace : WordTrace (prefixWord ++ tailWord_4740046) baseStart_4740046 baseEnd_4740046 := by
    simpa [prefixWord, tailWord_4740046, baseEnd_4740046] using wordTrace_append hprefix tailTrace_4740046
  have hstable : (prefixWord ++ tailWord_4740046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740046).length < 2 ^ (prefixWord ++ tailWord_4740046).sum := by decide
  have hdescent : baseEnd_4740046 < baseStart_4740046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740157 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4740157 : Nat := 118140960795 + 4740157 * 2 ^ 59
def prefixEnd_4740157 : Nat := 4983230072969 + 3 ^ 40 * 4740157 * 2
def baseEnd_4740157 : Nat := 2433978918774315847637921

theorem tailTrace_4740157 : CollatzResearch.WordTrace tailWord_4740157 prefixEnd_4740157 2433978918774315847637921 := by
  unfold tailWord_4740157
  simp only [CollatzResearch.WordTrace]
  refine ⟨172887729088228218208794725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115258486058818812139196483 172887729088228218208794725)
  ·
    refine ⟨32416449204042790914149011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172887729088228218208794725 32416449204042790914149011)
    ·
      refine ⟨48624673806064186371223517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32416449204042790914149011 48624673806064186371223517)
      ·
        refine ⟨18234252677274069889208819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48624673806064186371223517 18234252677274069889208819)
        ·
          refine ⟨27351379015911104833813229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18234252677274069889208819 27351379015911104833813229)
          ·
            refine ⟨10256767130966664312679961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27351379015911104833813229 10256767130966664312679961)
            ·
              refine ⟨7692575348224998234509971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10256767130966664312679961 7692575348224998234509971)
              ·
                refine ⟨11538863022337497351764957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692575348224998234509971 11538863022337497351764957)
                ·
                  refine ⟨4327073633376561506911859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11538863022337497351764957 4327073633376561506911859)
                  ·
                    refine ⟨6490610450064842260367789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4327073633376561506911859 6490610450064842260367789)
                    ·
                      refine ⟨2433978918774315847637921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6490610450064842260367789 2433978918774315847637921)
                      ·
                        rfl

theorem cell23_4740157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4740157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740157 prefixEnd_4740157 := by exact prefixLift 4740157
  have htrace : WordTrace (prefixWord ++ tailWord_4740157) baseStart_4740157 baseEnd_4740157 := by
    simpa [prefixWord, tailWord_4740157, baseEnd_4740157] using wordTrace_append hprefix tailTrace_4740157
  have hstable : (prefixWord ++ tailWord_4740157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740157).length < 2 ^ (prefixWord ++ tailWord_4740157).sum := by decide
  have hdescent : baseEnd_4740157 < baseStart_4740157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740180 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_4740180 : Nat := 118140960795 + 4740180 * 2 ^ 59
def prefixEnd_4740180 : Nat := 4983230072969 + 3 ^ 40 * 4740180 * 2
def baseEnd_4740180 : Nat := 2433990728829369257650315

theorem tailTrace_4740180 : CollatzResearch.WordTrace tailWord_4740180 prefixEnd_4740180 2433990728829369257650315 := by
  unfold tailWord_4740180
  simp only [CollatzResearch.WordTrace]
  refine ⟨86444283983572446568440997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115259045311429928757921329 86444283983572446568440997)
  ·
    refine ⟨16208303246919833731582687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86444283983572446568440997 16208303246919833731582687)
    ·
      refine ⟨24312454870379750597374031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16208303246919833731582687 24312454870379750597374031)
      ·
        refine ⟨36468682305569625896061047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24312454870379750597374031 36468682305569625896061047)
        ·
          refine ⟨54703023458354438844091571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36468682305569625896061047 54703023458354438844091571)
          ·
            refine ⟨82054535187531658266137357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54703023458354438844091571 82054535187531658266137357)
            ·
              refine ⟨30770450695324371849801509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82054535187531658266137357 30770450695324371849801509)
              ·
                refine ⟨5769459505373319721837783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30770450695324371849801509 5769459505373319721837783)
                ·
                  refine ⟨8654189258059979582756675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5769459505373319721837783 8654189258059979582756675)
                  ·
                    refine ⟨12981283887089969374135013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8654189258059979582756675 12981283887089969374135013)
                    ·
                      refine ⟨2433990728829369257650315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12981283887089969374135013 2433990728829369257650315)
                      ·
                        rfl

theorem cell23_4740180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_4740180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740180 prefixEnd_4740180 := by exact prefixLift 4740180
  have htrace : WordTrace (prefixWord ++ tailWord_4740180) baseStart_4740180 baseEnd_4740180 := by
    simpa [prefixWord, tailWord_4740180, baseEnd_4740180] using wordTrace_append hprefix tailTrace_4740180
  have hstable : (prefixWord ++ tailWord_4740180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740180).length < 2 ^ (prefixWord ++ tailWord_4740180).sum := by decide
  have hdescent : baseEnd_4740180 < baseStart_4740180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740193 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_4740193 : Nat := 118140960795 + 4740193 * 2 ^ 59
def prefixEnd_4740193 : Nat := 4983230072969 + 3 ^ 40 * 4740193 * 2
def baseEnd_4740193 : Nat := 2433997404077877706787755

theorem tailTrace_4740193 : CollatzResearch.WordTrace tailWord_4740193 prefixEnd_4740193 2433997404077877706787755 := by
  unfold tailWord_4740193
  simp only [CollatzResearch.WordTrace]
  refine ⟨172889042116097796357105233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115259361410731864238070155 172889042116097796357105233)
  ·
    refine ⟨129666781587073347267828925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172889042116097796357105233 129666781587073347267828925)
    ·
      refine ⟨48625043095152505225435847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129666781587073347267828925 48625043095152505225435847)
      ·
        refine ⟨72937564642728757838153771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48625043095152505225435847 72937564642728757838153771)
        ·
          refine ⟨109406346964093136757230657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72937564642728757838153771 109406346964093136757230657)
          ·
            refine ⟨82054760223069852567922993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109406346964093136757230657 82054760223069852567922993)
            ·
              refine ⟨61541070167302389425942245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82054760223069852567922993 61541070167302389425942245)
              ·
                refine ⟨11538950656369198017364171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61541070167302389425942245 11538950656369198017364171)
                ·
                  refine ⟨17308425984553797026046257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11538950656369198017364171 17308425984553797026046257)
                  ·
                    refine ⟨12981319488415347769534693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17308425984553797026046257 12981319488415347769534693)
                    ·
                      refine ⟨2433997404077877706787755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12981319488415347769534693 2433997404077877706787755)
                      ·
                        rfl

theorem cell23_4740193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_4740193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740193 prefixEnd_4740193 := by exact prefixLift 4740193
  have htrace : WordTrace (prefixWord ++ tailWord_4740193) baseStart_4740193 baseEnd_4740193 := by
    simpa [prefixWord, tailWord_4740193, baseEnd_4740193] using wordTrace_append hprefix tailTrace_4740193
  have hstable : (prefixWord ++ tailWord_4740193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740193).length < 2 ^ (prefixWord ++ tailWord_4740193).sum := by decide
  have hdescent : baseEnd_4740193 < baseStart_4740193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740320 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_4740320 : Nat := 118140960795 + 4740320 * 2 ^ 59
def prefixEnd_4740320 : Nat := 4983230072969 + 3 ^ 40 * 4740320 * 2
def baseEnd_4740320 : Nat := 2434062616120998709899671

theorem tailTrace_4740320 : CollatzResearch.WordTrace tailWord_4740320 prefixEnd_4740320 2434062616120998709899671 := by
  unfold tailWord_4740320
  simp only [CollatzResearch.WordTrace]
  refine ⟨86446837093318848523489207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115262449457758464697985609 86446837093318848523489207)
  ·
    refine ⟨129670255639978272785233811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86446837093318848523489207 129670255639978272785233811)
    ·
      refine ⟨194505383459967409177850717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129670255639978272785233811 194505383459967409177850717)
      ·
        refine ⟨72939518797487778441694019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194505383459967409177850717 72939518797487778441694019)
        ·
          refine ⟨109409278196231667662541029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72939518797487778441694019 109409278196231667662541029)
          ·
            refine ⟨20514239661793437686726443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109409278196231667662541029 20514239661793437686726443)
            ·
              refine ⟨30771359492690156530089665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20514239661793437686726443 30771359492690156530089665)
              ·
                refine ⟨23078519619517617397567249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30771359492690156530089665 23078519619517617397567249)
                ·
                  refine ⟨17308889714638213048175437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23078519619517617397567249 17308889714638213048175437)
                  ·
                    refine ⟨6490833642989329893065789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17308889714638213048175437 6490833642989329893065789)
                    ·
                      refine ⟨2434062616120998709899671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6490833642989329893065789 2434062616120998709899671)
                      ·
                        rfl

theorem cell23_4740320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_4740320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740320 prefixEnd_4740320 := by exact prefixLift 4740320
  have htrace : WordTrace (prefixWord ++ tailWord_4740320) baseStart_4740320 baseEnd_4740320 := by
    simpa [prefixWord, tailWord_4740320, baseEnd_4740320] using wordTrace_append hprefix tailTrace_4740320
  have hstable : (prefixWord ++ tailWord_4740320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740320).length < 2 ^ (prefixWord ++ tailWord_4740320).sum := by decide
  have hdescent : baseEnd_4740320 < baseStart_4740320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740321 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_4740321 : Nat := 118140960795 + 4740321 * 2 ^ 59
def prefixEnd_4740321 : Nat := 4983230072969 + 3 ^ 40 * 4740321 * 2
def baseEnd_4740321 : Nat := 2434063129601653205987167

theorem tailTrace_4740321 : CollatzResearch.WordTrace tailWord_4740321 prefixEnd_4740321 2434063129601653205987167 := by
  unfold tailWord_4740321
  simp only [CollatzResearch.WordTrace]
  refine ⟨172893710659634074217764817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115262473773089382811843211 172893710659634074217764817)
  ·
    refine ⟨129670282994725555663323613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172893710659634074217764817 129670282994725555663323613)
    ·
      refine ⟨48626356123022083373746355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129670282994725555663323613 48626356123022083373746355)
      ·
        refine ⟨72939534184533125060619533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48626356123022083373746355 72939534184533125060619533)
        ·
          refine ⟨27352325319199921897732325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72939534184533125060619533 27352325319199921897732325)
          ·
            refine ⟨5128560997349985355824811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27352325319199921897732325 5128560997349985355824811)
            ·
              refine ⟨7692841496024978033737217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5128560997349985355824811 7692841496024978033737217)
              ·
                refine ⟨5769631122018733525302913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7692841496024978033737217 5769631122018733525302913)
                ·
                  refine ⟨4327223341514050143977185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5769631122018733525302913 4327223341514050143977185)
                  ·
                    refine ⟨3245417506135537607982889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4327223341514050143977185 3245417506135537607982889)
                    ·
                      refine ⟨2434063129601653205987167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245417506135537607982889 2434063129601653205987167)
                      ·
                        rfl

theorem cell23_4740321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_4740321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740321 prefixEnd_4740321 := by exact prefixLift 4740321
  have htrace : WordTrace (prefixWord ++ tailWord_4740321) baseStart_4740321 baseEnd_4740321 := by
    simpa [prefixWord, tailWord_4740321, baseEnd_4740321] using wordTrace_append hprefix tailTrace_4740321
  have hstable : (prefixWord ++ tailWord_4740321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740321).length < 2 ^ (prefixWord ++ tailWord_4740321).sum := by decide
  have hdescent : baseEnd_4740321 < baseStart_4740321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740327 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 7]
def baseStart_4740327 : Nat := 118140960795 + 4740327 * 2 ^ 59
def prefixEnd_4740327 : Nat := 4983230072969 + 3 ^ 40 * 4740327 * 2
def baseEnd_4740327 : Nat := 270451801165064464723571

theorem tailTrace_4740327 : CollatzResearch.WordTrace tailWord_4740327 prefixEnd_4740327 270451801165064464723571 := by
  unfold tailWord_4740327
  simp only [CollatzResearch.WordTrace]
  refine ⟨172893929497612337242483235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115262619665074891494988823 172893929497612337242483235)
  ·
    refine ⟨259340894246418505863724853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172893929497612337242483235 259340894246418505863724853)
    ·
      refine ⟨24313208835601734924724205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259340894246418505863724853 24313208835601734924724205)
      ·
        refine ⟨9117453313350650596771577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24313208835601734924724205 9117453313350650596771577)
        ·
          refine ⟨6838089985012987947578683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9117453313350650596771577 6838089985012987947578683)
          ·
            refine ⟨10257134977519481921368025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838089985012987947578683 10257134977519481921368025)
            ·
              refine ⟨7692851233139611441026019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10257134977519481921368025 7692851233139611441026019)
              ·
                refine ⟨11539276849709417161539029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692851233139611441026019 11539276849709417161539029)
                ·
                  refine ⟨270451801165064464723571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11539276849709417161539029 270451801165064464723571)
                  ·
                    rfl

theorem cell23_4740327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 7].length) (baseStart_4740327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740327 prefixEnd_4740327 := by exact prefixLift 4740327
  have htrace : WordTrace (prefixWord ++ tailWord_4740327) baseStart_4740327 baseEnd_4740327 := by
    simpa [prefixWord, tailWord_4740327, baseEnd_4740327] using wordTrace_append hprefix tailTrace_4740327
  have hstable : (prefixWord ++ tailWord_4740327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740327).length < 2 ^ (prefixWord ++ tailWord_4740327).sum := by decide
  have hdescent : baseEnd_4740327 < baseStart_4740327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740338 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_4740338 : Nat := 118140960795 + 4740338 * 2 ^ 59
def prefixEnd_4740338 : Nat := 4983230072969 + 3 ^ 40 * 4740338 * 2
def baseEnd_4740338 : Nat := 2434071858772779639474589

theorem tailTrace_4740338 : CollatzResearch.WordTrace tailWord_4740338 prefixEnd_4740338 2434071858772779639474589 := by
  unfold tailWord_4740338
  simp only [CollatzResearch.WordTrace]
  refine ⟨43223582675143121530283417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115262887133714990747422445 43223582675143121530283417)
  ·
    refine ⟨32417687006357341147712563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43223582675143121530283417 32417687006357341147712563)
    ·
      refine ⟨48626530509536011721568845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32417687006357341147712563 48626530509536011721568845)
      ·
        refine ⟨18234948941076004395588317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48626530509536011721568845 18234948941076004395588317)
        ·
          refine ⟨6838105852903501648345619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18234948941076004395588317 6838105852903501648345619)
          ·
            refine ⟨10257158779355252472518429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838105852903501648345619 10257158779355252472518429)
            ·
              refine ⟨3846434542258219677194411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10257158779355252472518429 3846434542258219677194411)
              ·
                refine ⟨5769651813387329515791617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846434542258219677194411 5769651813387329515791617)
                ·
                  refine ⟨4327238860040497136843713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5769651813387329515791617 4327238860040497136843713)
                  ·
                    refine ⟨3245429145030372852632785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4327238860040497136843713 3245429145030372852632785)
                    ·
                      refine ⟨2434071858772779639474589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245429145030372852632785 2434071858772779639474589)
                      ·
                        rfl

theorem cell23_4740338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_4740338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740338 prefixEnd_4740338 := by exact prefixLift 4740338
  have htrace : WordTrace (prefixWord ++ tailWord_4740338) baseStart_4740338 baseEnd_4740338 := by
    simpa [prefixWord, tailWord_4740338, baseEnd_4740338] using wordTrace_append hprefix tailTrace_4740338
  have hstable : (prefixWord ++ tailWord_4740338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740338).length < 2 ^ (prefixWord ++ tailWord_4740338).sum := by decide
  have hdescent : baseEnd_4740338 < baseStart_4740338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740387 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 3, 4]
def baseStart_4740387 : Nat := 118140960795 + 4740387 * 2 ^ 59
def prefixEnd_4740387 : Nat := 4983230072969 + 3 ^ 40 * 4740387 * 2
def baseEnd_4740387 : Nat := 811365673108283315920621

theorem tailTrace_4740387 : CollatzResearch.WordTrace tailWord_4740387 prefixEnd_4740387 811365673108283315920621 := by
  unfold tailWord_4740387
  simp only [CollatzResearch.WordTrace]
  refine ⟨172896117877394967489667415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115264078584929978326444943 172896117877394967489667415)
  ·
    refine ⟨259344176816092451234501123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172896117877394967489667415 259344176816092451234501123)
    ·
      refine ⟨389016265224138676851751685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259344176816092451234501123 389016265224138676851751685)
      ·
        refine ⟨72940549729526001909703441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389016265224138676851751685 72940549729526001909703441)
        ·
          refine ⟨54705412297144501432277581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72940549729526001909703441 54705412297144501432277581)
          ·
            refine ⟨20514529611429188037104093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54705412297144501432277581 20514529611429188037104093)
            ·
              refine ⟨7692948604285945513914035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20514529611429188037104093 7692948604285945513914035)
              ·
                refine ⟨11539422906428918270871053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692948604285945513914035 11539422906428918270871053)
                ·
                  refine ⟨4327283589910844351576645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11539422906428918270871053 4327283589910844351576645)
                  ·
                    refine ⟨811365673108283315920621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327283589910844351576645 811365673108283315920621)
                    ·
                      rfl

theorem cell23_4740387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 4].length) (baseStart_4740387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740387 prefixEnd_4740387 := by exact prefixLift 4740387
  have htrace : WordTrace (prefixWord ++ tailWord_4740387) baseStart_4740387 baseEnd_4740387 := by
    simpa [prefixWord, tailWord_4740387, baseEnd_4740387] using wordTrace_append hprefix tailTrace_4740387
  have hstable : (prefixWord ++ tailWord_4740387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740387).length < 2 ^ (prefixWord ++ tailWord_4740387).sum := by decide
  have hdescent : baseEnd_4740387 < baseStart_4740387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740393 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_4740393 : Nat := 118140960795 + 4740393 * 2 ^ 59
def prefixEnd_4740393 : Nat := 4983230072969 + 3 ^ 40 * 4740393 * 2
def baseEnd_4740393 : Nat := 2434100100208776924286835

theorem tailTrace_4740393 : CollatzResearch.WordTrace tailWord_4740393 prefixEnd_4740393 2434100100208776924286835 := by
  unfold tailWord_4740393
  simp only [CollatzResearch.WordTrace]
  refine ⟨172896336715373230514385833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115264224476915487009590555 172896336715373230514385833)
  ·
    refine ⟨129672252536529922885789375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172896336715373230514385833 129672252536529922885789375)
    ·
      refine ⟨194508378804794884328684063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129672252536529922885789375 194508378804794884328684063)
      ·
        refine ⟨291762568207192326493026095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194508378804794884328684063 291762568207192326493026095)
        ·
          refine ⟨437643852310788489739539143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291762568207192326493026095 437643852310788489739539143)
          ·
            refine ⟨656465778466182734609308715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437643852310788489739539143 656465778466182734609308715)
            ·
              refine ⟨984698667699274101913963073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656465778466182734609308715 984698667699274101913963073)
              ·
                refine ⟨738524000774455576435472305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984698667699274101913963073 738524000774455576435472305)
                ·
                  refine ⟨553893000580841682326604229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 738524000774455576435472305 553893000580841682326604229)
                  ·
                    refine ⟨103854937608907815436238293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553893000580841682326604229 103854937608907815436238293)
                    ·
                      refine ⟨2434100100208776924286835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103854937608907815436238293 2434100100208776924286835)
                      ·
                        rfl

theorem cell23_4740393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_4740393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740393 prefixEnd_4740393 := by exact prefixLift 4740393
  have htrace : WordTrace (prefixWord ++ tailWord_4740393) baseStart_4740393 baseEnd_4740393 := by
    simpa [prefixWord, tailWord_4740393, baseEnd_4740393] using wordTrace_append hprefix tailTrace_4740393
  have hstable : (prefixWord ++ tailWord_4740393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740393).length < 2 ^ (prefixWord ++ tailWord_4740393).sum := by decide
  have hdescent : baseEnd_4740393 < baseStart_4740393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740400 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 6]
def baseStart_4740400 : Nat := 118140960795 + 4740400 * 2 ^ 59
def prefixEnd_4740400 : Nat := 4983230072969 + 3 ^ 40 * 4740400 * 2
def baseEnd_4740400 : Nat := 270455966063706488544367

theorem tailTrace_4740400 : CollatzResearch.WordTrace tailWord_4740400 prefixEnd_4740400 270455966063706488544367 := by
  unfold tailWord_4740400
  simp only [CollatzResearch.WordTrace]
  refine ⟨86448296013173935354945327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115264394684231913806593769 86448296013173935354945327)
  ·
    refine ⟨129672444019760903032417991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86448296013173935354945327 129672444019760903032417991)
    ·
      refine ⟨194508666029641354548626987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129672444019760903032417991 194508666029641354548626987)
      ·
        refine ⟨291762999044462031822940481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194508666029641354548626987 291762999044462031822940481)
        ·
          refine ⟨218822249283346523867205361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291762999044462031822940481 218822249283346523867205361)
          ·
            refine ⟨164116686962509892900404021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218822249283346523867205361 164116686962509892900404021)
            ·
              refine ⟨15385939402735302459412877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164116686962509892900404021 15385939402735302459412877)
              ·
                refine ⟨5769727276025738422279829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15385939402735302459412877 5769727276025738422279829)
                ·
                  refine ⟨270455966063706488544367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5769727276025738422279829 270455966063706488544367)
                  ·
                    rfl

theorem cell23_4740400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_4740400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740400 prefixEnd_4740400 := by exact prefixLift 4740400
  have htrace : WordTrace (prefixWord ++ tailWord_4740400) baseStart_4740400 baseEnd_4740400 := by
    simpa [prefixWord, tailWord_4740400, baseEnd_4740400] using wordTrace_append hprefix tailTrace_4740400
  have hstable : (prefixWord ++ tailWord_4740400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740400).length < 2 ^ (prefixWord ++ tailWord_4740400).sum := by decide
  have hdescent : baseEnd_4740400 < baseStart_4740400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740414 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_4740414 : Nat := 118140960795 + 4740414 * 2 ^ 59
def prefixEnd_4740414 : Nat := 4983230072969 + 3 ^ 40 * 4740414 * 2
def baseEnd_4740414 : Nat := 2434110883302521342124239

theorem tailTrace_4740414 : CollatzResearch.WordTrace tailWord_4740414 prefixEnd_4740414 2434110883302521342124239 := by
  unfold tailWord_4740414
  simp only [CollatzResearch.WordTrace]
  refine ⟨21612137831037143887612537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115264735098864767400600197 21612137831037143887612537)
  ·
    refine ⟨16209103373277857915709403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21612137831037143887612537 16209103373277857915709403)
    ·
      refine ⟨24313655059916786873564105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16209103373277857915709403 24313655059916786873564105)
      ·
        refine ⟨18235241294937590155173079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24313655059916786873564105 18235241294937590155173079)
        ·
          refine ⟨27352861942406385232759619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18235241294937590155173079 27352861942406385232759619)
          ·
            refine ⟨41029292913609577849139429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27352861942406385232759619 41029292913609577849139429)
            ·
              refine ⟨7692992421301795846713643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41029292913609577849139429 7692992421301795846713643)
              ·
                refine ⟨11539488631952693770070465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692992421301795846713643 11539488631952693770070465)
                ·
                  refine ⟨8654616473964520327552849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11539488631952693770070465 8654616473964520327552849)
                  ·
                    refine ⟨6490962355473390245664637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8654616473964520327552849 6490962355473390245664637)
                    ·
                      refine ⟨2434110883302521342124239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6490962355473390245664637 2434110883302521342124239)
                      ·
                        rfl

theorem cell23_4740414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_4740414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740414 prefixEnd_4740414 := by exact prefixLift 4740414
  have htrace : WordTrace (prefixWord ++ tailWord_4740414) baseStart_4740414 baseEnd_4740414 := by
    simpa [prefixWord, tailWord_4740414, baseEnd_4740414] using wordTrace_append hprefix tailTrace_4740414
  have hstable : (prefixWord ++ tailWord_4740414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740414).length < 2 ^ (prefixWord ++ tailWord_4740414).sum := by decide
  have hdescent : baseEnd_4740414 < baseStart_4740414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740477 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_4740477 : Nat := 118140960795 + 4740477 * 2 ^ 59
def prefixEnd_4740477 : Nat := 4983230072969 + 3 ^ 40 * 4740477 * 2
def baseEnd_4740477 : Nat := 811381077527918198545483

theorem tailTrace_4740477 : CollatzResearch.WordTrace tailWord_4740477 prefixEnd_4740477 811381077527918198545483 := by
  unfold tailWord_4740477
  simp only [CollatzResearch.WordTrace]
  refine ⟨172899400447068912860443685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115266266964712608573629123 172899400447068912860443685)
  ·
    refine ⟨32418637583825421161333191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172899400447068912860443685 32418637583825421161333191)
    ·
      refine ⟨48627956375738131741999787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32418637583825421161333191 48627956375738131741999787)
      ·
        refine ⟨72941934563607197612999681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48627956375738131741999787 72941934563607197612999681)
        ·
          refine ⟨54706450922705398209749761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72941934563607197612999681 54706450922705398209749761)
          ·
            refine ⟨41029838192029048657312321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54706450922705398209749761 41029838192029048657312321)
            ·
              refine ⟨30772378644021786492984241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41029838192029048657312321 30772378644021786492984241)
              ·
                refine ⟨23079283983016339869738181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30772378644021786492984241 23079283983016339869738181)
                ·
                  refine ⟨4327365746815563725575909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23079283983016339869738181 4327365746815563725575909)
                  ·
                    refine ⟨811381077527918198545483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327365746815563725575909 811381077527918198545483)
                    ·
                      rfl

theorem cell23_4740477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_4740477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740477 prefixEnd_4740477 := by exact prefixLift 4740477
  have htrace : WordTrace (prefixWord ++ tailWord_4740477) baseStart_4740477 baseEnd_4740477 := by
    simpa [prefixWord, tailWord_4740477, baseEnd_4740477] using wordTrace_append hprefix tailTrace_4740477
  have hstable : (prefixWord ++ tailWord_4740477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740477).length < 2 ^ (prefixWord ++ tailWord_4740477).sum := by decide
  have hdescent : baseEnd_4740477 < baseStart_4740477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740484 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_4740484 : Nat := 118140960795 + 4740484 * 2 ^ 59
def prefixEnd_4740484 : Nat := 4983230072969 + 3 ^ 40 * 4740484 * 2
def baseEnd_4740484 : Nat := 2434146826948336068248917

theorem tailTrace_4740484 : CollatzResearch.WordTrace tailWord_4740484 prefixEnd_4740484 2434146826948336068248917 := by
  unfold tailWord_4740484
  simp only [CollatzResearch.WordTrace]
  refine ⟨86449827879021776527974253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115266437172029035370632337 86449827879021776527974253)
  ·
    refine ⟨32418685454633166197990345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86449827879021776527974253 32418685454633166197990345)
    ·
      refine ⟨24314014090974874648492759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32418685454633166197990345 24314014090974874648492759)
      ·
        refine ⟨36471021136462311972739139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24314014090974874648492759 36471021136462311972739139)
        ·
          refine ⟨54706531704693467959108709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36471021136462311972739139 54706531704693467959108709)
          ·
            refine ⟨10257474694630025242332883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54706531704693467959108709 10257474694630025242332883)
            ·
              refine ⟨15386212041945037863499325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10257474694630025242332883 15386212041945037863499325)
              ·
                refine ⟨5769829515729389198812247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15386212041945037863499325 5769829515729389198812247)
                ·
                  refine ⟨8654744273594083798218371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5769829515729389198812247 8654744273594083798218371)
                  ·
                    refine ⟨12982116410391125697327557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8654744273594083798218371 12982116410391125697327557)
                    ·
                      refine ⟨2434146826948336068248917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12982116410391125697327557 2434146826948336068248917)
                      ·
                        rfl

theorem cell23_4740484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_4740484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740484 prefixEnd_4740484 := by exact prefixLift 4740484
  have htrace : WordTrace (prefixWord ++ tailWord_4740484) baseStart_4740484 baseEnd_4740484 := by
    simpa [prefixWord, tailWord_4740484, baseEnd_4740484] using wordTrace_append hprefix tailTrace_4740484
  have hstable : (prefixWord ++ tailWord_4740484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740484).length < 2 ^ (prefixWord ++ tailWord_4740484).sum := by decide
  have hdescent : baseEnd_4740484 < baseStart_4740484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740504 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4740504 : Nat := 118140960795 + 4740504 * 2 ^ 59
def prefixEnd_4740504 : Nat := 4983230072969 + 3 ^ 40 * 4740504 * 2
def baseEnd_4740504 : Nat := 2434157096561425989998825

theorem tailTrace_4740504 : CollatzResearch.WordTrace tailWord_4740504 prefixEnd_4740504 2434157096561425989998825 := by
  unfold tailWord_4740504
  simp only [CollatzResearch.WordTrace]
  refine ⟨86450192608985548235838283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115266923478647397647784377 86450192608985548235838283)
  ·
    refine ⟨129675288913478322353757425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86450192608985548235838283 129675288913478322353757425)
    ·
      refine ⟨97256466685108741765318069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129675288913478322353757425 97256466685108741765318069)
      ·
        refine ⟨9117793751728944540498569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97256466685108741765318069 9117793751728944540498569)
        ·
          refine ⟨6838345313796708405373927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9117793751728944540498569 6838345313796708405373927)
          ·
            refine ⟨10257517970695062608060891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838345313796708405373927 10257517970695062608060891)
            ·
              refine ⟨15386276956042593912091337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10257517970695062608060891 15386276956042593912091337)
              ·
                refine ⟨11539707717031945434068503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15386276956042593912091337 11539707717031945434068503)
                ·
                  refine ⟨17309561575547918151102755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11539707717031945434068503 17309561575547918151102755)
                  ·
                    refine ⟨25964342363321877226654133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17309561575547918151102755 25964342363321877226654133)
                    ·
                      refine ⟨2434157096561425989998825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25964342363321877226654133 2434157096561425989998825)
                      ·
                        rfl

theorem cell23_4740504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4740504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740504 prefixEnd_4740504 := by exact prefixLift 4740504
  have htrace : WordTrace (prefixWord ++ tailWord_4740504) baseStart_4740504 baseEnd_4740504 := by
    simpa [prefixWord, tailWord_4740504, baseEnd_4740504] using wordTrace_append hprefix tailTrace_4740504
  have hstable : (prefixWord ++ tailWord_4740504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740504).length < 2 ^ (prefixWord ++ tailWord_4740504).sum := by decide
  have hdescent : baseEnd_4740504 < baseStart_4740504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740511 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 2, 4]
def baseStart_4740511 : Nat := 118140960795 + 4740511 * 2 ^ 59
def prefixEnd_4740511 : Nat := 4983230072969 + 3 ^ 40 * 4740511 * 2
def baseEnd_4740511 : Nat := 811386896975335820870431

theorem tailTrace_4740511 : CollatzResearch.WordTrace tailWord_4740511 prefixEnd_4740511 811386896975335820870431 := by
  unfold tailWord_4740511
  simp only [CollatzResearch.WordTrace]
  refine ⟨172900640528945736667181387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115267093685963824444787591 172900640528945736667181387)
  ·
    refine ⟨259350960793418605000772081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172900640528945736667181387 259350960793418605000772081)
    ·
      refine ⟨194513220595063953750579061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259350960793418605000772081 194513220595063953750579061)
      ·
        refine ⟨18235614430787245664116787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194513220595063953750579061 18235614430787245664116787)
        ·
          refine ⟨27353421646180868496175181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18235614430787245664116787 27353421646180868496175181)
          ·
            refine ⟨10257533117317825686065693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27353421646180868496175181 10257533117317825686065693)
            ·
              refine ⟨3846574918994184632274635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10257533117317825686065693 3846574918994184632274635)
              ·
                refine ⟨5769862378491276948411953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846574918994184632274635 5769862378491276948411953)
                ·
                  refine ⟨4327396783868457711308965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5769862378491276948411953 4327396783868457711308965)
                  ·
                    refine ⟨811386896975335820870431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327396783868457711308965 811386896975335820870431)
                    ·
                      rfl

theorem cell23_4740511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 4].length) (baseStart_4740511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740511 prefixEnd_4740511 := by exact prefixLift 4740511
  have htrace : WordTrace (prefixWord ++ tailWord_4740511) baseStart_4740511 baseEnd_4740511 := by
    simpa [prefixWord, tailWord_4740511, baseEnd_4740511] using wordTrace_append hprefix tailTrace_4740511
  have hstable : (prefixWord ++ tailWord_4740511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740511).length < 2 ^ (prefixWord ++ tailWord_4740511).sum := by decide
  have hdescent : baseEnd_4740511 < baseStart_4740511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740514 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4740514 : Nat := 118140960795 + 4740514 * 2 ^ 59
def prefixEnd_4740514 : Nat := 4983230072969 + 3 ^ 40 * 4740514 * 2
def baseEnd_4740514 : Nat := 2434162231367970950873779

theorem tailTrace_4740514 : CollatzResearch.WordTrace tailWord_4740514 prefixEnd_4740514 2434162231367970950873779 := by
  unfold tailWord_4740514
  simp only [CollatzResearch.WordTrace]
  refine ⟨43225187486983717044885149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115267166631956578786360397 43225187486983717044885149)
  ·
    refine ⟨16209445307618893891831931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43225187486983717044885149 16209445307618893891831931)
    ·
      refine ⟨24314167961428340837747897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16209445307618893891831931 24314167961428340837747897)
      ·
        refine ⟨18235625971071255628310923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24314167961428340837747897 18235625971071255628310923)
        ·
          refine ⟨27353438956606883442466385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18235625971071255628310923 27353438956606883442466385)
          ·
            refine ⟨20515079217455162581849789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27353438956606883442466385 20515079217455162581849789)
            ·
              refine ⟨7693154706545685968193671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20515079217455162581849789 7693154706545685968193671)
              ·
                refine ⟨11539732059818528952290507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7693154706545685968193671 11539732059818528952290507)
                ·
                  refine ⟨17309598089727793428435761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11539732059818528952290507 17309598089727793428435761)
                  ·
                    refine ⟨12982198567295845071326821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17309598089727793428435761 12982198567295845071326821)
                    ·
                      refine ⟨2434162231367970950873779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12982198567295845071326821 2434162231367970950873779)
                      ·
                        rfl

theorem cell23_4740514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4740514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740514 prefixEnd_4740514 := by exact prefixLift 4740514
  have htrace : WordTrace (prefixWord ++ tailWord_4740514) baseStart_4740514 baseEnd_4740514 := by
    simpa [prefixWord, tailWord_4740514, baseEnd_4740514] using wordTrace_append hprefix tailTrace_4740514
  have hstable : (prefixWord ++ tailWord_4740514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740514).length < 2 ^ (prefixWord ++ tailWord_4740514).sum := by decide
  have hdescent : baseEnd_4740514 < baseStart_4740514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740517 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_4740517 : Nat := 118140960795 + 4740517 * 2 ^ 59
def prefixEnd_4740517 : Nat := 4983230072969 + 3 ^ 40 * 4740517 * 2
def baseEnd_4740517 : Nat := 2434163771809934439136265

theorem tailTrace_4740517 : CollatzResearch.WordTrace tailWord_4740517 prefixEnd_4740517 2434163771809934439136265 := by
  unfold tailWord_4740517
  simp only [CollatzResearch.WordTrace]
  refine ⟨172900859366923999691899805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115267239577949333127933203 172900859366923999691899805)
  ·
    refine ⟨64837822262596499884462427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172900859366923999691899805 64837822262596499884462427)
    ·
      refine ⟨97256733393894749826693641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64837822262596499884462427 97256733393894749826693641)
      ·
        refine ⟨72942550045421062370020231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97256733393894749826693641 72942550045421062370020231)
        ·
          refine ⟨109413825068131593555030347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72942550045421062370020231 109413825068131593555030347)
          ·
            refine ⟨164120737602197390332545521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109413825068131593555030347 164120737602197390332545521)
            ·
              refine ⟨123090553201648042749409141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164120737602197390332545521 123090553201648042749409141)
              ·
                refine ⟨11539739362654504007757107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123090553201648042749409141 11539739362654504007757107)
                ·
                  refine ⟨17309609043981756011635661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11539739362654504007757107 17309609043981756011635661)
                  ·
                    refine ⟨6491103391493158504363373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17309609043981756011635661 6491103391493158504363373)
                    ·
                      refine ⟨2434163771809934439136265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6491103391493158504363373 2434163771809934439136265)
                      ·
                        rfl

theorem cell23_4740517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_4740517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740517 prefixEnd_4740517 := by exact prefixLift 4740517
  have htrace : WordTrace (prefixWord ++ tailWord_4740517) baseStart_4740517 baseEnd_4740517 := by
    simpa [prefixWord, tailWord_4740517, baseEnd_4740517] using wordTrace_append hprefix tailTrace_4740517
  have hstable : (prefixWord ++ tailWord_4740517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740517).length < 2 ^ (prefixWord ++ tailWord_4740517).sum := by decide
  have hdescent : baseEnd_4740517 < baseStart_4740517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740527 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 7, 2]
def baseStart_4740527 : Nat := 118140960795 + 4740527 * 2 ^ 59
def prefixEnd_4740527 : Nat := 4983230072969 + 3 ^ 40 * 4740527 * 2
def baseEnd_4740527 : Nat := 2434168906616479400011219

theorem tailTrace_4740527 : CollatzResearch.WordTrace tailWord_4740527 prefixEnd_4740527 2434168906616479400011219 := by
  unfold tailWord_4740527
  simp only [CollatzResearch.WordTrace]
  refine ⟨172901224096887771399763835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115267482731258514266509223 172901224096887771399763835)
  ·
    refine ⟨259351836145331657099645753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172901224096887771399763835 259351836145331657099645753)
    ·
      refine ⟨194513877108998742824734315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259351836145331657099645753 194513877108998742824734315)
      ·
        refine ⟨291770815663498114237101473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194513877108998742824734315 291770815663498114237101473)
        ·
          refine ⟨218828111747623585677826105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291770815663498114237101473 218828111747623585677826105)
          ·
            refine ⟨164121083810717689258369579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218828111747623585677826105 164121083810717689258369579)
            ·
              refine ⟨246181625716076533887554369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164121083810717689258369579 246181625716076533887554369)
              ·
                refine ⟨184636219287057400415665777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246181625716076533887554369 184636219287057400415665777)
                ·
                  refine ⟨138477164465293050311749333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184636219287057400415665777 138477164465293050311749333)
                  ·
                    refine ⟨3245558542155305866681625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138477164465293050311749333 3245558542155305866681625)
                    ·
                      refine ⟨2434168906616479400011219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245558542155305866681625 2434168906616479400011219)
                      ·
                        rfl

theorem cell23_4740527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7, 2].length) (baseStart_4740527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740527 prefixEnd_4740527 := by exact prefixLift 4740527
  have htrace : WordTrace (prefixWord ++ tailWord_4740527) baseStart_4740527 baseEnd_4740527 := by
    simpa [prefixWord, tailWord_4740527, baseEnd_4740527] using wordTrace_append hprefix tailTrace_4740527
  have hstable : (prefixWord ++ tailWord_4740527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740527).length < 2 ^ (prefixWord ++ tailWord_4740527).sum := by decide
  have hdescent : baseEnd_4740527 < baseStart_4740527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740546 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4740546 : Nat := 118140960795 + 4740546 * 2 ^ 59
def prefixEnd_4740546 : Nat := 4983230072969 + 3 ^ 40 * 4740546 * 2
def baseEnd_4740546 : Nat := 2434178662748914825673633

theorem tailTrace_4740546 : CollatzResearch.WordTrace tailWord_4740546 prefixEnd_4740546 2434178662748914825673633 := by
  unfold tailWord_4740546
  simp only [CollatzResearch.WordTrace]
  refine ⟨43225479270954734411176373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115267944722545958429803661 43225479270954734411176373)
  ·
    refine ⟨4052388681652006351047785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43225479270954734411176373 4052388681652006351047785)
    ·
      refine ⟨3039291511239004763285839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4052388681652006351047785 3039291511239004763285839)
      ·
        refine ⟨4558937266858507144928759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039291511239004763285839 4558937266858507144928759)
        ·
          refine ⟨6838405900287760717393139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558937266858507144928759 6838405900287760717393139)
          ·
            refine ⟨10257608850431641076089709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838405900287760717393139 10257608850431641076089709)
            ·
              refine ⟨3846603318911865403533641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10257608850431641076089709 3846603318911865403533641)
              ·
                refine ⟨2884952489183899052650231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3846603318911865403533641 2884952489183899052650231)
                ·
                  refine ⟨4327428733775848578975347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884952489183899052650231 4327428733775848578975347)
                  ·
                    refine ⟨6491143100663772868463021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4327428733775848578975347 6491143100663772868463021)
                    ·
                      refine ⟨2434178662748914825673633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6491143100663772868463021 2434178662748914825673633)
                      ·
                        rfl

theorem cell23_4740546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4740546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740546 prefixEnd_4740546 := by exact prefixLift 4740546
  have htrace : WordTrace (prefixWord ++ tailWord_4740546) baseStart_4740546 baseEnd_4740546 := by
    simpa [prefixWord, tailWord_4740546, baseEnd_4740546] using wordTrace_append hprefix tailTrace_4740546
  have hstable : (prefixWord ++ tailWord_4740546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740546).length < 2 ^ (prefixWord ++ tailWord_4740546).sum := by decide
  have hdescent : baseEnd_4740546 < baseStart_4740546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740577 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_4740577 : Nat := 118140960795 + 4740577 * 2 ^ 59
def prefixEnd_4740577 : Nat := 4983230072969 + 3 ^ 40 * 4740577 * 2
def baseEnd_4740577 : Nat := 2434194580649204204385989

theorem tailTrace_4740577 : CollatzResearch.WordTrace tailWord_4740577 prefixEnd_4740577 2434194580649204204385989 := by
  unfold tailWord_4740577
  simp only [CollatzResearch.WordTrace]
  refine ⟨172903047746706629939083985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115268698497804419959389323 172903047746706629939083985)
  ·
    refine ⟨129677285810029972454312989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172903047746706629939083985 129677285810029972454312989)
    ·
      refine ⟨48628982178761239670367371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129677285810029972454312989 48628982178761239670367371)
      ·
        refine ⟨72943473268141859505551057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48628982178761239670367371 72943473268141859505551057)
        ·
          refine ⟨54707604951106394629163293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72943473268141859505551057 54707604951106394629163293)
          ·
            refine ⟨20515351856664897985936235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54707604951106394629163293 20515351856664897985936235)
            ·
              refine ⟨30773027784997346978904353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20515351856664897985936235 30773027784997346978904353)
              ·
                refine ⟨23079770838748010234178265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30773027784997346978904353 23079770838748010234178265)
                ·
                  refine ⟨17309828129061007675633699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23079770838748010234178265 17309828129061007675633699)
                  ·
                    refine ⟨25964742193591511513450549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17309828129061007675633699 25964742193591511513450549)
                    ·
                      refine ⟨2434194580649204204385989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25964742193591511513450549 2434194580649204204385989)
                      ·
                        rfl

theorem cell23_4740577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_4740577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740577 prefixEnd_4740577 := by exact prefixLift 4740577
  have htrace : WordTrace (prefixWord ++ tailWord_4740577) baseStart_4740577 baseEnd_4740577 := by
    simpa [prefixWord, tailWord_4740577, baseEnd_4740577] using wordTrace_append hprefix tailTrace_4740577
  have hstable : (prefixWord ++ tailWord_4740577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740577).length < 2 ^ (prefixWord ++ tailWord_4740577).sum := by decide
  have hdescent : baseEnd_4740577 < baseStart_4740577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740594 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4740594 : Nat := 118140960795 + 4740594 * 2 ^ 59
def prefixEnd_4740594 : Nat := 4983230072969 + 3 ^ 40 * 4740594 * 2
def baseEnd_4740594 : Nat := 2434203309820330637873411

theorem tailTrace_4740594 : CollatzResearch.WordTrace tailWord_4740594 prefixEnd_4740594 2434203309820330637873411 := by
  unfold tailWord_4740594
  simp only [CollatzResearch.WordTrace]
  refine ⟨43225916946911260460613209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115269111858430027894968557 43225916946911260460613209)
  ·
    refine ⟨32419437710183445345459907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43225916946911260460613209 32419437710183445345459907)
    ·
      refine ⟨48629156565275168018189861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32419437710183445345459907 48629156565275168018189861)
      ·
        refine ⟨9117966855989094003410599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48629156565275168018189861 9117966855989094003410599)
        ·
          refine ⟨13676950283983641005115899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117966855989094003410599 13676950283983641005115899)
          ·
            refine ⟨20515425425975461507673849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13676950283983641005115899 20515425425975461507673849)
            ·
              refine ⟨15386569069481596130755387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20515425425975461507673849 15386569069481596130755387)
              ·
                refine ⟨23079853604222394196133081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15386569069481596130755387 23079853604222394196133081)
                ·
                  refine ⟨17309890203166795647099811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23079853604222394196133081 17309890203166795647099811)
                  ·
                    refine ⟨25964835304750193470649717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17309890203166795647099811 25964835304750193470649717)
                    ·
                      refine ⟨2434203309820330637873411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25964835304750193470649717 2434203309820330637873411)
                      ·
                        rfl

theorem cell23_4740594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4740594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740594 prefixEnd_4740594 := by exact prefixLift 4740594
  have htrace : WordTrace (prefixWord ++ tailWord_4740594) baseStart_4740594 baseEnd_4740594 := by
    simpa [prefixWord, tailWord_4740594, baseEnd_4740594] using wordTrace_append hprefix tailTrace_4740594
  have hstable : (prefixWord ++ tailWord_4740594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740594).length < 2 ^ (prefixWord ++ tailWord_4740594).sum := by decide
  have hdescent : baseEnd_4740594 < baseStart_4740594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740634 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2]
def baseStart_4740634 : Nat := 118140960795 + 4740634 * 2 ^ 59
def prefixEnd_4740634 : Nat := 4983230072969 + 3 ^ 40 * 4740634 * 2
def baseEnd_4740634 : Nat := 2434223849046510481373227

theorem tailTrace_4740634 : CollatzResearch.WordTrace tailWord_4740634 prefixEnd_4740634 2434223849046510481373227 := by
  unfold tailWord_4740634
  simp only [CollatzResearch.WordTrace]
  refine ⟨43226281676875032168477239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115270084471666752449272637 43226281676875032168477239)
  ·
    refine ⟨64839422515312548252715859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43226281676875032168477239 64839422515312548252715859)
    ·
      refine ⟨97259133772968822379073789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64839422515312548252715859 97259133772968822379073789)
      ·
        refine ⟨36472175164863308392152671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97259133772968822379073789 36472175164863308392152671)
        ·
          refine ⟨54708262747294962588229007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36472175164863308392152671 54708262747294962588229007)
          ·
            refine ⟨82062394120942443882343511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54708262747294962588229007 82062394120942443882343511)
            ·
              refine ⟨123093591181413665823515267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82062394120942443882343511 123093591181413665823515267)
              ·
                refine ⟨184640386772120498735272901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123093591181413665823515267 184640386772120498735272901)
                ·
                  refine ⟨34620072519772593512863669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184640386772120498735272901 34620072519772593512863669)
                  ·
                    refine ⟨3245631798728680641830969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34620072519772593512863669 3245631798728680641830969)
                    ·
                      refine ⟨2434223849046510481373227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245631798728680641830969 2434223849046510481373227)
                      ·
                        rfl

theorem cell23_4740634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_4740634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740634 prefixEnd_4740634 := by exact prefixLift 4740634
  have htrace : WordTrace (prefixWord ++ tailWord_4740634) baseStart_4740634 baseEnd_4740634 := by
    simpa [prefixWord, tailWord_4740634, baseEnd_4740634] using wordTrace_append hprefix tailTrace_4740634
  have hstable : (prefixWord ++ tailWord_4740634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740634).length < 2 ^ (prefixWord ++ tailWord_4740634).sum := by decide
  have hdescent : baseEnd_4740634 < baseStart_4740634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740648 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 5]
def baseStart_4740648 : Nat := 118140960795 + 4740648 * 2 ^ 59
def prefixEnd_4740648 : Nat := 4983230072969 + 3 ^ 40 * 4740648 * 2
def baseEnd_4740648 : Nat := 270470115308408158510907

theorem tailTrace_4740648 : CollatzResearch.WordTrace tailWord_4740648 prefixEnd_4740648 270470115308408158510907 := by
  unfold tailWord_4740648
  simp only [CollatzResearch.WordTrace]
  refine ⟨86452818664724704532459299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115270424886299606043279065 86452818664724704532459299)
  ·
    refine ⟨129679227997087056798688949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86452818664724704532459299 129679227997087056798688949)
    ·
      refine ⟨12157427624726911574877089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129679227997087056798688949 12157427624726911574877089)
      ·
        refine ⟨9118070718545183681157817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12157427624726911574877089 9118070718545183681157817)
        ·
          refine ⟨6838553038908887760868363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9118070718545183681157817 6838553038908887760868363)
          ·
            refine ⟨10257829558363331641302545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838553038908887760868363 10257829558363331641302545)
            ·
              refine ⟨7693372168772498730976909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10257829558363331641302545 7693372168772498730976909)
              ·
                refine ⟨2885014563289687024116341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7693372168772498730976909 2885014563289687024116341)
                ·
                  refine ⟨270470115308408158510907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2885014563289687024116341 270470115308408158510907)
                  ·
                    rfl

theorem cell23_4740648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 5].length) (baseStart_4740648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740648 prefixEnd_4740648 := by exact prefixLift 4740648
  have htrace : WordTrace (prefixWord ++ tailWord_4740648) baseStart_4740648 baseEnd_4740648 := by
    simpa [prefixWord, tailWord_4740648, baseEnd_4740648] using wordTrace_append hprefix tailTrace_4740648
  have hstable : (prefixWord ++ tailWord_4740648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740648).length < 2 ^ (prefixWord ++ tailWord_4740648).sum := by decide
  have hdescent : baseEnd_4740648 < baseStart_4740648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740677 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_4740677 : Nat := 118140960795 + 4740677 * 2 ^ 59
def prefixEnd_4740677 : Nat := 4983230072969 + 3 ^ 40 * 4740677 * 2
def baseEnd_4740677 : Nat := 2434245928714653813135529

theorem tailTrace_4740677 : CollatzResearch.WordTrace tailWord_4740677 prefixEnd_4740677 2434245928714653813135529 := by
  unfold tailWord_4740677
  simp only [CollatzResearch.WordTrace]
  refine ⟨172906695046344347017724285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115271130030896231345149523 172906695046344347017724285)
  ·
    refine ⟨64840010642379130131646607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172906695046344347017724285 64840010642379130131646607)
    ·
      refine ⟨97260015963568695197469911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64840010642379130131646607 97260015963568695197469911)
      ·
        refine ⟨145890023945353042796204867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97260015963568695197469911 145890023945353042796204867)
        ·
          refine ⟨218835035918029564194307301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145890023945353042796204867 218835035918029564194307301)
          ·
            refine ⟨41031569234630543286432619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218835035918029564194307301 41031569234630543286432619)
            ·
              refine ⟨61547353851945814929648929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41031569234630543286432619 61547353851945814929648929)
              ·
                refine ⟨46160515388959361197236697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61547353851945814929648929 46160515388959361197236697)
                ·
                  refine ⟨34620386541719520897927523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46160515388959361197236697 34620386541719520897927523)
                  ·
                    refine ⟨51930579812579281346891285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34620386541719520897927523 51930579812579281346891285)
                    ·
                      refine ⟨2434245928714653813135529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51930579812579281346891285 2434245928714653813135529)
                      ·
                        rfl

theorem cell23_4740677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_4740677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740677 prefixEnd_4740677 := by exact prefixLift 4740677
  have htrace : WordTrace (prefixWord ++ tailWord_4740677) baseStart_4740677 baseEnd_4740677 := by
    simpa [prefixWord, tailWord_4740677, baseEnd_4740677] using wordTrace_append hprefix tailTrace_4740677
  have hstable : (prefixWord ++ tailWord_4740677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740677).length < 2 ^ (prefixWord ++ tailWord_4740677).sum := by decide
  have hdescent : baseEnd_4740677 < baseStart_4740677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740684 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_4740684 : Nat := 118140960795 + 4740684 * 2 ^ 59
def prefixEnd_4740684 : Nat := 4983230072969 + 3 ^ 40 * 4740684 * 2
def baseEnd_4740684 : Nat := 2434249523079235285747997

theorem tailTrace_4740684 : CollatzResearch.WordTrace tailWord_4740684 prefixEnd_4740684 2434249523079235285747997 := by
  unfold tailWord_4740684
  simp only [CollatzResearch.WordTrace]
  refine ⟨86453475178659493606614553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115271300238212658142152737 86453475178659493606614553)
  ·
    refine ⟨64840106383994620204960915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86453475178659493606614553 64840106383994620204960915)
    ·
      refine ⟨97260159575991930307441373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64840106383994620204960915 97260159575991930307441373)
      ·
        refine ⟨36472559840996973865290515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97260159575991930307441373 36472559840996973865290515)
        ·
          refine ⟨54708839761495460797935773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36472559840996973865290515 54708839761495460797935773)
          ·
            refine ⟨20515814910560797799225915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54708839761495460797935773 20515814910560797799225915)
            ·
              refine ⟨30773722365841196698838873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20515814910560797799225915 30773722365841196698838873)
              ·
                refine ⟨23080291774380897524129155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30773722365841196698838873 23080291774380897524129155)
                ·
                  refine ⟨34620437661571346286193733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23080291774380897524129155 34620437661571346286193733)
                  ·
                    refine ⟨6491332061544627428661325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34620437661571346286193733 6491332061544627428661325)
                    ·
                      refine ⟨2434249523079235285747997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6491332061544627428661325 2434249523079235285747997)
                      ·
                        rfl

theorem cell23_4740684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_4740684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740684 prefixEnd_4740684 := by exact prefixLift 4740684
  have htrace : WordTrace (prefixWord ++ tailWord_4740684) baseStart_4740684 baseEnd_4740684 := by
    simpa [prefixWord, tailWord_4740684, baseEnd_4740684] using wordTrace_append hprefix tailTrace_4740684
  have hstable : (prefixWord ++ tailWord_4740684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740684).length < 2 ^ (prefixWord ++ tailWord_4740684).sum := by decide
  have hdescent : baseEnd_4740684 < baseStart_4740684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740708 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_4740708 : Nat := 118140960795 + 4740708 * 2 ^ 59
def prefixEnd_4740708 : Nat := 4983230072969 + 3 ^ 40 * 4740708 * 2
def baseEnd_4740708 : Nat := 811420615538314397282629

theorem tailTrace_4740708 : CollatzResearch.WordTrace tailWord_4740708 prefixEnd_4740708 811420615538314397282629 := by
  unfold tailWord_4740708
  simp only [CollatzResearch.WordTrace]
  refine ⟨86453912854616019656051389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115271883806154692874735185 86453912854616019656051389)
  ·
    refine ⟨32420217320481007371019271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86453912854616019656051389 32420217320481007371019271)
    ·
      refine ⟨48630325980721511056528907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32420217320481007371019271 48630325980721511056528907)
      ·
        refine ⟨72945488971082266584793361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48630325980721511056528907 72945488971082266584793361)
        ·
          refine ⟨54709116728311699938595021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72945488971082266584793361 54709116728311699938595021)
          ·
            refine ⟨20515918773116887476973133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54709116728311699938595021 20515918773116887476973133)
            ·
              refine ⟨7693469539918832803864925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20515918773116887476973133 7693469539918832803864925)
              ·
                refine ⟨2885051077469562301449347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7693469539918832803864925 2885051077469562301449347)
                ·
                  refine ⟨4327576616204343452174021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885051077469562301449347 4327576616204343452174021)
                  ·
                    refine ⟨811420615538314397282629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327576616204343452174021 811420615538314397282629)
                    ·
                      rfl

theorem cell23_4740708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_4740708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740708 prefixEnd_4740708 := by exact prefixLift 4740708
  have htrace : WordTrace (prefixWord ++ tailWord_4740708) baseStart_4740708 baseEnd_4740708 := by
    simpa [prefixWord, tailWord_4740708, baseEnd_4740708] using wordTrace_append hprefix tailTrace_4740708
  have hstable : (prefixWord ++ tailWord_4740708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740708).length < 2 ^ (prefixWord ++ tailWord_4740708).sum := by decide
  have hdescent : baseEnd_4740708 < baseStart_4740708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740718 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4740718 : Nat := 118140960795 + 4740718 * 2 ^ 59
def prefixEnd_4740718 : Nat := 4983230072969 + 3 ^ 40 * 4740718 * 2
def baseEnd_4740718 : Nat := 2434266981421488152722841

theorem tailTrace_4740718 : CollatzResearch.WordTrace tailWord_4740718 prefixEnd_4740718 2434266981421488152722841 := by
  unfold tailWord_4740718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21613523804899476377495851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115272126959463874013311205 21613523804899476377495851)
  ·
    refine ⟨32420285707349214566243777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21613523804899476377495851 32420285707349214566243777)
    ·
      refine ⟨24315214280511910924682833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32420285707349214566243777 24315214280511910924682833)
      ·
        refine ⟨18236410710383933193512125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24315214280511910924682833 18236410710383933193512125)
        ·
          refine ⟨6838654016393974947567047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18236410710383933193512125 6838654016393974947567047)
          ·
            refine ⟨10257981024590962421350571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838654016393974947567047 10257981024590962421350571)
            ·
              refine ⟨15386971536886443632025857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10257981024590962421350571 15386971536886443632025857)
              ·
                refine ⟨11540228652664832724019393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15386971536886443632025857 11540228652664832724019393)
                ·
                  refine ⟨8655171489498624543014545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11540228652664832724019393 8655171489498624543014545)
                  ·
                    refine ⟨6491378617123968407260909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8655171489498624543014545 6491378617123968407260909)
                    ·
                      refine ⟨2434266981421488152722841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6491378617123968407260909 2434266981421488152722841)
                      ·
                        rfl

theorem cell23_4740718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4740718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740718 prefixEnd_4740718 := by exact prefixLift 4740718
  have htrace : WordTrace (prefixWord ++ tailWord_4740718) baseStart_4740718 baseEnd_4740718 := by
    simpa [prefixWord, tailWord_4740718, baseEnd_4740718] using wordTrace_append hprefix tailTrace_4740718
  have hstable : (prefixWord ++ tailWord_4740718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740718).length < 2 ^ (prefixWord ++ tailWord_4740718).sum := by decide
  have hdescent : baseEnd_4740718 < baseStart_4740718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740727 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_4740727 : Nat := 118140960795 + 4740727 * 2 ^ 59
def prefixEnd_4740727 : Nat := 4983230072969 + 3 ^ 40 * 4740727 * 2
def baseEnd_4740727 : Nat := 2434271602747378617510299

theorem tailTrace_4740727 : CollatzResearch.WordTrace tailWord_4740727 prefixEnd_4740727 2434271602747378617510299 := by
  unfold tailWord_4740727
  simp only [CollatzResearch.WordTrace]
  refine ⟨172908518696163205557044435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115272345797442137038029623 172908518696163205557044435)
  ·
    refine ⟨259362778044244808335566653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172908518696163205557044435 259362778044244808335566653)
    ·
      refine ⟨97261041766591803125837495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259362778044244808335566653 97261041766591803125837495)
      ·
        refine ⟨145891562649887704688756243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97261041766591803125837495 145891562649887704688756243)
        ·
          refine ⟨218837343974831557033134365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145891562649887704688756243 218837343974831557033134365)
          ·
            refine ⟨82064003990561833887425387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218837343974831557033134365 82064003990561833887425387)
            ·
              refine ⟨123096005985842750831138081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82064003990561833887425387 123096005985842750831138081)
              ·
                refine ⟨92322004489382063123353561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123096005985842750831138081 92322004489382063123353561)
                ·
                  refine ⟨69241503367036547342515171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92322004489382063123353561 69241503367036547342515171)
                  ·
                    refine ⟨103862255050554821013772757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69241503367036547342515171 103862255050554821013772757)
                    ·
                      refine ⟨2434271602747378617510299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103862255050554821013772757 2434271602747378617510299)
                      ·
                        rfl

theorem cell23_4740727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_4740727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740727 prefixEnd_4740727 := by exact prefixLift 4740727
  have htrace : WordTrace (prefixWord ++ tailWord_4740727) baseStart_4740727 baseEnd_4740727 := by
    simpa [prefixWord, tailWord_4740727, baseEnd_4740727] using wordTrace_append hprefix tailTrace_4740727
  have hstable : (prefixWord ++ tailWord_4740727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740727).length < 2 ^ (prefixWord ++ tailWord_4740727).sum := by decide
  have hdescent : baseEnd_4740727 < baseStart_4740727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740741 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 4, 3, 2]
def baseStart_4740741 : Nat := 118140960795 + 4740741 * 2 ^ 59
def prefixEnd_4740741 : Nat := 4983230072969 + 3 ^ 40 * 4740741 * 2
def baseEnd_4740741 : Nat := 2434278791476541562735235

theorem tailTrace_4740741 : CollatzResearch.WordTrace tailWord_4740741 prefixEnd_4740741 2434278791476541562735235 := by
  unfold tailWord_4740741
  simp only [CollatzResearch.WordTrace]
  refine ⟨172909029318112485948054077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115272686212074990632036051 172909029318112485948054077)
  ·
    refine ⟨64840885994292182230520279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172909029318112485948054077 64840885994292182230520279)
    ·
      refine ⟨97261328991438273345780419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64840885994292182230520279 97261328991438273345780419)
      ·
        refine ⟨145891993487157410018670629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97261328991438273345780419 145891993487157410018670629)
        ·
          refine ⟨27354748778842014378500743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145891993487157410018670629 27354748778842014378500743)
          ·
            refine ⟨41032123168263021567751115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27354748778842014378500743 41032123168263021567751115)
            ·
              refine ⟨61548184752394532351626673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41032123168263021567751115 61548184752394532351626673)
              ·
                refine ⟨46161138564295899263720005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61548184752394532351626673 46161138564295899263720005)
                ·
                  refine ⟨8655213480805481111947501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46161138564295899263720005 8655213480805481111947501)
                  ·
                    refine ⟨3245705055302055416980313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8655213480805481111947501 3245705055302055416980313)
                    ·
                      refine ⟨2434278791476541562735235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245705055302055416980313 2434278791476541562735235)
                      ·
                        rfl

theorem cell23_4740741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_4740741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740741 prefixEnd_4740741 := by exact prefixLift 4740741
  have htrace : WordTrace (prefixWord ++ tailWord_4740741) baseStart_4740741 baseEnd_4740741 := by
    simpa [prefixWord, tailWord_4740741, baseEnd_4740741] using wordTrace_append hprefix tailTrace_4740741
  have hstable : (prefixWord ++ tailWord_4740741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740741).length < 2 ^ (prefixWord ++ tailWord_4740741).sum := by decide
  have hdescent : baseEnd_4740741 < baseStart_4740741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740768 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 1, 5]
def baseStart_4740768 : Nat := 118140960795 + 4740768 * 2 ^ 59
def prefixEnd_4740768 : Nat := 4983230072969 + 3 ^ 40 * 4740768 * 2
def baseEnd_4740768 : Nat := 811430885151404319032537

theorem tailTrace_4740768 : CollatzResearch.WordTrace tailWord_4740768 prefixEnd_4740768 811430885151404319032537 := by
  unfold tailWord_4740768
  simp only [CollatzResearch.WordTrace]
  refine ⟨86455007044507334779643479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115273342726009779706191305 86455007044507334779643479)
  ·
    refine ⟨129682510566761002169465219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86455007044507334779643479 129682510566761002169465219)
    ·
      refine ⟨194523765850141503254197829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129682510566761002169465219 194523765850141503254197829)
      ·
        refine ⟨36473206096901531860162093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194523765850141503254197829 36473206096901531860162093)
        ·
          refine ⟨13677452286338074447560785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36473206096901531860162093 13677452286338074447560785)
          ·
            refine ⟨10258089214753555835670589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13677452286338074447560785 10258089214753555835670589)
            ·
              refine ⟨3846783455532583438376471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10258089214753555835670589 3846783455532583438376471)
              ·
                refine ⟨5770175183298875157564707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846783455532583438376471 5770175183298875157564707)
                ·
                  refine ⟨8655262774948312736347061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770175183298875157564707 8655262774948312736347061)
                  ·
                    refine ⟨811430885151404319032537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8655262774948312736347061 811430885151404319032537)
                    ·
                      rfl

theorem cell23_4740768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 5].length) (baseStart_4740768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740768 prefixEnd_4740768 := by exact prefixLift 4740768
  have htrace : WordTrace (prefixWord ++ tailWord_4740768) baseStart_4740768 baseEnd_4740768 := by
    simpa [prefixWord, tailWord_4740768, baseEnd_4740768] using wordTrace_append hprefix tailTrace_4740768
  have hstable : (prefixWord ++ tailWord_4740768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740768).length < 2 ^ (prefixWord ++ tailWord_4740768).sum := by decide
  have hdescent : baseEnd_4740768 < baseStart_4740768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740776 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4740776 : Nat := 118140960795 + 4740776 * 2 ^ 59
def prefixEnd_4740776 : Nat := 4983230072969 + 3 ^ 40 * 4740776 * 2
def baseEnd_4740776 : Nat := 811432254433149641932525

theorem tailTrace_4740776 : CollatzResearch.WordTrace tailWord_4740776 prefixEnd_4740776 811432254433149641932525 := by
  unfold tailWord_4740776
  simp only [CollatzResearch.WordTrace]
  refine ⟨86455152936492843462789091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115273537248657124617052121 86455152936492843462789091)
  ·
    refine ⟨129682729404739265194183637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86455152936492843462789091 129682729404739265194183637)
    ·
      refine ⟨3039438970423576527988679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 129682729404739265194183637 3039438970423576527988679)
      ·
        refine ⟨4559158455635364791983019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039438970423576527988679 4559158455635364791983019)
        ·
          refine ⟨6838737683453047187974529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559158455635364791983019 6838737683453047187974529)
          ·
            refine ⟨5129053262589785390980897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6838737683453047187974529 5129053262589785390980897)
            ·
              refine ⟨3846789946942339043235673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129053262589785390980897 3846789946942339043235673)
              ·
                refine ⟨2885092460206754282426755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3846789946942339043235673 2885092460206754282426755)
                ·
                  refine ⟨4327638690310131423640133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885092460206754282426755 4327638690310131423640133)
                  ·
                    refine ⟨811432254433149641932525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327638690310131423640133 811432254433149641932525)
                    ·
                      rfl

theorem cell23_4740776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4740776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740776 prefixEnd_4740776 := by exact prefixLift 4740776
  have htrace : WordTrace (prefixWord ++ tailWord_4740776) baseStart_4740776 baseEnd_4740776 := by
    simpa [prefixWord, tailWord_4740776, baseEnd_4740776] using wordTrace_append hprefix tailTrace_4740776
  have hstable : (prefixWord ++ tailWord_4740776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740776).length < 2 ^ (prefixWord ++ tailWord_4740776).sum := by decide
  have hdescent : baseEnd_4740776 < baseStart_4740776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740791 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_4740791 : Nat := 118140960795 + 4740791 * 2 ^ 59
def prefixEnd_4740791 : Nat := 4983230072969 + 3 ^ 40 * 4740791 * 2
def baseEnd_4740791 : Nat := 2434304465509266367110005

theorem tailTrace_4740791 : CollatzResearch.WordTrace tailWord_4740791 prefixEnd_4740791 2434304465509266367110005 := by
  unfold tailWord_4740791
  simp only [CollatzResearch.WordTrace]
  refine ⟨172910852967931344487374227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115273901978620896324916151 172910852967931344487374227)
  ·
    refine ⟨259366279451897016731061341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172910852967931344487374227 259366279451897016731061341)
    ·
      refine ⟨97262354794461381274148003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259366279451897016731061341 97262354794461381274148003)
      ·
        refine ⟨145893532191692071911222005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97262354794461381274148003 145893532191692071911222005)
        ·
          refine ⟨13677518642971131741677063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145893532191692071911222005 13677518642971131741677063)
          ·
            refine ⟨20516277964456697612515595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13677518642971131741677063 20516277964456697612515595)
            ·
              refine ⟨30774416946685046418773393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20516277964456697612515595 30774416946685046418773393)
              ·
                refine ⟨23080812710013784814080045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30774416946685046418773393 23080812710013784814080045)
                ·
                  refine ⟨8655304766255169305280017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23080812710013784814080045 8655304766255169305280017)
                  ·
                    refine ⟨6491478574691376978960013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8655304766255169305280017 6491478574691376978960013)
                    ·
                      refine ⟨2434304465509266367110005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6491478574691376978960013 2434304465509266367110005)
                      ·
                        rfl

theorem cell23_4740791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_4740791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740791 prefixEnd_4740791 := by exact prefixLift 4740791
  have htrace : WordTrace (prefixWord ++ tailWord_4740791) baseStart_4740791 baseEnd_4740791 := by
    simpa [prefixWord, tailWord_4740791, baseEnd_4740791] using wordTrace_append hprefix tailTrace_4740791
  have hstable : (prefixWord ++ tailWord_4740791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740791).length < 2 ^ (prefixWord ++ tailWord_4740791).sum := by decide
  have hdescent : baseEnd_4740791 < baseStart_4740791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740794 : List Nat := [3, 1, 1, 1, 2, 4, 3, 8]
def baseStart_4740794 : Nat := 118140960795 + 4740794 * 2 ^ 59
def prefixEnd_4740794 : Nat := 4983230072969 + 3 ^ 40 * 4740794 * 2
def baseEnd_4740794 : Nat := 90159481701897402050833

theorem tailTrace_4740794 : CollatzResearch.WordTrace tailWord_4740794 prefixEnd_4740794 90159481701897402050833 := by
  unfold tailWord_4740794
  simp only [CollatzResearch.WordTrace]
  refine ⟨43227740596730118999933359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115273974924613650666488957 43227740596730118999933359)
  ·
    refine ⟨64841610895095178499900039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43227740596730118999933359 64841610895095178499900039)
    ·
      refine ⟨97262416342642767749850059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64841610895095178499900039 97262416342642767749850059)
      ·
        refine ⟨145893624513964151624775089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97262416342642767749850059 145893624513964151624775089)
        ·
          refine ⟨109420218385473113718581317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145893624513964151624775089 109420218385473113718581317)
          ·
            refine ⟨20516290947276208822233997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109420218385473113718581317 20516290947276208822233997)
            ·
              refine ⟨7693609105228578308337749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20516290947276208822233997 7693609105228578308337749)
              ·
                refine ⟨90159481701897402050833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7693609105228578308337749 90159481701897402050833)
                ·
                  rfl

theorem cell23_4740794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_4740794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740794 prefixEnd_4740794 := by exact prefixLift 4740794
  have htrace : WordTrace (prefixWord ++ tailWord_4740794) baseStart_4740794 baseEnd_4740794 := by
    simpa [prefixWord, tailWord_4740794, baseEnd_4740794] using wordTrace_append hprefix tailTrace_4740794
  have hstable : (prefixWord ++ tailWord_4740794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740794).length < 2 ^ (prefixWord ++ tailWord_4740794).sum := by decide
  have hdescent : baseEnd_4740794 < baseStart_4740794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740798 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4740798 : Nat := 118140960795 + 4740798 * 2 ^ 59
def prefixEnd_4740798 : Nat := 4983230072969 + 3 ^ 40 * 4740798 * 2
def baseEnd_4740798 : Nat := 811436019957949279907491

theorem tailTrace_4740798 : CollatzResearch.WordTrace tailWord_4740798 prefixEnd_4740798 811436019957949279907491 := by
  unfold tailWord_4740798
  simp only [CollatzResearch.WordTrace]
  refine ⟨21613888534863248085359881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115274072185937323121919365 21613888534863248085359881)
  ·
    refine ⟨16210416401147436064019911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21613888534863248085359881 16210416401147436064019911)
    ·
      refine ⟨24315624601721154096029867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16210416401147436064019911 24315624601721154096029867)
      ·
        refine ⟨36473436902581731144044801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24315624601721154096029867 36473436902581731144044801)
        ·
          refine ⟨27355077676936298358033601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36473436902581731144044801 27355077676936298358033601)
          ·
            refine ⟨20516308257702223768525201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27355077676936298358033601 20516308257702223768525201)
            ·
              refine ⟨15387231193276667826393901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20516308257702223768525201 15387231193276667826393901)
              ·
                refine ⟨5770211697478750434897713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15387231193276667826393901 5770211697478750434897713)
                ·
                  refine ⟨4327658773109062826173285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5770211697478750434897713 4327658773109062826173285)
                  ·
                    refine ⟨811436019957949279907491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327658773109062826173285 811436019957949279907491)
                    ·
                      rfl

theorem cell23_4740798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4740798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740798 prefixEnd_4740798 := by exact prefixLift 4740798
  have htrace : WordTrace (prefixWord ++ tailWord_4740798) baseStart_4740798 baseEnd_4740798 := by
    simpa [prefixWord, tailWord_4740798, baseEnd_4740798] using wordTrace_append hprefix tailTrace_4740798
  have hstable : (prefixWord ++ tailWord_4740798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740798).length < 2 ^ (prefixWord ++ tailWord_4740798).sum := by decide
  have hdescent : baseEnd_4740798 < baseStart_4740798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740822 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4740822 : Nat := 118140960795 + 4740822 * 2 ^ 59
def prefixEnd_4740822 : Nat := 4983230072969 + 3 ^ 40 * 4740822 * 2
def baseEnd_4740822 : Nat := 2434320383409555745822363

theorem tailTrace_4740822 : CollatzResearch.WordTrace tailWord_4740822 prefixEnd_4740822 2434320383409555745822363 := by
  unfold tailWord_4740822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806998976926189798859545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115274655753879357854501813 10806998976926189798859545)
  ·
    refine ⟨8105249232694642349144659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10806998976926189798859545 8105249232694642349144659)
    ·
      refine ⟨12157873849041963523716989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105249232694642349144659 12157873849041963523716989)
      ·
        refine ⟨4559202693390736321393871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12157873849041963523716989 4559202693390736321393871)
        ·
          refine ⟨6838804040086104482090807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559202693390736321393871 6838804040086104482090807)
          ·
            refine ⟨10258206060129156723136211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838804040086104482090807 10258206060129156723136211)
            ·
              refine ⟨15387309090193735084704317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10258206060129156723136211 15387309090193735084704317)
              ·
                refine ⟨5770240908822650656764119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15387309090193735084704317 5770240908822650656764119)
                ·
                  refine ⟨8655361363233975985146179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770240908822650656764119 8655361363233975985146179)
                  ·
                    refine ⟨12983042044850963977719269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8655361363233975985146179 12983042044850963977719269)
                    ·
                      refine ⟨2434320383409555745822363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12983042044850963977719269 2434320383409555745822363)
                      ·
                        rfl

theorem cell23_4740822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4740822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740822 prefixEnd_4740822 := by exact prefixLift 4740822
  have htrace : WordTrace (prefixWord ++ tailWord_4740822) baseStart_4740822 baseEnd_4740822 := by
    simpa [prefixWord, tailWord_4740822, baseEnd_4740822] using wordTrace_append hprefix tailTrace_4740822
  have hstable : (prefixWord ++ tailWord_4740822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740822).length < 2 ^ (prefixWord ++ tailWord_4740822).sum := by decide
  have hdescent : baseEnd_4740822 < baseStart_4740822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740825 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 1, 2, 3]
def baseStart_4740825 : Nat := 118140960795 + 4740825 * 2 ^ 59
def prefixEnd_4740825 : Nat := 4983230072969 + 3 ^ 40 * 4740825 * 2
def baseEnd_4740825 : Nat := 2434321923851519234084849

theorem tailTrace_4740825 : CollatzResearch.WordTrace tailWord_4740825 prefixEnd_4740825 2434321923851519234084849 := by
  unfold tailWord_4740825
  simp only [CollatzResearch.WordTrace]
  refine ⟨172912093049808168294111929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115274728699872112196074619 172912093049808168294111929)
  ·
    refine ⟨129684069787356126220583947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172912093049808168294111929 129684069787356126220583947)
    ·
      refine ⟨194526104681034189330875921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129684069787356126220583947 194526104681034189330875921)
      ·
        refine ⟨145894578510775641998156941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194526104681034189330875921 145894578510775641998156941)
        ·
          refine ⟨54710466941540865749308853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145894578510775641998156941 54710466941540865749308853)
          ·
            refine ⟨5129106275769456163997705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54710466941540865749308853 5129106275769456163997705)
            ·
              refine ⟨3846829706827092122998279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129106275769456163997705 3846829706827092122998279)
              ·
                refine ⟨5770244560240638184497419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846829706827092122998279 5770244560240638184497419)
                ·
                  refine ⟨8655366840360957276746129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770244560240638184497419 8655366840360957276746129)
                  ·
                    refine ⟨6491525130270717957559597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8655366840360957276746129 6491525130270717957559597)
                    ·
                      refine ⟨2434321923851519234084849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6491525130270717957559597 2434321923851519234084849)
                      ·
                        rfl

theorem cell23_4740825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_4740825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740825 prefixEnd_4740825 := by exact prefixLift 4740825
  have htrace : WordTrace (prefixWord ++ tailWord_4740825) baseStart_4740825 baseEnd_4740825 := by
    simpa [prefixWord, tailWord_4740825, baseEnd_4740825] using wordTrace_append hprefix tailTrace_4740825
  have hstable : (prefixWord ++ tailWord_4740825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740825).length < 2 ^ (prefixWord ++ tailWord_4740825).sum := by decide
  have hdescent : baseEnd_4740825 < baseStart_4740825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740844 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_4740844 : Nat := 118140960795 + 4740844 * 2 ^ 59
def prefixEnd_4740844 : Nat := 4983230072969 + 3 ^ 40 * 4740844 * 2
def baseEnd_4740844 : Nat := 2434331679983954659747261

theorem tailTrace_4740844 : CollatzResearch.WordTrace tailWord_4740844 prefixEnd_4740844 2434331679983954659747261 := by
  unfold tailWord_4740844
  simp only [CollatzResearch.WordTrace]
  refine ⟨86456393018369667269526793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115275190691159556359369057 86456393018369667269526793)
  ·
    refine ⟨64842294763777250452145095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86456393018369667269526793 64842294763777250452145095)
    ·
      refine ⟨97263442145665875678217643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64842294763777250452145095 97263442145665875678217643)
      ·
        refine ⟨145895163218498813517326465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97263442145665875678217643 145895163218498813517326465)
        ·
          refine ⟨109421372413874110137994849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145895163218498813517326465 109421372413874110137994849)
          ·
            refine ⟨82066029310405582603496137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109421372413874110137994849 82066029310405582603496137)
            ·
              refine ⟨61549521982804186952622103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82066029310405582603496137 61549521982804186952622103)
              ·
                refine ⟨92324282974206280428933155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61549521982804186952622103 92324282974206280428933155)
                ·
                  refine ⟨138486424461309420643399733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92324282974206280428933155 138486424461309420643399733)
                  ·
                    refine ⟨12983102293247758185318725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 138486424461309420643399733 12983102293247758185318725)
                    ·
                      refine ⟨2434331679983954659747261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12983102293247758185318725 2434331679983954659747261)
                      ·
                        rfl

theorem cell23_4740844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_4740844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740844 prefixEnd_4740844 := by exact prefixLift 4740844
  have htrace : WordTrace (prefixWord ++ tailWord_4740844) baseStart_4740844 baseEnd_4740844 := by
    simpa [prefixWord, tailWord_4740844, baseEnd_4740844] using wordTrace_append hprefix tailTrace_4740844
  have hstable : (prefixWord ++ tailWord_4740844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740844).length < 2 ^ (prefixWord ++ tailWord_4740844).sum := by decide
  have hdescent : baseEnd_4740844 < baseStart_4740844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740852 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4740852 : Nat := 118140960795 + 4740852 * 2 ^ 59
def prefixEnd_4740852 : Nat := 4983230072969 + 3 ^ 40 * 4740852 * 2
def baseEnd_4740852 : Nat := 2434335787829190628447225

theorem tailTrace_4740852 : CollatzResearch.WordTrace tailWord_4740852 prefixEnd_4740852 2434335787829190628447225 := by
  unfold tailWord_4740852
  simp only [CollatzResearch.WordTrace]
  refine ⟨86456538910355175952672405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115275385213806901270229873 86456538910355175952672405)
  ·
    refine ⟨4052650261422898872781519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86456538910355175952672405 4052650261422898872781519)
    ·
      refine ⟨6078975392134348309172279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4052650261422898872781519 6078975392134348309172279)
      ·
        refine ⟨9118463088201522463758419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6078975392134348309172279 9118463088201522463758419)
        ·
          refine ⟨13677694632302283695637629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9118463088201522463758419 13677694632302283695637629)
          ·
            refine ⟨5129135487113356385864111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13677694632302283695637629 5129135487113356385864111)
            ·
              refine ⟨7693703230670034578796167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129135487113356385864111 7693703230670034578796167)
              ·
                refine ⟨11540554846005051868194251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7693703230670034578796167 11540554846005051868194251)
                ·
                  refine ⟨17310832269007577802291377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11540554846005051868194251 17310832269007577802291377)
                  ·
                    refine ⟨12983124201755683351718533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17310832269007577802291377 12983124201755683351718533)
                    ·
                      refine ⟨2434335787829190628447225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12983124201755683351718533 2434335787829190628447225)
                      ·
                        rfl

theorem cell23_4740852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4740852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740852 prefixEnd_4740852 := by exact prefixLift 4740852
  have htrace : WordTrace (prefixWord ++ tailWord_4740852) baseStart_4740852 baseEnd_4740852 := by
    simpa [prefixWord, tailWord_4740852, baseEnd_4740852] using wordTrace_append hprefix tailTrace_4740852
  have hstable : (prefixWord ++ tailWord_4740852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740852).length < 2 ^ (prefixWord ++ tailWord_4740852).sum := by decide
  have hdescent : baseEnd_4740852 < baseStart_4740852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740864 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_4740864 : Nat := 118140960795 + 4740864 * 2 ^ 59
def prefixEnd_4740864 : Nat := 4983230072969 + 3 ^ 40 * 4740864 * 2
def baseEnd_4740864 : Nat := 2434341949597044581497169

theorem tailTrace_4740864 : CollatzResearch.WordTrace tailWord_4740864 prefixEnd_4740864 2434341949597044581497169 := by
  unfold tailWord_4740864
  simp only [CollatzResearch.WordTrace]
  refine ⟨86456757748333438977390823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115275676997777918636521097 86456757748333438977390823)
  ·
    refine ⟨129685136622500158466086235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86456757748333438977390823 129685136622500158466086235)
    ·
      refine ⟨194527704933750237699129353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129685136622500158466086235 194527704933750237699129353)
      ·
        refine ⟨145895778700312678274347015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194527704933750237699129353 145895778700312678274347015)
        ·
          refine ⟨218843668050469017411520523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145895778700312678274347015 218843668050469017411520523)
          ·
            refine ⟨328265502075703526117280785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218843668050469017411520523 328265502075703526117280785)
            ·
              refine ⟨246199126556777644587960589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328265502075703526117280785 246199126556777644587960589)
              ·
                refine ⟨92324672458791616720485221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246199126556777644587960589 92324672458791616720485221)
                ·
                  refine ⟨17310876086023428135090979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92324672458791616720485221 17310876086023428135090979)
                  ·
                    refine ⟨25966314129035142202636469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17310876086023428135090979 25966314129035142202636469)
                    ·
                      refine ⟨2434341949597044581497169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25966314129035142202636469 2434341949597044581497169)
                      ·
                        rfl

theorem cell23_4740864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_4740864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740864 prefixEnd_4740864 := by exact prefixLift 4740864
  have htrace : WordTrace (prefixWord ++ tailWord_4740864) baseStart_4740864 baseEnd_4740864 := by
    simpa [prefixWord, tailWord_4740864, baseEnd_4740864] using wordTrace_append hprefix tailTrace_4740864
  have hstable : (prefixWord ++ tailWord_4740864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740864).length < 2 ^ (prefixWord ++ tailWord_4740864).sum := by decide
  have hdescent : baseEnd_4740864 < baseStart_4740864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740878 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_4740878 : Nat := 118140960795 + 4740878 * 2 ^ 59
def prefixEnd_4740878 : Nat := 4983230072969 + 3 ^ 40 * 4740878 * 2
def baseEnd_4740878 : Nat := 2434349138326207526722105

theorem tailTrace_4740878 : CollatzResearch.WordTrace tailWord_4740878 prefixEnd_4740878 2434349138326207526722105 := by
  unfold tailWord_4740878
  simp only [CollatzResearch.WordTrace]
  refine ⟨21614253264827019793223911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115276017412410772230527525 21614253264827019793223911)
  ·
    refine ⟨32421379897240529689835867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21614253264827019793223911 32421379897240529689835867)
    ·
      refine ⟨48632069845860794534753801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32421379897240529689835867 48632069845860794534753801)
      ·
        refine ⟨36474052384395595901065351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48632069845860794534753801 36474052384395595901065351)
        ·
          refine ⟨54711078576593393851598027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36474052384395595901065351 54711078576593393851598027)
          ·
            refine ⟨82066617864890090777397041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54711078576593393851598027 82066617864890090777397041)
            ·
              refine ⟨61549963398667568083047781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82066617864890090777397041 61549963398667568083047781)
              ·
                refine ⟨11540618137250169015571459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61549963398667568083047781 11540618137250169015571459)
                ·
                  refine ⟨17310927205875253523357189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11540618137250169015571459 17310927205875253523357189)
                  ·
                    refine ⟨3245798851101610035629473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17310927205875253523357189 3245798851101610035629473)
                    ·
                      refine ⟨2434349138326207526722105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245798851101610035629473 2434349138326207526722105)
                      ·
                        rfl

theorem cell23_4740878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_4740878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740878 prefixEnd_4740878 := by exact prefixLift 4740878
  have htrace : WordTrace (prefixWord ++ tailWord_4740878) baseStart_4740878 baseEnd_4740878 := by
    simpa [prefixWord, tailWord_4740878, baseEnd_4740878] using wordTrace_append hprefix tailTrace_4740878
  have hstable : (prefixWord ++ tailWord_4740878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740878).length < 2 ^ (prefixWord ++ tailWord_4740878).sum := by decide
  have hdescent : baseEnd_4740878 < baseStart_4740878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740882 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4740882 : Nat := 118140960795 + 4740882 * 2 ^ 59
def prefixEnd_4740882 : Nat := 4983230072969 + 3 ^ 40 * 4740882 * 2
def baseEnd_4740882 : Nat := 2434351192248825511072087

theorem tailTrace_4740882 : CollatzResearch.WordTrace tailWord_4740882 prefixEnd_4740882 2434351192248825511072087 := by
  unfold tailWord_4740882
  simp only [CollatzResearch.WordTrace]
  refine ⟨43228543002650416757234225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115276114673734444685957933 43228543002650416757234225)
  ·
    refine ⟨32421407251987812567925669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43228543002650416757234225 32421407251987812567925669)
    ·
      refine ⟨6079013859747714856486063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32421407251987812567925669 6079013859747714856486063)
      ·
        refine ⟨9118520789621572284729095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6079013859747714856486063 9118520789621572284729095)
        ·
          refine ⟨13677781184432358427093643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9118520789621572284729095 13677781184432358427093643)
          ·
            refine ⟨20516671776648537640640465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13677781184432358427093643 20516671776648537640640465)
            ·
              refine ⟨15387503832486403230480349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20516671776648537640640465 15387503832486403230480349)
              ·
                refine ⟨5770313937182401211430131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15387503832486403230480349 5770313937182401211430131)
                ·
                  refine ⟨8655470905773601817145197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770313937182401211430131 8655470905773601817145197)
                  ·
                    refine ⟨3245801589665100681429449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8655470905773601817145197 3245801589665100681429449)
                    ·
                      refine ⟨2434351192248825511072087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245801589665100681429449 2434351192248825511072087)
                      ·
                        rfl

theorem cell23_4740882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4740882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740882 prefixEnd_4740882 := by exact prefixLift 4740882
  have htrace : WordTrace (prefixWord ++ tailWord_4740882) baseStart_4740882 baseEnd_4740882 := by
    simpa [prefixWord, tailWord_4740882, baseEnd_4740882] using wordTrace_append hprefix tailTrace_4740882
  have hstable : (prefixWord ++ tailWord_4740882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740882).length < 2 ^ (prefixWord ++ tailWord_4740882).sum := by decide
  have hdescent : baseEnd_4740882 < baseStart_4740882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740895 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 2, 2, 2]
def baseStart_4740895 : Nat := 118140960795 + 4740895 * 2 ^ 59
def prefixEnd_4740895 : Nat := 4983230072969 + 3 ^ 40 * 4740895 * 2
def baseEnd_4740895 : Nat := 2434357867497333960209527

theorem tailTrace_4740895 : CollatzResearch.WordTrace tailWord_4740895 prefixEnd_4740895 2434357867497333960209527 := by
  unfold tailWord_4740895
  simp only [CollatzResearch.WordTrace]
  refine ⟨172914646159554570249160139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115276430773036380166106759 172914646159554570249160139)
  ·
    refine ⟨259371969239331855373740209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172914646159554570249160139 259371969239331855373740209)
    ·
      refine ⟨194528976929498891530305157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259371969239331855373740209 194528976929498891530305157)
      ·
        refine ⟨36474183174281042161932217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194528976929498891530305157 36474183174281042161932217)
        ·
          refine ⟨27355637380710781621449163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36474183174281042161932217 27355637380710781621449163)
          ·
            refine ⟨41033456071066172432173745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27355637380710781621449163 41033456071066172432173745)
            ·
              refine ⟨30775092053299629324130309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41033456071066172432173745 30775092053299629324130309)
              ·
                refine ⟨5770329759993680498274433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30775092053299629324130309 5770329759993680498274433)
                ·
                  refine ⟨4327747319995260373705825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5770329759993680498274433 4327747319995260373705825)
                  ·
                    refine ⟨3245810489996445280279369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4327747319995260373705825 3245810489996445280279369)
                    ·
                      refine ⟨2434357867497333960209527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245810489996445280279369 2434357867497333960209527)
                      ·
                        rfl

theorem cell23_4740895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_4740895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740895 prefixEnd_4740895 := by exact prefixLift 4740895
  have htrace : WordTrace (prefixWord ++ tailWord_4740895) baseStart_4740895 baseEnd_4740895 := by
    simpa [prefixWord, tailWord_4740895, baseEnd_4740895] using wordTrace_append hprefix tailTrace_4740895
  have hstable : (prefixWord ++ tailWord_4740895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740895).length < 2 ^ (prefixWord ++ tailWord_4740895).sum := by decide
  have hdescent : baseEnd_4740895 < baseStart_4740895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740901 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 7]
def baseStart_4740901 : Nat := 118140960795 + 4740901 * 2 ^ 59
def prefixEnd_4740901 : Nat := 4983230072969 + 3 ^ 40 * 4740901 * 2
def baseEnd_4740901 : Nat := 270484549820140104081611

theorem tailTrace_4740901 : CollatzResearch.WordTrace tailWord_4740901 prefixEnd_4740901 270484549820140104081611 := by
  unfold tailWord_4740901
  simp only [CollatzResearch.WordTrace]
  refine ⟨172914864997532833273878557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115276576665021888849252371 172914864997532833273878557)
  ·
    refine ⟨64843074374074812477704459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172914864997532833273878557 64843074374074812477704459)
    ·
      refine ⟨97264611561112218716556689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64843074374074812477704459 97264611561112218716556689)
      ·
        refine ⟨72948458670834164037417517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97264611561112218716556689 72948458670834164037417517)
        ·
          refine ⟨27355672001562811514031569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72948458670834164037417517 27355672001562811514031569)
          ·
            refine ⟨20516754001172108635523677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27355672001562811514031569 20516754001172108635523677)
            ·
              refine ⟨7693782750439540738321379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20516754001172108635523677 7693782750439540738321379)
              ·
                refine ⟨11540674125659311107482069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7693782750439540738321379 11540674125659311107482069)
                ·
                  refine ⟨270484549820140104081611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11540674125659311107482069 270484549820140104081611)
                  ·
                    rfl

theorem cell23_4740901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_4740901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740901 prefixEnd_4740901 := by exact prefixLift 4740901
  have htrace : WordTrace (prefixWord ++ tailWord_4740901) baseStart_4740901 baseEnd_4740901 := by
    simpa [prefixWord, tailWord_4740901, baseEnd_4740901] using wordTrace_append hprefix tailTrace_4740901
  have hstable : (prefixWord ++ tailWord_4740901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740901).length < 2 ^ (prefixWord ++ tailWord_4740901).sum := by decide
  have hdescent : baseEnd_4740901 < baseStart_4740901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740931 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 2, 5]
def baseStart_4740931 : Nat := 118140960795 + 4740931 * 2 ^ 59
def prefixEnd_4740931 : Nat := 4983230072969 + 3 ^ 40 * 4740931 * 2
def baseEnd_4740931 : Nat := 811458784266965273119787

theorem tailTrace_4740931 : CollatzResearch.WordTrace tailWord_4740931 prefixEnd_4740931 811458784266965273119787 := by
  unfold tailWord_4740931
  simp only [CollatzResearch.WordTrace]
  refine ⟨172915959187424148397470647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115277306124949432264980431 172915959187424148397470647)
  ·
    refine ⟨259373938781136222596205971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172915959187424148397470647 259373938781136222596205971)
    ·
      refine ⟨389060908171704333894308957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259373938781136222596205971 389060908171704333894308957)
      ·
        refine ⟨145897840564389125210365859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389060908171704333894308957 145897840564389125210365859)
        ·
          refine ⟨218846760846583687815548789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145897840564389125210365859 218846760846583687815548789)
          ·
            refine ⟨20516883829367220732707699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218846760846583687815548789 20516883829367220732707699)
            ·
              refine ⟨30775325744050831099061549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20516883829367220732707699 30775325744050831099061549)
              ·
                refine ⟨11540747154019061662148081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30775325744050831099061549 11540747154019061662148081)
                ·
                  refine ⟨8655560365514296246611061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11540747154019061662148081 8655560365514296246611061)
                  ·
                    refine ⟨811458784266965273119787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8655560365514296246611061 811458784266965273119787)
                    ·
                      rfl

theorem cell23_4740931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 5].length) (baseStart_4740931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740931 prefixEnd_4740931 := by exact prefixLift 4740931
  have htrace : WordTrace (prefixWord ++ tailWord_4740931) baseStart_4740931 baseEnd_4740931 := by
    simpa [prefixWord, tailWord_4740931, baseEnd_4740931] using wordTrace_append hprefix tailTrace_4740931
  have hstable : (prefixWord ++ tailWord_4740931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740931).length < 2 ^ (prefixWord ++ tailWord_4740931).sum := by decide
  have hdescent : baseEnd_4740931 < baseStart_4740931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740948 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_4740948 : Nat := 118140960795 + 4740948 * 2 ^ 59
def prefixEnd_4740948 : Nat := 4983230072969 + 3 ^ 40 * 4740948 * 2
def baseEnd_4740948 : Nat := 811461693990674084282261

theorem tailTrace_4740948 : CollatzResearch.WordTrace tailWord_4740948 prefixEnd_4740948 811461693990674084282261 := by
  unfold tailWord_4740948
  simp only [CollatzResearch.WordTrace]
  refine ⟨86458289614181280150419749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115277719485575040200559665 86458289614181280150419749)
  ·
    refine ⟨16210929302658990028203703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86458289614181280150419749 16210929302658990028203703)
    ·
      refine ⟨24316393953988485042305555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16210929302658990028203703 24316393953988485042305555)
      ·
        refine ⟨36474590930982727563458333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24316393953988485042305555 36474590930982727563458333)
        ·
          refine ⟨13677971599118522836296875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36474590930982727563458333 13677971599118522836296875)
          ·
            refine ⟨20516957398677784254445313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13677971599118522836296875 20516957398677784254445313)
            ·
              refine ⟨15387718049008338190833985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20516957398677784254445313 15387718049008338190833985)
              ·
                refine ⟨11540788536756253643125489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15387718049008338190833985 11540788536756253643125489)
                ·
                  refine ⟨8655591402567190232344117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11540788536756253643125489 8655591402567190232344117)
                  ·
                    refine ⟨811461693990674084282261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8655591402567190232344117 811461693990674084282261)
                    ·
                      rfl

theorem cell23_4740948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_4740948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740948 prefixEnd_4740948 := by exact prefixLift 4740948
  have htrace : WordTrace (prefixWord ++ tailWord_4740948) baseStart_4740948 baseEnd_4740948 := by
    simpa [prefixWord, tailWord_4740948, baseEnd_4740948] using wordTrace_append hprefix tailTrace_4740948
  have hstable : (prefixWord ++ tailWord_4740948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740948).length < 2 ^ (prefixWord ++ tailWord_4740948).sum := by decide
  have hdescent : baseEnd_4740948 < baseStart_4740948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740971 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 3]
def baseStart_4740971 : Nat := 118140960795 + 4740971 * 2 ^ 59
def prefixEnd_4740971 : Nat := 4983230072969 + 3 ^ 40 * 4740971 * 2
def baseEnd_4740971 : Nat := 2434396892027075662859177

theorem tailTrace_4740971 : CollatzResearch.WordTrace tailWord_4740971 prefixEnd_4740971 2434396892027075662859177 := by
  unfold tailWord_4740971
  simp only [CollatzResearch.WordTrace]
  refine ⟨172917418107279235228926767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115278278738186156819284511 172917418107279235228926767)
  ·
    refine ⟨259376127160918852843390151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172917418107279235228926767 259376127160918852843390151)
    ·
      refine ⟨389064190741378279265085227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259376127160918852843390151 389064190741378279265085227)
      ·
        refine ⟨583596286112067418897627841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389064190741378279265085227 583596286112067418897627841)
        ·
          refine ⟨437697214584050564173220881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583596286112067418897627841 437697214584050564173220881)
          ·
            refine ⟨328272910938037923129915661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437697214584050564173220881 328272910938037923129915661)
            ·
              refine ⟨123102341601764221173718373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328272910938037923129915661 123102341601764221173718373)
              ·
                refine ⟨23081689050330791470072195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123102341601764221173718373 23081689050330791470072195)
                ·
                  refine ⟨34622533575496187205108293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23081689050330791470072195 34622533575496187205108293)
                  ·
                    refine ⟨6491725045405535100957805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34622533575496187205108293 6491725045405535100957805)
                    ·
                      refine ⟨2434396892027075662859177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6491725045405535100957805 2434396892027075662859177)
                      ·
                        rfl

theorem cell23_4740971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 3].length) (baseStart_4740971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740971 prefixEnd_4740971 := by exact prefixLift 4740971
  have htrace : WordTrace (prefixWord ++ tailWord_4740971) baseStart_4740971 baseEnd_4740971 := by
    simpa [prefixWord, tailWord_4740971, baseEnd_4740971] using wordTrace_append hprefix tailTrace_4740971
  have hstable : (prefixWord ++ tailWord_4740971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740971).length < 2 ^ (prefixWord ++ tailWord_4740971).sum := by decide
  have hdescent : baseEnd_4740971 < baseStart_4740971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740982 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_4740982 : Nat := 118140960795 + 4740982 * 2 ^ 59
def prefixEnd_4740982 : Nat := 4983230072969 + 3 ^ 40 * 4740982 * 2
def baseEnd_4740982 : Nat := 811467513438091706607209

theorem tailTrace_4740982 : CollatzResearch.WordTrace tailWord_4740982 prefixEnd_4740982 811467513438091706607209 := by
  unfold tailWord_4740982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807363706889961506723575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115278546206826256071718133 10807363706889961506723575)
  ·
    refine ⟨16211045560334942260085363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10807363706889961506723575 16211045560334942260085363)
    ·
      refine ⟨24316568340502413390128045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16211045560334942260085363 24316568340502413390128045)
      ·
        refine ⟨9118713127688405021298017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24316568340502413390128045 9118713127688405021298017)
        ·
          refine ⟨6839034845766303765973513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9118713127688405021298017 6839034845766303765973513)
          ·
            refine ⟨5129276134324727824480135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6839034845766303765973513 5129276134324727824480135)
            ·
              refine ⟨7693914201487091736720203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129276134324727824480135 7693914201487091736720203)
              ·
                refine ⟨11540871302230637605080305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7693914201487091736720203 11540871302230637605080305)
                ·
                  refine ⟨8655653476672978203810229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11540871302230637605080305 8655653476672978203810229)
                  ·
                    refine ⟨811467513438091706607209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8655653476672978203810229 811467513438091706607209)
                    ·
                      rfl

theorem cell23_4740982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_4740982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740982 prefixEnd_4740982 := by exact prefixLift 4740982
  have htrace : WordTrace (prefixWord ++ tailWord_4740982) baseStart_4740982 baseEnd_4740982 := by
    simpa [prefixWord, tailWord_4740982, baseEnd_4740982] using wordTrace_append hprefix tailTrace_4740982
  have hstable : (prefixWord ++ tailWord_4740982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740982).length < 2 ^ (prefixWord ++ tailWord_4740982).sum := by decide
  have hdescent : baseEnd_4740982 < baseStart_4740982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4740995 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 1, 4]
def baseStart_4740995 : Nat := 118140960795 + 4740995 * 2 ^ 59
def prefixEnd_4740995 : Nat := 4983230072969 + 3 ^ 40 * 4740995 * 2
def baseEnd_4740995 : Nat := 811469738520927856319689

theorem tailTrace_4740995 : CollatzResearch.WordTrace tailWord_4740995 prefixEnd_4740995 811469738520927856319689 := by
  unfold tailWord_4740995
  simp only [CollatzResearch.WordTrace]
  refine ⟨172918293459192287327800439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115278862306128191551866959 172918293459192287327800439)
  ·
    refine ⟨259377440188788430991700659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172918293459192287327800439 259377440188788430991700659)
    ·
      refine ⟨389066160283182646487550989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259377440188788430991700659 389066160283182646487550989)
      ·
        refine ⟨145899810106193492432831621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389066160283182646487550989 145899810106193492432831621)
        ·
          refine ⟨27356214394911279831155929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145899810106193492432831621 27356214394911279831155929)
          ·
            refine ⟨20517160796183459873366947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27356214394911279831155929 20517160796183459873366947)
            ·
              refine ⟨30775741194275189810050421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20517160796183459873366947 30775741194275189810050421)
              ·
                refine ⟨2885225736963299044692227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30775741194275189810050421 2885225736963299044692227)
                ·
                  refine ⟨4327838605444948567038341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885225736963299044692227 4327838605444948567038341)
                  ·
                    refine ⟨811469738520927856319689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327838605444948567038341 811469738520927856319689)
                    ·
                      rfl

theorem cell23_4740995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 4].length) (baseStart_4740995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4740995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4740995 prefixEnd_4740995 := by exact prefixLift 4740995
  have htrace : WordTrace (prefixWord ++ tailWord_4740995) baseStart_4740995 baseEnd_4740995 := by
    simpa [prefixWord, tailWord_4740995, baseEnd_4740995] using wordTrace_append hprefix tailTrace_4740995
  have hstable : (prefixWord ++ tailWord_4740995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4740995).length < 2 ^ (prefixWord ++ tailWord_4740995).sum := by decide
  have hdescent : baseEnd_4740995 < baseStart_4740995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4740995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741012 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_4741012 : Nat := 118140960795 + 4741012 * 2 ^ 59
def prefixEnd_4741012 : Nat := 4983230072969 + 3 ^ 40 * 4741012 * 2
def baseEnd_4741012 : Nat := 811472648244636667482163

theorem tailTrace_4741012 : CollatzResearch.WordTrace tailWord_4741012 prefixEnd_4741012 811472648244636667482163 := by
  unfold tailWord_4741012
  simp only [CollatzResearch.WordTrace]
  refine ⟨86459456750065349615584645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115279275666753799487446193 86459456750065349615584645)
  ·
    refine ⟨16211148140637253052922121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86459456750065349615584645 16211148140637253052922121)
    ·
      refine ⟨12158361105477939789691591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16211148140637253052922121 12158361105477939789691591)
      ·
        refine ⟨18237541658216909684537387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12158361105477939789691591 18237541658216909684537387)
        ·
          refine ⟨27356312487325364526806081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18237541658216909684537387 27356312487325364526806081)
          ·
            refine ⟨20517234365494023395104561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27356312487325364526806081 20517234365494023395104561)
            ·
              refine ⟨15387925774120517546328421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20517234365494023395104561 15387925774120517546328421)
              ·
                refine ⟨2885236082647597039936579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15387925774120517546328421 2885236082647597039936579)
                ·
                  refine ⟨4327854123971395559904869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885236082647597039936579 4327854123971395559904869)
                  ·
                    refine ⟨811472648244636667482163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327854123971395559904869 811472648244636667482163)
                    ·
                      rfl

theorem cell23_4741012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_4741012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741012 prefixEnd_4741012 := by exact prefixLift 4741012
  have htrace : WordTrace (prefixWord ++ tailWord_4741012) baseStart_4741012 baseEnd_4741012 := by
    simpa [prefixWord, tailWord_4741012, baseEnd_4741012] using wordTrace_append hprefix tailTrace_4741012
  have hstable : (prefixWord ++ tailWord_4741012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741012).length < 2 ^ (prefixWord ++ tailWord_4741012).sum := by decide
  have hdescent : baseEnd_4741012 < baseStart_4741012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741045 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_4741045 : Nat := 118140960795 + 4741045 * 2 ^ 59
def prefixEnd_4741045 : Nat := 4983230072969 + 3 ^ 40 * 4741045 * 2
def baseEnd_4741045 : Nat := 2434434889595508373333837

theorem tailTrace_4741045 : CollatzResearch.WordTrace tailWord_4741045 prefixEnd_4741045 2434434889595508373333837 := by
  unfold tailWord_4741045
  simp only [CollatzResearch.WordTrace]
  refine ⟨172920117109011145867120589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115280078072674097244747059 172920117109011145867120589)
  ·
    refine ⟨64845043915879179700170221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172920117109011145867120589 64845043915879179700170221)
    ·
      refine ⟨24316891468454692387563833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64845043915879179700170221 24316891468454692387563833)
      ·
        refine ⟨18237668601341019290672875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24316891468454692387563833 18237668601341019290672875)
        ·
          refine ⟨27356502902011528936009313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18237668601341019290672875 27356502902011528936009313)
          ·
            refine ⟨20517377176508646702006985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27356502902011528936009313 20517377176508646702006985)
            ·
              refine ⟨15388032882381485026505239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20517377176508646702006985 15388032882381485026505239)
              ·
                refine ⟨23082049323572227539757859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15388032882381485026505239 23082049323572227539757859)
                ·
                  refine ⟨34623073985358341309636789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23082049323572227539757859 34623073985358341309636789)
                  ·
                    refine ⟨3245913186127344497778449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34623073985358341309636789 3245913186127344497778449)
                    ·
                      refine ⟨2434434889595508373333837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245913186127344497778449 2434434889595508373333837)
                      ·
                        rfl

theorem cell23_4741045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_4741045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741045 prefixEnd_4741045 := by exact prefixLift 4741045
  have htrace : WordTrace (prefixWord ++ tailWord_4741045) baseStart_4741045 baseEnd_4741045 := by
    simpa [prefixWord, tailWord_4741045, baseEnd_4741045] using wordTrace_append hprefix tailTrace_4741045
  have hstable : (prefixWord ++ tailWord_4741045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741045).length < 2 ^ (prefixWord ++ tailWord_4741045).sum := by decide
  have hdescent : baseEnd_4741045 < baseStart_4741045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741071 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_4741071 : Nat := 118140960795 + 4741071 * 2 ^ 59
def prefixEnd_4741071 : Nat := 4983230072969 + 3 ^ 40 * 4741071 * 2
def baseEnd_4741071 : Nat := 2434448240092525271608717

theorem tailTrace_4741071 : CollatzResearch.WordTrace tailWord_4741071 prefixEnd_4741071 2434448240092525271608717 := by
  unfold tailWord_4741071
  simp only [CollatzResearch.WordTrace]
  refine ⟨172921065406916952307567067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115280710271277968205044711 172921065406916952307567067)
  ·
    refine ⟨259381598110375428461350601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172921065406916952307567067 259381598110375428461350601)
    ·
      refine ⟨194536198582781571346012951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259381598110375428461350601 194536198582781571346012951)
      ·
        refine ⟨291804297874172357019019427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194536198582781571346012951 291804297874172357019019427)
        ·
          refine ⟨437706446811258535528529141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291804297874172357019019427 437706446811258535528529141)
          ·
            refine ⟨41034979388555487705799607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 437706446811258535528529141 41034979388555487705799607)
            ·
              refine ⟨61552469082833231558699411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41034979388555487705799607 61552469082833231558699411)
              ·
                refine ⟨92328703624249847338049117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61552469082833231558699411 92328703624249847338049117)
                ·
                  refine ⟨34623263859093692751768419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92328703624249847338049117 34623263859093692751768419)
                  ·
                    refine ⟨51934895788640539127652629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34623263859093692751768419 51934895788640539127652629)
                    ·
                      refine ⟨2434448240092525271608717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51934895788640539127652629 2434448240092525271608717)
                      ·
                        rfl

theorem cell23_4741071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_4741071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741071 prefixEnd_4741071 := by exact prefixLift 4741071
  have htrace : WordTrace (prefixWord ++ tailWord_4741071) baseStart_4741071 baseEnd_4741071 := by
    simpa [prefixWord, tailWord_4741071, baseEnd_4741071] using wordTrace_append hprefix tailTrace_4741071
  have hstable : (prefixWord ++ tailWord_4741071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741071).length < 2 ^ (prefixWord ++ tailWord_4741071).sum := by decide
  have hdescent : baseEnd_4741071 < baseStart_4741071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741105 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_4741105 : Nat := 118140960795 + 4741105 * 2 ^ 59
def prefixEnd_4741105 : Nat := 4983230072969 + 3 ^ 40 * 4741105 * 2
def baseEnd_4741105 : Nat := 2434465698434778138583561

theorem tailTrace_4741105 : CollatzResearch.WordTrace tailWord_4741105 prefixEnd_4741105 2434465698434778138583561 := by
  unfold tailWord_4741105
  simp only [CollatzResearch.WordTrace]
  refine ⟨172922305488793776114304769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115281536992529184076203179 172922305488793776114304769)
  ·
    refine ⟨129691729116595332085728577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172922305488793776114304769 129691729116595332085728577)
    ·
      refine ⟨97268796837446499064296433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129691729116595332085728577 97268796837446499064296433)
      ·
        refine ⟨72951597628084874298222325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97268796837446499064296433 72951597628084874298222325)
        ·
          refine ⟨6839212277632956965458343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72951597628084874298222325 6839212277632956965458343)
          ·
            refine ⟨10258818416449435448187515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6839212277632956965458343 10258818416449435448187515)
            ·
              refine ⟨15388227624674153172281273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10258818416449435448187515 15388227624674153172281273)
              ·
                refine ⟨11541170718505614879210955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15388227624674153172281273 11541170718505614879210955)
                ·
                  refine ⟨17311756077758422318816433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11541170718505614879210955 17311756077758422318816433)
                  ·
                    refine ⟨12983817058318816739112325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17311756077758422318816433 12983817058318816739112325)
                    ·
                      refine ⟨2434465698434778138583561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12983817058318816739112325 2434465698434778138583561)
                      ·
                        rfl

theorem cell23_4741105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_4741105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741105 prefixEnd_4741105 := by exact prefixLift 4741105
  have htrace : WordTrace (prefixWord ++ tailWord_4741105) baseStart_4741105 baseEnd_4741105 := by
    simpa [prefixWord, tailWord_4741105, baseEnd_4741105] using wordTrace_append hprefix tailTrace_4741105
  have hstable : (prefixWord ++ tailWord_4741105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741105).length < 2 ^ (prefixWord ++ tailWord_4741105).sum := by decide
  have hdescent : baseEnd_4741105 < baseStart_4741105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741111 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 6, 7]
def baseStart_4741111 : Nat := 118140960795 + 4741111 * 2 ^ 59
def prefixEnd_4741111 : Nat := 4983230072969 + 3 ^ 40 * 4741111 * 2
def baseEnd_4741111 : Nat := 811489593106235038369511

theorem tailTrace_4741111 : CollatzResearch.WordTrace tailWord_4741111 prefixEnd_4741111 811489593106235038369511 := by
  unfold tailWord_4741111
  simp only [CollatzResearch.WordTrace]
  refine ⟨172922524326772039139023187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115281682884514692759348791 172922524326772039139023187)
  ·
    refine ⟨259383786490158058708534781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172922524326772039139023187 259383786490158058708534781)
    ·
      refine ⟨97268919933809272015700543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259383786490158058708534781 97268919933809272015700543)
      ·
        refine ⟨145903379900713908023550815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97268919933809272015700543 145903379900713908023550815)
        ·
          refine ⟨218855069851070862035326223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145903379900713908023550815 218855069851070862035326223)
          ·
            refine ⟨328282604776606293052989335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218855069851070862035326223 328282604776606293052989335)
            ·
              refine ⟨492423907164909439579484003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328282604776606293052989335 492423907164909439579484003)
              ·
                refine ⟨738635860747364159369226005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492423907164909439579484003 738635860747364159369226005)
                ·
                  refine ⟨34623555972532694970432469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 738635860747364159369226005 34623555972532694970432469)
                  ·
                    refine ⟨811489593106235038369511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34623555972532694970432469 811489593106235038369511)
                    ·
                      rfl

theorem cell23_4741111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_4741111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741111 prefixEnd_4741111 := by exact prefixLift 4741111
  have htrace : WordTrace (prefixWord ++ tailWord_4741111) baseStart_4741111 baseEnd_4741111 := by
    simpa [prefixWord, tailWord_4741111, baseEnd_4741111] using wordTrace_append hprefix tailTrace_4741111
  have hstable : (prefixWord ++ tailWord_4741111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741111).length < 2 ^ (prefixWord ++ tailWord_4741111).sum := by decide
  have hdescent : baseEnd_4741111 < baseStart_4741111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741169 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 1, 3, 2]
def baseStart_4741169 : Nat := 118140960795 + 4741169 * 2 ^ 59
def prefixEnd_4741169 : Nat := 4983230072969 + 3 ^ 40 * 4741169 * 2
def baseEnd_4741169 : Nat := 2434498561196665888183267

theorem tailTrace_4741169 : CollatzResearch.WordTrace tailWord_4741169 prefixEnd_4741169 2434498561196665888183267 := by
  unfold tailWord_4741169
  simp only [CollatzResearch.WordTrace]
  refine ⟨172924639760561915044634561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115283093173707943363089707 172924639760561915044634561)
  ·
    refine ⟨129693479820421436283475921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172924639760561915044634561 129693479820421436283475921)
    ·
      refine ⟨97270109865316077212606941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129693479820421436283475921 97270109865316077212606941)
      ·
        refine ⟨36476291199493528954727603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97270109865316077212606941 36476291199493528954727603)
        ·
          refine ⟨54714436799240293432091405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36476291199493528954727603 54714436799240293432091405)
          ·
            refine ⟨20517913799715110037034277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54714436799240293432091405 20517913799715110037034277)
            ·
              refine ⟨3847108837446583131943927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20517913799715110037034277 3847108837446583131943927)
              ·
                refine ⟨5770663256169874697915891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847108837446583131943927 5770663256169874697915891)
                ·
                  refine ⟨8655994884254812046873837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770663256169874697915891 8655994884254812046873837)
                  ·
                    refine ⟨3245998081595554517577689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8655994884254812046873837 3245998081595554517577689)
                    ·
                      refine ⟨2434498561196665888183267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3245998081595554517577689 2434498561196665888183267)
                      ·
                        rfl

theorem cell23_4741169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_4741169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741169 prefixEnd_4741169 := by exact prefixLift 4741169
  have htrace : WordTrace (prefixWord ++ tailWord_4741169) baseStart_4741169 baseEnd_4741169 := by
    simpa [prefixWord, tailWord_4741169, baseEnd_4741169] using wordTrace_append hprefix tailTrace_4741169
  have hstable : (prefixWord ++ tailWord_4741169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741169).length < 2 ^ (prefixWord ++ tailWord_4741169).sum := by decide
  have hdescent : baseEnd_4741169 < baseStart_4741169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741176 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 2, 1, 3]
def baseStart_4741176 : Nat := 118140960795 + 4741176 * 2 ^ 59
def prefixEnd_4741176 : Nat := 4983230072969 + 3 ^ 40 * 4741176 * 2
def baseEnd_4741176 : Nat := 2434502155561247360795735

theorem tailTrace_4741176 : CollatzResearch.WordTrace tailWord_4741176 prefixEnd_4741176 2434502155561247360795735 := by
  unfold tailWord_4741176
  simp only [CollatzResearch.WordTrace]
  refine ⟨86462447535768277620069691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115283263381024370160092921 86462447535768277620069691)
  ·
    refine ⟨129693671303652416430104537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86462447535768277620069691 129693671303652416430104537)
    ·
      refine ⟨97270253477739312322578403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129693671303652416430104537 97270253477739312322578403)
      ·
        refine ⟨145905380216608968483867605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97270253477739312322578403 145905380216608968483867605)
        ·
          refine ⟨3419657348826772698840647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 145905380216608968483867605 3419657348826772698840647)
          ·
            refine ⟨5129486023240159048260971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419657348826772698840647 5129486023240159048260971)
            ·
              refine ⟨7694229034860238572391457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129486023240159048260971 7694229034860238572391457)
              ·
                refine ⟨5770671776145178929293593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7694229034860238572391457 5770671776145178929293593)
                ·
                  refine ⟨4328003832108884196970195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5770671776145178929293593 4328003832108884196970195)
                  ·
                    refine ⟨6492005748163326295455293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4328003832108884196970195 6492005748163326295455293)
                    ·
                      refine ⟨2434502155561247360795735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6492005748163326295455293 2434502155561247360795735)
                      ·
                        rfl

theorem cell23_4741176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_4741176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741176 prefixEnd_4741176 := by exact prefixLift 4741176
  have htrace : WordTrace (prefixWord ++ tailWord_4741176) baseStart_4741176 baseEnd_4741176 := by
    simpa [prefixWord, tailWord_4741176, baseEnd_4741176] using wordTrace_append hprefix tailTrace_4741176
  have hstable : (prefixWord ++ tailWord_4741176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741176).length < 2 ^ (prefixWord ++ tailWord_4741176).sum := by decide
  have hdescent : baseEnd_4741176 < baseStart_4741176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741245 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4741245 : Nat := 118140960795 + 4741245 * 2 ^ 59
def prefixEnd_4741245 : Nat := 4983230072969 + 3 ^ 40 * 4741245 * 2
def baseEnd_4741245 : Nat := 2434537585726407590832917

theorem tailTrace_4741245 : CollatzResearch.WordTrace tailWord_4741245 prefixEnd_4741245 2434537585726407590832917 := by
  unfold tailWord_4741245
  simp only [CollatzResearch.WordTrace]
  refine ⟨172927411708286580024401189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115284941138857720016267459 172927411708286580024401189)
  ·
    refine ⟨32423889695303733754575223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172927411708286580024401189 32423889695303733754575223)
    ·
      refine ⟨48635834542955600631862835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32423889695303733754575223 48635834542955600631862835)
      ·
        refine ⟨72953751814433400947794253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48635834542955600631862835 72953751814433400947794253)
        ·
          refine ⟨27357656930412525355422845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72953751814433400947794253 27357656930412525355422845)
          ·
            refine ⟨10259121348904697008283567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27357656930412525355422845 10259121348904697008283567)
            ·
              refine ⟨15388682023357045512425351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10259121348904697008283567 15388682023357045512425351)
              ·
                refine ⟨23083023035035568268638027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15388682023357045512425351 23083023035035568268638027)
                ·
                  refine ⟨34624534552553352402957041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23083023035035568268638027 34624534552553352402957041)
                  ·
                    refine ⟨25968400914415014302217781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34624534552553352402957041 25968400914415014302217781)
                    ·
                      refine ⟨2434537585726407590832917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25968400914415014302217781 2434537585726407590832917)
                      ·
                        rfl

theorem cell23_4741245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4741245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741245 prefixEnd_4741245 := by exact prefixLift 4741245
  have htrace : WordTrace (prefixWord ++ tailWord_4741245) baseStart_4741245 baseEnd_4741245 := by
    simpa [prefixWord, tailWord_4741245, baseEnd_4741245] using wordTrace_append hprefix tailTrace_4741245
  have hstable : (prefixWord ++ tailWord_4741245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741245).length < 2 ^ (prefixWord ++ tailWord_4741245).sum := by decide
  have hdescent : baseEnd_4741245 < baseStart_4741245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 1, 1, 3]
def baseStart_4741339 : Nat := 118140960795 + 4741339 * 2 ^ 59
def prefixEnd_4741339 : Nat := 4983230072969 + 3 ^ 40 * 4741339 * 2
def baseEnd_4741339 : Nat := 2434585852907930223057485

theorem tailTrace_4741339 : CollatzResearch.WordTrace tailWord_4741339 prefixEnd_4741339 2434585852907930223057485 := by
  unfold tailWord_4741339
  simp only [CollatzResearch.WordTrace]
  refine ⟨172930840169946034078323071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115287226779964022718882047 172930840169946034078323071)
  ·
    refine ⟨259396260254919051117484607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172930840169946034078323071 259396260254919051117484607)
    ·
      refine ⟨389094390382378576676226911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259396260254919051117484607 389094390382378576676226911)
      ·
        refine ⟨583641585573567865014340367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389094390382378576676226911 583641585573567865014340367)
        ·
          refine ⟨875462378360351797521510551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583641585573567865014340367 875462378360351797521510551)
          ·
            refine ⟨1313193567540527696282265827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875462378360351797521510551 1313193567540527696282265827)
            ·
              refine ⟨1969790351310791544423398741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313193567540527696282265827 1969790351310791544423398741)
              ·
                refine ⟨2885435084927917301401463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1969790351310791544423398741 2885435084927917301401463)
                ·
                  refine ⟨4328152627391875952102195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885435084927917301401463 4328152627391875952102195)
                  ·
                    refine ⟨6492228941087813928153293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4328152627391875952102195 6492228941087813928153293)
                    ·
                      refine ⟨2434585852907930223057485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6492228941087813928153293 2434585852907930223057485)
                      ·
                        rfl

theorem cell23_4741339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 1, 3].length) (baseStart_4741339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741339 prefixEnd_4741339 := by exact prefixLift 4741339
  have htrace : WordTrace (prefixWord ++ tailWord_4741339) baseStart_4741339 baseEnd_4741339 := by
    simpa [prefixWord, tailWord_4741339, baseEnd_4741339] using wordTrace_append hprefix tailTrace_4741339
  have hstable : (prefixWord ++ tailWord_4741339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741339).length < 2 ^ (prefixWord ++ tailWord_4741339).sum := by decide
  have hdescent : baseEnd_4741339 < baseStart_4741339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741346 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_4741346 : Nat := 118140960795 + 4741346 * 2 ^ 59
def prefixEnd_4741346 : Nat := 4983230072969 + 3 ^ 40 * 4741346 * 2
def baseEnd_4741346 : Nat := 270509938585834632852217

theorem tailTrace_4741346 : CollatzResearch.WordTrace tailWord_4741346 prefixEnd_4741346 270509938585834632852217 := by
  unfold tailWord_4741346
  simp only [CollatzResearch.WordTrace]
  refine ⟨43232773870230168568456973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115287396987280449515885261 43232773870230168568456973)
  ·
    refine ⟨16212290201336313213171365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43232773870230168568456973 16212290201336313213171365)
    ·
      refine ⟨3039804412750558727469631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16212290201336313213171365 3039804412750558727469631)
      ·
        refine ⟨4559706619125838091204447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039804412750558727469631 4559706619125838091204447)
        ·
          refine ⟨6839559928688757136806671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559706619125838091204447 6839559928688757136806671)
          ·
            refine ⟨10259339893033135705210007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6839559928688757136806671 10259339893033135705210007)
            ·
              refine ⟨15389009839549703557815011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10259339893033135705210007 15389009839549703557815011)
              ·
                refine ⟨23083514759324555336722517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15389009839549703557815011 23083514759324555336722517)
                ·
                  refine ⟨270509938585834632852217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23083514759324555336722517 270509938585834632852217)
                  ·
                    rfl

theorem cell23_4741346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_4741346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741346 prefixEnd_4741346 := by exact prefixLift 4741346
  have htrace : WordTrace (prefixWord ++ tailWord_4741346) baseStart_4741346 baseEnd_4741346 := by
    simpa [prefixWord, tailWord_4741346, baseEnd_4741346] using wordTrace_append hprefix tailTrace_4741346
  have hstable : (prefixWord ++ tailWord_4741346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741346).length < 2 ^ (prefixWord ++ tailWord_4741346).sum := by decide
  have hdescent : baseEnd_4741346 < baseStart_4741346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741372 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_4741372 : Nat := 118140960795 + 4741372 * 2 ^ 59
def prefixEnd_4741372 : Nat := 4983230072969 + 3 ^ 40 * 4741372 * 2
def baseEnd_4741372 : Nat := 811534265923176197981611

theorem tailTrace_4741372 : CollatzResearch.WordTrace tailWord_4741372 prefixEnd_4741372 811534265923176197981611 := by
  unfold tailWord_4741372
  simp only [CollatzResearch.WordTrace]
  refine ⟨86466021889413240357137185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115288029185884320476182913 86466021889413240357137185)
  ·
    refine ⟨64849516417059930267852889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86466021889413240357137185 64849516417059930267852889)
    ·
      refine ⟨48637137312794947700889667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64849516417059930267852889 48637137312794947700889667)
      ·
        refine ⟨72955705969192421551334501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48637137312794947700889667 72955705969192421551334501)
        ·
          refine ⟨13679194869223579040875219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72955705969192421551334501 13679194869223579040875219)
          ·
            refine ⟨20518792303835368561312829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13679194869223579040875219 20518792303835368561312829)
            ·
              refine ⟨7694547113938263210492311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20518792303835368561312829 7694547113938263210492311)
              ·
                refine ⟨11541820670907394815738467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7694547113938263210492311 11541820670907394815738467)
                ·
                  refine ⟨17312731006361092223607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11541820670907394815738467 17312731006361092223607701)
                  ·
                    refine ⟨811534265923176197981611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17312731006361092223607701 811534265923176197981611)
                    ·
                      rfl

theorem cell23_4741372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_4741372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741372 prefixEnd_4741372 := by exact prefixLift 4741372
  have htrace : WordTrace (prefixWord ++ tailWord_4741372) baseStart_4741372 baseEnd_4741372 := by
    simpa [prefixWord, tailWord_4741372, baseEnd_4741372] using wordTrace_append hprefix tailTrace_4741372
  have hstable : (prefixWord ++ tailWord_4741372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741372).length < 2 ^ (prefixWord ++ tailWord_4741372).sum := by decide
  have hdescent : baseEnd_4741372 < baseStart_4741372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741375 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_4741375 : Nat := 118140960795 + 4741375 * 2 ^ 59
def prefixEnd_4741375 : Nat := 4983230072969 + 3 ^ 40 * 4741375 * 2
def baseEnd_4741375 : Nat := 2434604338211492082207319

theorem tailTrace_4741375 : CollatzResearch.WordTrace tailWord_4741375 prefixEnd_4741375 2434604338211492082207319 := by
  unfold tailWord_4741375
  simp only [CollatzResearch.WordTrace]
  refine ⟨172932153197815612226633579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115288102131877074817755719 172932153197815612226633579)
  ·
    refine ⟨259398229796723418339950369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172932153197815612226633579 259398229796723418339950369)
    ·
      refine ⟨194548672347542563754962777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259398229796723418339950369 194548672347542563754962777)
      ·
        refine ⟨145911504260656922816222083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194548672347542563754962777 145911504260656922816222083)
        ·
          refine ⟨218867256390985384224333125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145911504260656922816222083 218867256390985384224333125)
          ·
            refine ⟨41037610573309759542062461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218867256390985384224333125 41037610573309759542062461)
            ·
              refine ⟨15389103964991159828273423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41037610573309759542062461 15389103964991159828273423)
              ·
                refine ⟨23083655947486739742410135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15389103964991159828273423 23083655947486739742410135)
                ·
                  refine ⟨34625483921230109613615203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23083655947486739742410135 34625483921230109613615203)
                  ·
                    refine ⟨51938225881845164420422805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34625483921230109613615203 51938225881845164420422805)
                    ·
                      refine ⟨2434604338211492082207319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51938225881845164420422805 2434604338211492082207319)
                      ·
                        rfl

theorem cell23_4741375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_4741375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741375 prefixEnd_4741375 := by exact prefixLift 4741375
  have htrace : WordTrace (prefixWord ++ tailWord_4741375) baseStart_4741375 baseEnd_4741375 := by
    simpa [prefixWord, tailWord_4741375, baseEnd_4741375] using wordTrace_append hprefix tailTrace_4741375
  have hstable : (prefixWord ++ tailWord_4741375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741375).length < 2 ^ (prefixWord ++ tailWord_4741375).sum := by decide
  have hdescent : baseEnd_4741375 < baseStart_4741375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741379 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 3, 2, 2]
def baseStart_4741379 : Nat := 118140960795 + 4741379 * 2 ^ 59
def prefixEnd_4741379 : Nat := 4983230072969 + 3 ^ 40 * 4741379 * 2
def baseEnd_4741379 : Nat := 2434606392134110066557301

theorem tailTrace_4741379 : CollatzResearch.WordTrace tailWord_4741379 prefixEnd_4741379 2434606392134110066557301 := by
  unfold tailWord_4741379
  simp only [CollatzResearch.WordTrace]
  refine ⟨172932299089801120909779191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115288199393200747273186127 172932299089801120909779191)
  ·
    refine ⟨259398448634701681364668787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172932299089801120909779191 259398448634701681364668787)
    ·
      refine ⟨389097672952052522047003181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259398448634701681364668787 389097672952052522047003181)
      ·
        refine ⟨145911627357019695767626193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389097672952052522047003181 145911627357019695767626193)
        ·
          refine ⟨109433720517764771825719645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145911627357019695767626193 109433720517764771825719645)
          ·
            refine ⟨41037645194161789434644867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109433720517764771825719645 41037645194161789434644867)
            ·
              refine ⟨61556467791242684151967301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41037645194161789434644867 61556467791242684151967301)
              ·
                refine ⟨11541837710858003278493869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61556467791242684151967301 11541837710858003278493869)
                ·
                  refine ⟨4328189141571751229435201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11541837710858003278493869 4328189141571751229435201)
                  ·
                    refine ⟨3246141856178813422076401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4328189141571751229435201 3246141856178813422076401)
                    ·
                      refine ⟨2434606392134110066557301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246141856178813422076401 2434606392134110066557301)
                      ·
                        rfl

theorem cell23_4741379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_4741379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741379 prefixEnd_4741379 := by exact prefixLift 4741379
  have htrace : WordTrace (prefixWord ++ tailWord_4741379) baseStart_4741379 baseEnd_4741379 := by
    simpa [prefixWord, tailWord_4741379, baseEnd_4741379] using wordTrace_append hprefix tailTrace_4741379
  have hstable : (prefixWord ++ tailWord_4741379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741379).length < 2 ^ (prefixWord ++ tailWord_4741379).sum := by decide
  have hdescent : baseEnd_4741379 < baseStart_4741379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741385 : List Nat := [1, 2, 1, 1, 3, 5, 1, 9]
def baseStart_4741385 : Nat := 118140960795 + 4741385 * 2 ^ 59
def prefixEnd_4741385 : Nat := 4983230072969 + 3 ^ 40 * 4741385 * 2
def baseEnd_4741385 : Nat := 90170721222890260854899

theorem tailTrace_4741385 : CollatzResearch.WordTrace tailWord_4741385 prefixEnd_4741385 90170721222890260854899 := by
  unfold tailWord_4741385
  simp only [CollatzResearch.WordTrace]
  refine ⟨172932517927779383934497609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115288345285186255956331739 172932517927779383934497609)
  ·
    refine ⟨129699388445834537950873207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172932517927779383934497609 129699388445834537950873207)
    ·
      refine ⟨194549082668751806926309811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129699388445834537950873207 194549082668751806926309811)
      ·
        refine ⟨291823624003127710389464717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194549082668751806926309811 291823624003127710389464717)
        ·
          refine ⟨109433859001172891396049269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291823624003127710389464717 109433859001172891396049269)
          ·
            refine ⟨10259424281359958568379619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109433859001172891396049269 10259424281359958568379619)
            ·
              refine ⟨15389136422039937852569429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10259424281359958568379619 15389136422039937852569429)
              ·
                refine ⟨90170721222890260854899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15389136422039937852569429 90170721222890260854899)
                ·
                  rfl

theorem cell23_4741385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 9].length) (baseStart_4741385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741385 prefixEnd_4741385 := by exact prefixLift 4741385
  have htrace : WordTrace (prefixWord ++ tailWord_4741385) baseStart_4741385 baseEnd_4741385 := by
    simpa [prefixWord, tailWord_4741385, baseEnd_4741385] using wordTrace_append hprefix tailTrace_4741385
  have hstable : (prefixWord ++ tailWord_4741385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741385).length < 2 ^ (prefixWord ++ tailWord_4741385).sum := by decide
  have hdescent : baseEnd_4741385 < baseStart_4741385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741399 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4741399 : Nat := 118140960795 + 4741399 * 2 ^ 59
def prefixEnd_4741399 : Nat := 4983230072969 + 3 ^ 40 * 4741399 * 2
def baseEnd_4741399 : Nat := 2434616661747199988307209

theorem tailTrace_4741399 : CollatzResearch.WordTrace tailWord_4741399 prefixEnd_4741399 2434616661747199988307209 := by
  unfold tailWord_4741399
  simp only [CollatzResearch.WordTrace]
  refine ⟨172933028549728664325507251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115288685699819109550338167 172933028549728664325507251)
  ·
    refine ⟨259399542824592996488260877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172933028549728664325507251 259399542824592996488260877)
    ·
      refine ⟨97274828559222373683097829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259399542824592996488260877 97274828559222373683097829)
      ·
        refine ⟨18239030354854195065580843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97274828559222373683097829 18239030354854195065580843)
        ·
          refine ⟨27358545532281292598371265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18239030354854195065580843 27358545532281292598371265)
          ·
            refine ⟨20518909149210969448778449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27358545532281292598371265 20518909149210969448778449)
            ·
              refine ⟨15389181861908227086583837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20518909149210969448778449 15389181861908227086583837)
              ·
                refine ⟨5770943198215585157468939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15389181861908227086583837 5770943198215585157468939)
                ·
                  refine ⟨8656414797323377736203409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770943198215585157468939 8656414797323377736203409)
                  ·
                    refine ⟨6492311097992533302152557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8656414797323377736203409 6492311097992533302152557)
                    ·
                      refine ⟨2434616661747199988307209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6492311097992533302152557 2434616661747199988307209)
                      ·
                        rfl

theorem cell23_4741399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4741399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741399 prefixEnd_4741399 := by exact prefixLift 4741399
  have htrace : WordTrace (prefixWord ++ tailWord_4741399) baseStart_4741399 baseEnd_4741399 := by
    simpa [prefixWord, tailWord_4741399, baseEnd_4741399] using wordTrace_append hprefix tailTrace_4741399
  have hstable : (prefixWord ++ tailWord_4741399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741399).length < 2 ^ (prefixWord ++ tailWord_4741399).sum := by decide
  have hdescent : baseEnd_4741399 < baseStart_4741399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741402 : List Nat := [3, 1, 1, 3, 4, 2, 9]
def baseStart_4741402 : Nat := 118140960795 + 4741402 * 2 ^ 59
def prefixEnd_4741402 : Nat := 4983230072969 + 3 ^ 40 * 4741402 * 2
def baseEnd_4741402 : Nat := 30057014841841524402095

theorem tailTrace_4741402 : CollatzResearch.WordTrace tailWord_4741402 prefixEnd_4741402 30057014841841524402095 := by
  unfold tailWord_4741402
  simp only [CollatzResearch.WordTrace]
  refine ⟨43233284492179448959466615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115288758645811863891910973 43233284492179448959466615)
  ·
    refine ⟨64849926738269173439199923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43233284492179448959466615 64849926738269173439199923)
    ·
      refine ⟨97274890107403760158799885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64849926738269173439199923 97274890107403760158799885)
      ·
        refine ⟨36478083790276410059549957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97274890107403760158799885 36478083790276410059549957)
        ·
          refine ⟨6839640710676826886165617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36478083790276410059549957 6839640710676826886165617)
          ·
            refine ⟨5129730533007620164624213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6839640710676826886165617 5129730533007620164624213)
            ·
              refine ⟨30057014841841524402095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5129730533007620164624213 30057014841841524402095)
              ·
                rfl

theorem cell23_4741402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 9].length) (baseStart_4741402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741402 prefixEnd_4741402 := by exact prefixLift 4741402
  have htrace : WordTrace (prefixWord ++ tailWord_4741402) baseStart_4741402 baseEnd_4741402 := by
    simpa [prefixWord, tailWord_4741402, baseEnd_4741402] using wordTrace_append hprefix tailTrace_4741402
  have hstable : (prefixWord ++ tailWord_4741402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741402).length < 2 ^ (prefixWord ++ tailWord_4741402).sum := by decide
  have hdescent : baseEnd_4741402 < baseStart_4741402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741406 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4741406 : Nat := 118140960795 + 4741406 * 2 ^ 59
def prefixEnd_4741406 : Nat := 4983230072969 + 3 ^ 40 * 4741406 * 2
def baseEnd_4741406 : Nat := 811540085370593820306559

theorem tailTrace_4741406 : CollatzResearch.WordTrace tailWord_4741406 prefixEnd_4741406 811540085370593820306559 := by
  unfold tailWord_4741406
  simp only [CollatzResearch.WordTrace]
  refine ⟨21616660482587913065126509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115288855907135536347341381 21616660482587913065126509)
  ·
    refine ⟨8106247680970467399422441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21616660482587913065126509 8106247680970467399422441)
    ·
      refine ⟨6079685760727850549566831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8106247680970467399422441 6079685760727850549566831)
      ·
        refine ⟨9119528641091775824350247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6079685760727850549566831 9119528641091775824350247)
        ·
          refine ⟨13679292961637663736525371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9119528641091775824350247 13679292961637663736525371)
          ·
            refine ⟨20518939442456495604788057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13679292961637663736525371 20518939442456495604788057)
            ·
              refine ⟨15389204581842371703591043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20518939442456495604788057 15389204581842371703591043)
              ·
                refine ⟨23083806872763557555386565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15389204581842371703591043 23083806872763557555386565)
                ·
                  refine ⟨4328213788643167041634981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23083806872763557555386565 4328213788643167041634981)
                  ·
                    refine ⟨811540085370593820306559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328213788643167041634981 811540085370593820306559)
                    ·
                      rfl

theorem cell23_4741406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4741406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741406 prefixEnd_4741406 := by exact prefixLift 4741406
  have htrace : WordTrace (prefixWord ++ tailWord_4741406) baseStart_4741406 baseEnd_4741406 := by
    simpa [prefixWord, tailWord_4741406, baseEnd_4741406] using wordTrace_append hprefix tailTrace_4741406
  have hstable : (prefixWord ++ tailWord_4741406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741406).length < 2 ^ (prefixWord ++ tailWord_4741406).sum := by decide
  have hdescent : baseEnd_4741406 < baseStart_4741406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741413 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 3, 2, 2]
def baseStart_4741413 : Nat := 118140960795 + 4741413 * 2 ^ 59
def prefixEnd_4741413 : Nat := 4983230072969 + 3 ^ 40 * 4741413 * 2
def baseEnd_4741413 : Nat := 2434623850476362933532145

theorem tailTrace_4741413 : CollatzResearch.WordTrace tailWord_4741413 prefixEnd_4741413 2434623850476362933532145 := by
  unfold tailWord_4741413
  simp only [CollatzResearch.WordTrace]
  refine ⟨172933539171677944716516893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115289026114451963144344595 172933539171677944716516893)
  ·
    refine ⟨64850077189379229268693835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172933539171677944716516893 64850077189379229268693835)
    ·
      refine ⟨97275115784068843903040753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64850077189379229268693835 97275115784068843903040753)
      ·
        refine ⟨72956336838051632927280565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97275115784068843903040753 72956336838051632927280565)
        ·
          refine ⟨6839656578567340586932553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72956336838051632927280565 6839656578567340586932553)
          ·
            refine ⟨5129742433925505440199415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6839656578567340586932553 5129742433925505440199415)
            ·
              refine ⟨7694613650888258160299123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129742433925505440199415 7694613650888258160299123)
              ·
                refine ⟨11541920476332387240448685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7694613650888258160299123 11541920476332387240448685)
                ·
                  refine ⟨4328220178624645215168257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11541920476332387240448685 4328220178624645215168257)
                  ·
                    refine ⟨3246165133968483911376193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4328220178624645215168257 3246165133968483911376193)
                    ·
                      refine ⟨2434623850476362933532145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246165133968483911376193 2434623850476362933532145)
                      ·
                        rfl

theorem cell23_4741413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_4741413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741413 prefixEnd_4741413 := by exact prefixLift 4741413
  have htrace : WordTrace (prefixWord ++ tailWord_4741413) baseStart_4741413 baseEnd_4741413 := by
    simpa [prefixWord, tailWord_4741413, baseEnd_4741413] using wordTrace_append hprefix tailTrace_4741413
  have hstable : (prefixWord ++ tailWord_4741413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741413).length < 2 ^ (prefixWord ++ tailWord_4741413).sum := by decide
  have hdescent : baseEnd_4741413 < baseStart_4741413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741439 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 3, 3, 2]
def baseStart_4741439 : Nat := 118140960795 + 4741439 * 2 ^ 59
def prefixEnd_4741439 : Nat := 4983230072969 + 3 ^ 40 * 4741439 * 2
def baseEnd_4741439 : Nat := 2434637200973379831807025

theorem tailTrace_4741439 : CollatzResearch.WordTrace tailWord_4741439 prefixEnd_4741439 2434637200973379831807025 := by
  unfold tailWord_4741439
  simp only [CollatzResearch.WordTrace]
  refine ⟨172934487469583751156963371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115289658313055834104642247 172934487469583751156963371)
  ·
    refine ⟨259401731204375626735445057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172934487469583751156963371 259401731204375626735445057)
    ·
      refine ⟨194551298403281720051583793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259401731204375626735445057 194551298403281720051583793)
      ·
        refine ⟨145913473802461290038687845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194551298403281720051583793 145913473802461290038687845)
        ·
          refine ⟨27358776337961491882253971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145913473802461290038687845 27358776337961491882253971)
          ·
            refine ⟨41038164506942237823380957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27358776337961491882253971 41038164506942237823380957)
            ·
              refine ⟨15389311690103339183767859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41038164506942237823380957 15389311690103339183767859)
              ·
                refine ⟨23083967535155008775651789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15389311690103339183767859 23083967535155008775651789)
                ·
                  refine ⟨8656487825683128290869421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23083967535155008775651789 8656487825683128290869421)
                  ·
                    refine ⟨3246182934631173109076033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8656487825683128290869421 3246182934631173109076033)
                    ·
                      refine ⟨2434637200973379831807025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246182934631173109076033 2434637200973379831807025)
                      ·
                        rfl

theorem cell23_4741439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_4741439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741439 prefixEnd_4741439 := by exact prefixLift 4741439
  have htrace : WordTrace (prefixWord ++ tailWord_4741439) baseStart_4741439 baseEnd_4741439 := by
    simpa [prefixWord, tailWord_4741439, baseEnd_4741439] using wordTrace_append hprefix tailTrace_4741439
  have hstable : (prefixWord ++ tailWord_4741439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741439).length < 2 ^ (prefixWord ++ tailWord_4741439).sum := by decide
  have hdescent : baseEnd_4741439 < baseStart_4741439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741445 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_4741445 : Nat := 118140960795 + 4741445 * 2 ^ 59
def prefixEnd_4741445 : Nat := 4983230072969 + 3 ^ 40 * 4741445 * 2
def baseEnd_4741445 : Nat := 811546760619102269443999

theorem tailTrace_4741445 : CollatzResearch.WordTrace tailWord_4741445 prefixEnd_4741445 811546760619102269443999 := by
  unfold tailWord_4741445
  simp only [CollatzResearch.WordTrace]
  refine ⟨172934706307562014181681789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115289804205041342787787859 172934706307562014181681789)
  ·
    refine ⟨64850514865335755318130671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172934706307562014181681789 64850514865335755318130671)
    ·
      refine ⟨97275772298003632977196007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64850514865335755318130671 97275772298003632977196007)
      ·
        refine ⟨145913658447005449465794011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97275772298003632977196007 145913658447005449465794011)
        ·
          refine ⟨218870487670508174198691017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145913658447005449465794011 218870487670508174198691017)
          ·
            refine ⟨164152865752881130649018263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218870487670508174198691017 164152865752881130649018263)
            ·
              refine ⟨246229298629321695973527395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164152865752881130649018263 246229298629321695973527395)
              ·
                refine ⟨369343947943982543960291093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246229298629321695973527395 369343947943982543960291093)
                ·
                  refine ⟨17312997559874181748138645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 369343947943982543960291093 17312997559874181748138645)
                  ·
                    refine ⟨811546760619102269443999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17312997559874181748138645 811546760619102269443999)
                    ·
                      rfl

theorem cell23_4741445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_4741445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741445 prefixEnd_4741445 := by exact prefixLift 4741445
  have htrace : WordTrace (prefixWord ++ tailWord_4741445) baseStart_4741445 baseEnd_4741445 := by
    simpa [prefixWord, tailWord_4741445, baseEnd_4741445] using wordTrace_append hprefix tailTrace_4741445
  have hstable : (prefixWord ++ tailWord_4741445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741445).length < 2 ^ (prefixWord ++ tailWord_4741445).sum := by decide
  have hdescent : baseEnd_4741445 < baseStart_4741445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741455 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_4741455 : Nat := 118140960795 + 4741455 * 2 ^ 59
def prefixEnd_4741455 : Nat := 4983230072969 + 3 ^ 40 * 4741455 * 2
def baseEnd_4741455 : Nat := 2434645416663851769206951

theorem tailTrace_4741455 : CollatzResearch.WordTrace tailWord_4741455 prefixEnd_4741455 2434645416663851769206951 := by
  unfold tailWord_4741455
  simp only [CollatzResearch.WordTrace]
  refine ⟨172935071037525785889545819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115290047358350523926363879 172935071037525785889545819)
  ·
    refine ⟨259402606556288678834318729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172935071037525785889545819 259402606556288678834318729)
    ·
      refine ⟨194551954917216509125739047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259402606556288678834318729 194551954917216509125739047)
      ·
        refine ⟨291827932375824763688608571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194551954917216509125739047 291827932375824763688608571)
        ·
          refine ⟨437741898563737145532912857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291827932375824763688608571 437741898563737145532912857)
          ·
            refine ⟨328306423922802859149684643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437741898563737145532912857 328306423922802859149684643)
            ·
              refine ⟨492459635884204288724526965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328306423922802859149684643 492459635884204288724526965)
              ·
                refine ⟨46168090864144152067924403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 492459635884204288724526965 46168090864144152067924403)
                ·
                  refine ⟨69252136296216228101886605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46168090864144152067924403 69252136296216228101886605)
                  ·
                    refine ⟨25969551111081085538207477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69252136296216228101886605 25969551111081085538207477)
                    ·
                      refine ⟨2434645416663851769206951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25969551111081085538207477 2434645416663851769206951)
                      ·
                        rfl

theorem cell23_4741455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_4741455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741455 prefixEnd_4741455 := by exact prefixLift 4741455
  have htrace : WordTrace (prefixWord ++ tailWord_4741455) baseStart_4741455 baseEnd_4741455 := by
    simpa [prefixWord, tailWord_4741455, baseEnd_4741455] using wordTrace_append hprefix tailTrace_4741455
  have hstable : (prefixWord ++ tailWord_4741455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741455).length < 2 ^ (prefixWord ++ tailWord_4741455).sum := by decide
  have hdescent : baseEnd_4741455 < baseStart_4741455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741465 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_4741465 : Nat := 118140960795 + 4741465 * 2 ^ 59
def prefixEnd_4741465 : Nat := 4983230072969 + 3 ^ 40 * 4741465 * 2
def baseEnd_4741465 : Nat := 2434650551470396730081905

theorem tailTrace_4741465 : CollatzResearch.WordTrace tailWord_4741465 prefixEnd_4741465 2434650551470396730081905 := by
  unfold tailWord_4741465
  simp only [CollatzResearch.WordTrace]
  refine ⟨172935435767489557597409849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115290290511659705064939899 172935435767489557597409849)
  ·
    refine ⟨129701576825617168198057387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172935435767489557597409849 129701576825617168198057387)
    ·
      refine ⟨194552365238425752297086081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129701576825617168198057387 194552365238425752297086081)
      ·
        refine ⟨145914273928819314222814561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194552365238425752297086081 145914273928819314222814561)
        ·
          refine ⟨109435705446614485667110921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145914273928819314222814561 109435705446614485667110921)
          ·
            refine ⟨82076779084960864250333191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109435705446614485667110921 82076779084960864250333191)
            ·
              refine ⟨123115168627441296375499787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82076779084960864250333191 123115168627441296375499787)
              ·
                refine ⟨184672752941161944563249681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123115168627441296375499787 184672752941161944563249681)
                ·
                  refine ⟨138504564705871458422437261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184672752941161944563249681 138504564705871458422437261)
                  ·
                    refine ⟨51939211764701796908413973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138504564705871458422437261 51939211764701796908413973)
                    ·
                      refine ⟨2434650551470396730081905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51939211764701796908413973 2434650551470396730081905)
                      ·
                        rfl

theorem cell23_4741465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_4741465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741465 prefixEnd_4741465 := by exact prefixLift 4741465
  have htrace : WordTrace (prefixWord ++ tailWord_4741465) baseStart_4741465 baseEnd_4741465 := by
    simpa [prefixWord, tailWord_4741465, baseEnd_4741465] using wordTrace_append hprefix tailTrace_4741465
  have hstable : (prefixWord ++ tailWord_4741465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741465).length < 2 ^ (prefixWord ++ tailWord_4741465).sum := by decide
  have hdescent : baseEnd_4741465 < baseStart_4741465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741470 : List Nat := [4, 4, 2, 1, 1, 2, 1, 8]
def baseStart_4741470 : Nat := 118140960795 + 4741470 * 2 ^ 59
def prefixEnd_4741470 : Nat := 4983230072969 + 3 ^ 40 * 4741470 * 2
def baseEnd_4741470 : Nat := 90172337736061822611829

theorem tailTrace_4741470 : CollatzResearch.WordTrace tailWord_4741470 prefixEnd_4741470 90172337736061822611829 := by
  unfold tailWord_4741470
  simp only [CollatzResearch.WordTrace]
  refine ⟨21616952266558930431417733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115290412088314295634227909 21616952266558930431417733)
  ·
    refine ⟨4053178549979799455890825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21616952266558930431417733 4053178549979799455890825)
    ·
      refine ⟨3039883912484849591918119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4053178549979799455890825 3039883912484849591918119)
      ·
        refine ⟨4559825868727274387877179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039883912484849591918119 4559825868727274387877179)
        ·
          refine ⟨6839738803090911581815769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559825868727274387877179 6839738803090911581815769)
          ·
            refine ⟨5129804102318183686361827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6839738803090911581815769 5129804102318183686361827)
            ·
              refine ⟨7694706153477275529542741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129804102318183686361827 7694706153477275529542741)
              ·
                refine ⟨90172337736061822611829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7694706153477275529542741 90172337736061822611829)
                ·
                  rfl

theorem cell23_4741470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_4741470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741470 prefixEnd_4741470 := by exact prefixLift 4741470
  have htrace : WordTrace (prefixWord ++ tailWord_4741470) baseStart_4741470 baseEnd_4741470 := by
    simpa [prefixWord, tailWord_4741470, baseEnd_4741470] using wordTrace_append hprefix tailTrace_4741470
  have hstable : (prefixWord ++ tailWord_4741470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741470).length < 2 ^ (prefixWord ++ tailWord_4741470).sum := by decide
  have hdescent : baseEnd_4741470 < baseStart_4741470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741537 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4741537 : Nat := 118140960795 + 4741537 * 2 ^ 59
def prefixEnd_4741537 : Nat := 4983230072969 + 3 ^ 40 * 4741537 * 2
def baseEnd_4741537 : Nat := 2434687522077520448381575

theorem tailTrace_4741537 : CollatzResearch.WordTrace tailWord_4741537 prefixEnd_4741537 2434687522077520448381575 := by
  unfold tailWord_4741537
  simp only [CollatzResearch.WordTrace]
  refine ⟨172938061823228713894030865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115292041215485809262687243 172938061823228713894030865)
  ·
    refine ⟨129703546367421535420523149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172938061823228713894030865 129703546367421535420523149)
    ·
      refine ⟨48638829887783075782696181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129703546367421535420523149 48638829887783075782696181)
      ·
        refine ⟨4559890301979663354627767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48638829887783075782696181 4559890301979663354627767)
        ·
          refine ⟨6839835452969495031941651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559890301979663354627767 6839835452969495031941651)
          ·
            refine ⟨10259753179454242547912477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6839835452969495031941651 10259753179454242547912477)
            ·
              refine ⟨3847407442295340955467179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10259753179454242547912477 3847407442295340955467179)
              ·
                refine ⟨5771111163443011433200769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847407442295340955467179 5771111163443011433200769)
                ·
                  refine ⟨4328333372582258574900577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5771111163443011433200769 4328333372582258574900577)
                  ·
                    refine ⟨3246250029436693931175433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4328333372582258574900577 3246250029436693931175433)
                    ·
                      refine ⟨2434687522077520448381575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246250029436693931175433 2434687522077520448381575)
                      ·
                        rfl

theorem cell23_4741537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4741537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741537 prefixEnd_4741537 := by exact prefixLift 4741537
  have htrace : WordTrace (prefixWord ++ tailWord_4741537) baseStart_4741537 baseEnd_4741537 := by
    simpa [prefixWord, tailWord_4741537, baseEnd_4741537] using wordTrace_append hprefix tailTrace_4741537
  have hstable : (prefixWord ++ tailWord_4741537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741537).length < 2 ^ (prefixWord ++ tailWord_4741537).sum := by decide
  have hdescent : baseEnd_4741537 < baseStart_4741537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741599 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 6]
def baseStart_4741599 : Nat := 118140960795 + 4741599 * 2 ^ 59
def prefixEnd_4741599 : Nat := 4983230072969 + 3 ^ 40 * 4741599 * 2
def baseEnd_4741599 : Nat := 270524373097566578422921

theorem tailTrace_4741599 : CollatzResearch.WordTrace tailWord_4741599 prefixEnd_4741599 270524373097566578422921 := by
  unfold tailWord_4741599
  simp only [CollatzResearch.WordTrace]
  refine ⟨172940323149004098482787851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115293548766002732321858567 172940323149004098482787851)
  ·
    refine ⟨259410484723506147724181777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172940323149004098482787851 259410484723506147724181777)
    ·
      refine ⟨194557863542629610793136333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259410484723506147724181777 194557863542629610793136333)
      ·
        refine ⟨72959198828486104047426125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194557863542629610793136333 72959198828486104047426125)
        ·
          refine ⟨27359699560682289017784797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72959198828486104047426125 27359699560682289017784797)
          ·
            refine ⟨10259887335255858381669299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27359699560682289017784797 10259887335255858381669299)
            ·
              refine ⟨15389831002883787572503949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10259887335255858381669299 15389831002883787572503949)
              ·
                refine ⟨5771186626081420339688981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15389831002883787572503949 5771186626081420339688981)
                ·
                  refine ⟨270524373097566578422921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5771186626081420339688981 270524373097566578422921)
                  ·
                    rfl

theorem cell23_4741599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 6].length) (baseStart_4741599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741599 prefixEnd_4741599 := by exact prefixLift 4741599
  have htrace : WordTrace (prefixWord ++ tailWord_4741599) baseStart_4741599 baseEnd_4741599 := by
    simpa [prefixWord, tailWord_4741599, baseEnd_4741599] using wordTrace_append hprefix tailTrace_4741599
  have hstable : (prefixWord ++ tailWord_4741599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741599).length < 2 ^ (prefixWord ++ tailWord_4741599).sum := by decide
  have hdescent : baseEnd_4741599 < baseStart_4741599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741613 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4741613 : Nat := 118140960795 + 4741613 * 2 ^ 59
def prefixEnd_4741613 : Nat := 4983230072969 + 3 ^ 40 * 4741613 * 2
def baseEnd_4741613 : Nat := 2434726546607262151031225

theorem tailTrace_4741613 : CollatzResearch.WordTrace tailWord_4741613 prefixEnd_4741613 2434726546607262151031225 := by
  unfold tailWord_4741613
  simp only [CollatzResearch.WordTrace]
  refine ⟨172940833770953378873797493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115293889180635585915864995 172940833770953378873797493)
  ·
    refine ⟨16213203166026879269418515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172940833770953378873797493 16213203166026879269418515)
    ·
      refine ⟨24319804749040318904127773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16213203166026879269418515 24319804749040318904127773)
      ·
        refine ⟨9119926780890119589047915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24319804749040318904127773 9119926780890119589047915)
        ·
          refine ⟨13679890171335179383571873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9119926780890119589047915 13679890171335179383571873)
          ·
            refine ⟨10259917628501384537678905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13679890171335179383571873 10259917628501384537678905)
            ·
              refine ⟨7694938221376038403259179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10259917628501384537678905 7694938221376038403259179)
              ·
                refine ⟨11542407332064057604888769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7694938221376038403259179 11542407332064057604888769)
                ·
                  refine ⟨8656805499048043203666577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11542407332064057604888769 8656805499048043203666577)
                  ·
                    refine ⟨6492604124286032402749933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8656805499048043203666577 6492604124286032402749933)
                    ·
                      refine ⟨2434726546607262151031225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6492604124286032402749933 2434726546607262151031225)
                      ·
                        rfl

theorem cell23_4741613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4741613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741613 prefixEnd_4741613 := by exact prefixLift 4741613
  have htrace : WordTrace (prefixWord ++ tailWord_4741613) baseStart_4741613 baseEnd_4741613 := by
    simpa [prefixWord, tailWord_4741613, baseEnd_4741613] using wordTrace_append hprefix tailTrace_4741613
  have hstable : (prefixWord ++ tailWord_4741613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741613).length < 2 ^ (prefixWord ++ tailWord_4741613).sum := by decide
  have hdescent : baseEnd_4741613 < baseStart_4741613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741666 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_4741666 : Nat := 118140960795 + 4741666 * 2 ^ 59
def prefixEnd_4741666 : Nat := 4983230072969 + 3 ^ 40 * 4741666 * 2
def baseEnd_4741666 : Nat := 2434753761081950443668481

theorem tailTrace_4741666 : CollatzResearch.WordTrace tailWord_4741666 prefixEnd_4741666 2434753761081950443668481 := by
  unfold tailWord_4741666
  simp only [CollatzResearch.WordTrace]
  refine ⟨43235691709940342231369213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115295177893174245950317901 43235691709940342231369213)
  ·
    refine ⟨16213384391227628336763455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43235691709940342231369213 16213384391227628336763455)
    ·
      refine ⟨24320076586841442505145183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16213384391227628336763455 24320076586841442505145183)
      ·
        refine ⟨36480114880262163757717775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24320076586841442505145183 36480114880262163757717775)
        ·
          refine ⟨54720172320393245636576663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36480114880262163757717775 54720172320393245636576663)
          ·
            refine ⟨82080258480589868454864995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54720172320393245636576663 82080258480589868454864995)
            ·
              refine ⟨123120387720884802682297493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82080258480589868454864995 123120387720884802682297493)
              ·
                refine ⟨5771268174416475125732695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123120387720884802682297493 5771268174416475125732695)
                ·
                  refine ⟨8656902261624712688599043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5771268174416475125732695 8656902261624712688599043)
                  ·
                    refine ⟨12985353392437069032898565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8656902261624712688599043 12985353392437069032898565)
                    ·
                      refine ⟨2434753761081950443668481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12985353392437069032898565 2434753761081950443668481)
                      ·
                        rfl

theorem cell23_4741666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_4741666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741666 prefixEnd_4741666 := by exact prefixLift 4741666
  have htrace : WordTrace (prefixWord ++ tailWord_4741666) baseStart_4741666 baseEnd_4741666 := by
    simpa [prefixWord, tailWord_4741666, baseEnd_4741666] using wordTrace_append hprefix tailTrace_4741666
  have hstable : (prefixWord ++ tailWord_4741666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741666).length < 2 ^ (prefixWord ++ tailWord_4741666).sum := by decide
  have hdescent : baseEnd_4741666 < baseStart_4741666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741693 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_4741693 : Nat := 118140960795 + 4741693 * 2 ^ 59
def prefixEnd_4741693 : Nat := 4983230072969 + 3 ^ 40 * 4741693 * 2
def baseEnd_4741693 : Nat := 811589208353207279343619

theorem tailTrace_4741693 : CollatzResearch.WordTrace tailWord_4741693 prefixEnd_4741693 811589208353207279343619 := by
  unfold tailWord_4741693
  simp only [CollatzResearch.WordTrace]
  refine ⟨172943751610663552536709733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115295834407109035024473155 172943751610663552536709733)
  ·
    refine ⟨32426953426999416100633075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172943751610663552536709733 32426953426999416100633075)
    ·
      refine ⟨48640430140499124150949613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32426953426999416100633075 48640430140499124150949613)
      ·
        refine ⟨18240161302687171556606105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48640430140499124150949613 18240161302687171556606105)
        ·
          refine ⟨13680120977015378667454579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18240161302687171556606105 13680120977015378667454579)
          ·
            refine ⟨20520181465523068001181869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13680120977015378667454579 20520181465523068001181869)
            ·
              refine ⟨7695068049571150500443201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20520181465523068001181869 7695068049571150500443201)
              ·
                refine ⟨5771301037178362875332401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7695068049571150500443201 5771301037178362875332401)
                ·
                  refine ⟨4328475777883772156499301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5771301037178362875332401 4328475777883772156499301)
                  ·
                    refine ⟨811589208353207279343619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328475777883772156499301 811589208353207279343619)
                    ·
                      rfl

theorem cell23_4741693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_4741693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741693 prefixEnd_4741693 := by exact prefixLift 4741693
  have htrace : WordTrace (prefixWord ++ tailWord_4741693) baseStart_4741693 baseEnd_4741693 := by
    simpa [prefixWord, tailWord_4741693, baseEnd_4741693] using wordTrace_append hprefix tailTrace_4741693
  have hstable : (prefixWord ++ tailWord_4741693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741693).length < 2 ^ (prefixWord ++ tailWord_4741693).sum := by decide
  have hdescent : baseEnd_4741693 < baseStart_4741693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741699 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 3]
def baseStart_4741699 : Nat := 118140960795 + 4741699 * 2 ^ 59
def prefixEnd_4741699 : Nat := 4983230072969 + 3 ^ 40 * 4741699 * 2
def baseEnd_4741699 : Nat := 2434770705943548814555829

theorem tailTrace_4741699 : CollatzResearch.WordTrace tailWord_4741699 prefixEnd_4741699 2434770705943548814555829 := by
  unfold tailWord_4741699
  simp only [CollatzResearch.WordTrace]
  refine ⟨172943970448641815561428151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115295980299094543707618767 172943970448641815561428151)
  ·
    refine ⟨259415955672962723342142227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172943970448641815561428151 259415955672962723342142227)
    ·
      refine ⟨389123933509444085013213341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259415955672962723342142227 389123933509444085013213341)
      ·
        refine ⟨145921475066041531879955003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389123933509444085013213341 145921475066041531879955003)
        ·
          refine ⟨218882212599062297819932505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145921475066041531879955003 218882212599062297819932505)
          ·
            refine ⟨164161659449296723364949379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218882212599062297819932505 164161659449296723364949379)
            ·
              refine ⟨246242489173945085047424069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164161659449296723364949379 246242489173945085047424069)
              ·
                refine ⟨46170466720114703446392013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246242489173945085047424069 46170466720114703446392013)
                ·
                  refine ⟨17313925020043013792397005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46170466720114703446392013 17313925020043013792397005)
                  ·
                    refine ⟨6492721882516130172148877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17313925020043013792397005 6492721882516130172148877)
                    ·
                      refine ⟨2434770705943548814555829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6492721882516130172148877 2434770705943548814555829)
                      ·
                        rfl

theorem cell23_4741699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_4741699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741699 prefixEnd_4741699 := by exact prefixLift 4741699
  have htrace : WordTrace (prefixWord ++ tailWord_4741699) baseStart_4741699 baseEnd_4741699 := by
    simpa [prefixWord, tailWord_4741699, baseEnd_4741699] using wordTrace_append hprefix tailTrace_4741699
  have hstable : (prefixWord ++ tailWord_4741699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741699).length < 2 ^ (prefixWord ++ tailWord_4741699).sum := by decide
  have hdescent : baseEnd_4741699 < baseStart_4741699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741729 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_4741729 : Nat := 118140960795 + 4741729 * 2 ^ 59
def prefixEnd_4741729 : Nat := 4983230072969 + 3 ^ 40 * 4741729 * 2
def baseEnd_4741729 : Nat := 2434786110363183697180691

theorem tailTrace_4741729 : CollatzResearch.WordTrace tailWord_4741729 prefixEnd_4741729 2434786110363183697180691 := by
  unfold tailWord_4741729
  simp only [CollatzResearch.WordTrace]
  refine ⟨172945064638533130685020241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115296709759022087123346827 172945064638533130685020241)
  ·
    refine ⟨129708798478899848013765181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172945064638533130685020241 129708798478899848013765181)
    ·
      refine ⟨48640799429587443005161943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129708798478899848013765181 48640799429587443005161943)
      ·
        refine ⟨72961199144381164507742915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48640799429587443005161943 72961199144381164507742915)
        ·
          refine ⟨109441798716571746761614373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72961199144381164507742915 109441798716571746761614373)
          ·
            refine ⟨20520337259357202517802695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109441798716571746761614373 20520337259357202517802695)
            ·
              refine ⟨30780505889035803776704043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20520337259357202517802695 30780505889035803776704043)
              ·
                refine ⟨46170758833553705665056065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30780505889035803776704043 46170758833553705665056065)
                ·
                  refine ⟨34628069125165279248792049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46170758833553705665056065 34628069125165279248792049)
                  ·
                    refine ⟨25971051843873959436594037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34628069125165279248792049 25971051843873959436594037)
                    ·
                      refine ⟨2434786110363183697180691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25971051843873959436594037 2434786110363183697180691)
                      ·
                        rfl

theorem cell23_4741729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_4741729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741729 prefixEnd_4741729 := by exact prefixLift 4741729
  have htrace : WordTrace (prefixWord ++ tailWord_4741729) baseStart_4741729 baseEnd_4741729 := by
    simpa [prefixWord, tailWord_4741729, baseEnd_4741729] using wordTrace_append hprefix tailTrace_4741729
  have hstable : (prefixWord ++ tailWord_4741729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741729).length < 2 ^ (prefixWord ++ tailWord_4741729).sum := by decide
  have hdescent : baseEnd_4741729 < baseStart_4741729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741743 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 1, 3, 2]
def baseStart_4741743 : Nat := 118140960795 + 4741743 * 2 ^ 59
def prefixEnd_4741743 : Nat := 4983230072969 + 3 ^ 40 * 4741743 * 2
def baseEnd_4741743 : Nat := 2434793299092346642405627

theorem tailTrace_4741743 : CollatzResearch.WordTrace tailWord_4741743 prefixEnd_4741743 2434793299092346642405627 := by
  unfold tailWord_4741743
  simp only [CollatzResearch.WordTrace]
  refine ⟨172945575260482411076029883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115297050173654940717353255 172945575260482411076029883)
  ·
    refine ⟨259418362890723616614044825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172945575260482411076029883 259418362890723616614044825)
    ·
      refine ⟨194563772168042712460533619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259418362890723616614044825 194563772168042712460533619)
      ·
        refine ⟨291845658252064068690800429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194563772168042712460533619 291845658252064068690800429)
        ·
          refine ⟨109442121844524025759050161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291845658252064068690800429 109442121844524025759050161)
          ·
            refine ⟨82081591383393019319287621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109442121844524025759050161 82081591383393019319287621)
            ·
              refine ⟨15390298384386191122366429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82081591383393019319287621 15390298384386191122366429)
              ·
                refine ⟨5771361894144821670887411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15390298384386191122366429 5771361894144821670887411)
                ·
                  refine ⟨8657042841217232506331117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5771361894144821670887411 8657042841217232506331117)
                  ·
                    refine ⟨3246391065456462189874169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8657042841217232506331117 3246391065456462189874169)
                    ·
                      refine ⟨2434793299092346642405627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246391065456462189874169 2434793299092346642405627)
                      ·
                        rfl

theorem cell23_4741743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 3, 2].length) (baseStart_4741743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741743 prefixEnd_4741743 := by exact prefixLift 4741743
  have htrace : WordTrace (prefixWord ++ tailWord_4741743) baseStart_4741743 baseEnd_4741743 := by
    simpa [prefixWord, tailWord_4741743, baseEnd_4741743] using wordTrace_append hprefix tailTrace_4741743
  have hstable : (prefixWord ++ tailWord_4741743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741743).length < 2 ^ (prefixWord ++ tailWord_4741743).sum := by decide
  have hdescent : baseEnd_4741743 < baseStart_4741743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741769 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_4741769 : Nat := 118140960795 + 4741769 * 2 ^ 59
def prefixEnd_4741769 : Nat := 4983230072969 + 3 ^ 40 * 4741769 * 2
def baseEnd_4741769 : Nat := 2434806649589363540680507

theorem tailTrace_4741769 : CollatzResearch.WordTrace tailWord_4741769 prefixEnd_4741769 2434806649589363540680507 := by
  unfold tailWord_4741769
  simp only [CollatzResearch.WordTrace]
  refine ⟨172946523558388217516476361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115297682372258811677650907 172946523558388217516476361)
  ·
    refine ⟨129709892668791163137357271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172946523558388217516476361 129709892668791163137357271)
    ·
      refine ⟨194564839003186744706035907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129709892668791163137357271 194564839003186744706035907)
      ·
        refine ⟨291847258504780117059053861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194564839003186744706035907 291847258504780117059053861)
        ·
          refine ⟨54721360969646271948572599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291847258504780117059053861 54721360969646271948572599)
          ·
            refine ⟨82082041454469407922858899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54721360969646271948572599 82082041454469407922858899)
            ·
              refine ⟨123123062181704111884288349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82082041454469407922858899 123123062181704111884288349)
              ·
                refine ⟨46171148318139041956608131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123123062181704111884288349 46171148318139041956608131)
                ·
                  refine ⟨69256722477208562934912197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46171148318139041956608131 69256722477208562934912197)
                  ·
                    refine ⟨12985635464476605550296037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69256722477208562934912197 12985635464476605550296037)
                    ·
                      refine ⟨2434806649589363540680507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12985635464476605550296037 2434806649589363540680507)
                      ·
                        rfl

theorem cell23_4741769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_4741769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741769 prefixEnd_4741769 := by exact prefixLift 4741769
  have htrace : WordTrace (prefixWord ++ tailWord_4741769) baseStart_4741769 baseEnd_4741769 := by
    simpa [prefixWord, tailWord_4741769, baseEnd_4741769] using wordTrace_append hprefix tailTrace_4741769
  have hstable : (prefixWord ++ tailWord_4741769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741769).length < 2 ^ (prefixWord ++ tailWord_4741769).sum := by decide
  have hdescent : baseEnd_4741769 < baseStart_4741769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741790 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4741790 : Nat := 118140960795 + 4741790 * 2 ^ 59
def prefixEnd_4741790 : Nat := 4983230072969 + 3 ^ 40 * 4741790 * 2
def baseEnd_4741790 : Nat := 2434817432683107958517911

theorem tailTrace_4741790 : CollatzResearch.WordTrace tailWord_4741790 prefixEnd_4741790 2434817432683107958517911 := by
  unfold tailWord_4741790
  simp only [CollatzResearch.WordTrace]
  refine ⟨21618411186414017262873853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115298192994208092068660549 21618411186414017262873853)
  ·
    refine ⟨8106904194905256473577695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21618411186414017262873853 8106904194905256473577695)
    ·
      refine ⟨12160356292357884710366543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8106904194905256473577695 12160356292357884710366543)
      ·
        refine ⟨18240534438536827065549815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12160356292357884710366543 18240534438536827065549815)
        ·
          refine ⟨27360801657805240598324723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18240534438536827065549815 27360801657805240598324723)
          ·
            refine ⟨41041202486707860897487085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27360801657805240598324723 41041202486707860897487085)
            ·
              refine ⟨15390450932515447836557657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41041202486707860897487085 15390450932515447836557657)
              ·
                refine ⟨11542838199386585877418243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15390450932515447836557657 11542838199386585877418243)
                ·
                  refine ⟨17314257299079878816127365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11542838199386585877418243 17314257299079878816127365)
                  ·
                    refine ⟨3246423243577477278023881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17314257299079878816127365 3246423243577477278023881)
                    ·
                      refine ⟨2434817432683107958517911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246423243577477278023881 2434817432683107958517911)
                      ·
                        rfl

theorem cell23_4741790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4741790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741790 prefixEnd_4741790 := by exact prefixLift 4741790
  have htrace : WordTrace (prefixWord ++ tailWord_4741790) baseStart_4741790 baseEnd_4741790 := by
    simpa [prefixWord, tailWord_4741790, baseEnd_4741790] using wordTrace_append hprefix tailTrace_4741790
  have hstable : (prefixWord ++ tailWord_4741790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741790).length < 2 ^ (prefixWord ++ tailWord_4741790).sum := by decide
  have hdescent : baseEnd_4741790 < baseStart_4741790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741856 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 7, 4]
def baseStart_4741856 : Nat := 118140960795 + 4741856 * 2 ^ 59
def prefixEnd_4741856 : Nat := 4983230072969 + 3 ^ 40 * 4741856 * 2
def baseEnd_4741856 : Nat := 811617107468768233430869

theorem tailTrace_4741856 : CollatzResearch.WordTrace tailWord_4741856 prefixEnd_4741856 811617107468768233430869 := by
  unfold tailWord_4741856
  simp only [CollatzResearch.WordTrace]
  refine ⟨86474848354536515687446711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115299797806048687583262281 86474848354536515687446711)
  ·
    refine ⟨129712272531804773531170067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86474848354536515687446711 129712272531804773531170067)
    ·
      refine ⟨194568408797707160296755101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129712272531804773531170067 194568408797707160296755101)
      ·
        refine ⟨72963153299140185111283163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194568408797707160296755101 72963153299140185111283163)
        ·
          refine ⟨109444729948710277666924745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72963153299140185111283163 109444729948710277666924745)
          ·
            refine ⟨82083547461532708250193559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109444729948710277666924745 82083547461532708250193559)
            ·
              refine ⟨123125321192299062375290339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82083547461532708250193559 123125321192299062375290339)
              ·
                refine ⟨184687981788448593562935509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123125321192299062375290339 184687981788448593562935509)
                ·
                  refine ⟨4328624573166763911631301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184687981788448593562935509 4328624573166763911631301)
                  ·
                    refine ⟨811617107468768233430869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328624573166763911631301 811617107468768233430869)
                    ·
                      rfl

theorem cell23_4741856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_4741856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741856 prefixEnd_4741856 := by exact prefixLift 4741856
  have htrace : WordTrace (prefixWord ++ tailWord_4741856) baseStart_4741856 baseEnd_4741856 := by
    simpa [prefixWord, tailWord_4741856, baseEnd_4741856] using wordTrace_append hprefix tailTrace_4741856
  have hstable : (prefixWord ++ tailWord_4741856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741856).length < 2 ^ (prefixWord ++ tailWord_4741856).sum := by decide
  have hdescent : baseEnd_4741856 < baseStart_4741856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741873 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 3, 4]
def baseStart_4741873 : Nat := 118140960795 + 4741873 * 2 ^ 59
def prefixEnd_4741873 : Nat := 4983230072969 + 3 ^ 40 * 4741873 * 2
def baseEnd_4741873 : Nat := 811620017192477044593343

theorem tailTrace_4741873 : CollatzResearch.WordTrace tailWord_4741873 prefixEnd_4741873 811620017192477044593343 := by
  unfold tailWord_4741873
  simp only [CollatzResearch.WordTrace]
  refine ⟨172950316750011443278262273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115300211166674295518841515 172950316750011443278262273)
  ·
    refine ⟨129712737562508582458696705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172950316750011443278262273 129712737562508582458696705)
    ·
      refine ⟨97284553171881436844022529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129712737562508582458696705 97284553171881436844022529)
      ·
        refine ⟨72963414878911077633016897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97284553171881436844022529 72963414878911077633016897)
        ·
          refine ⟨54722561159183308224762673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72963414878911077633016897 54722561159183308224762673)
          ·
            refine ⟨41041920869387481168572005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54722561159183308224762673 41041920869387481168572005)
            ·
              refine ⟨7695360163010152719107251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41041920869387481168572005 7695360163010152719107251)
              ·
                refine ⟨11543040244515229078660877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7695360163010152719107251 11543040244515229078660877)
                ·
                  refine ⟨4328640091693210904497829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11543040244515229078660877 4328640091693210904497829)
                  ·
                    refine ⟨811620017192477044593343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328640091693210904497829 811620017192477044593343)
                    ·
                      rfl

theorem cell23_4741873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_4741873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741873 prefixEnd_4741873 := by exact prefixLift 4741873
  have htrace : WordTrace (prefixWord ++ tailWord_4741873) baseStart_4741873 baseEnd_4741873 := by
    simpa [prefixWord, tailWord_4741873, baseEnd_4741873] using wordTrace_append hprefix tailTrace_4741873
  have hstable : (prefixWord ++ tailWord_4741873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741873).length < 2 ^ (prefixWord ++ tailWord_4741873).sum := by decide
  have hdescent : baseEnd_4741873 < baseStart_4741873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741890 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_4741890 : Nat := 118140960795 + 4741890 * 2 ^ 59
def prefixEnd_4741890 : Nat := 4983230072969 + 3 ^ 40 * 4741890 * 2
def baseEnd_4741890 : Nat := 811622926916185855755817

theorem tailTrace_4741890 : CollatzResearch.WordTrace tailWord_4741890 prefixEnd_4741890 811622926916185855755817 := by
  unfold tailWord_4741890
  simp only [CollatzResearch.WordTrace]
  refine ⟨43237734197737463795407781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115300624527299903454420749 43237734197737463795407781)
  ·
    refine ⟨8107075162075774461638959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43237734197737463795407781 8107075162075774461638959)
    ·
      refine ⟨12160612743113661692458439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8107075162075774461638959 12160612743113661692458439)
      ·
        refine ⟨18240919114670492538687659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12160612743113661692458439 18240919114670492538687659)
        ·
          refine ⟨27361378672005738808031489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18240919114670492538687659 27361378672005738808031489)
          ·
            refine ⟨20521034004004304106023617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27361378672005738808031489 20521034004004304106023617)
            ·
              refine ⟨15390775503003228079517713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20521034004004304106023617 15390775503003228079517713)
              ·
                refine ⟨11543081627252421059638285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15390775503003228079517713 11543081627252421059638285)
                ·
                  refine ⟨4328655610219657897364357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11543081627252421059638285 4328655610219657897364357)
                  ·
                    refine ⟨811622926916185855755817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328655610219657897364357 811622926916185855755817)
                    ·
                      rfl

theorem cell23_4741890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_4741890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741890 prefixEnd_4741890 := by exact prefixLift 4741890
  have htrace : WordTrace (prefixWord ++ tailWord_4741890) baseStart_4741890 baseEnd_4741890 := by
    simpa [prefixWord, tailWord_4741890, baseEnd_4741890] using wordTrace_append hprefix tailTrace_4741890
  have hstable : (prefixWord ++ tailWord_4741890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741890).length < 2 ^ (prefixWord ++ tailWord_4741890).sum := by decide
  have hdescent : baseEnd_4741890 < baseStart_4741890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741917 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4741917 : Nat := 118140960795 + 4741917 * 2 ^ 59
def prefixEnd_4741917 : Nat := 4983230072969 + 3 ^ 40 * 4741917 * 2
def baseEnd_4741917 : Nat := 2434882644726228961629827

theorem tailTrace_4741917 : CollatzResearch.WordTrace tailWord_4741917 prefixEnd_4741917 2434882644726228961629827 := by
  unfold tailWord_4741917
  simp only [CollatzResearch.WordTrace]
  refine ⟨172951921561852038792864005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115301281041234692528576003 172951921561852038792864005)
  ·
    refine ⟨32428485292847257273662001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172951921561852038792864005 32428485292847257273662001)
    ·
      refine ⟨24321363969635442955246501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32428485292847257273662001 24321363969635442955246501)
      ·
        refine ⟨4560255744306645554108719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24321363969635442955246501 4560255744306645554108719)
        ·
          refine ⟨6840383616459968331163079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560255744306645554108719 6840383616459968331163079)
          ·
            refine ⟨10260575424689952496744619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840383616459968331163079 10260575424689952496744619)
            ·
              refine ⟨15390863137034928745116929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10260575424689952496744619 15390863137034928745116929)
              ·
                refine ⟨11543147352776196558837697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15390863137034928745116929 11543147352776196558837697)
                ·
                  refine ⟨8657360514582147419128273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11543147352776196558837697 8657360514582147419128273)
                  ·
                    refine ⟨6493020385936610564346205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8657360514582147419128273 6493020385936610564346205)
                    ·
                      refine ⟨2434882644726228961629827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493020385936610564346205 2434882644726228961629827)
                      ·
                        rfl

theorem cell23_4741917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4741917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741917 prefixEnd_4741917 := by exact prefixLift 4741917
  have htrace : WordTrace (prefixWord ++ tailWord_4741917) baseStart_4741917 baseEnd_4741917 := by
    simpa [prefixWord, tailWord_4741917, baseEnd_4741917] using wordTrace_append hprefix tailTrace_4741917
  have hstable : (prefixWord ++ tailWord_4741917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741917).length < 2 ^ (prefixWord ++ tailWord_4741917).sum := by decide
  have hdescent : baseEnd_4741917 < baseStart_4741917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741924 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_4741924 : Nat := 118140960795 + 4741924 * 2 ^ 59
def prefixEnd_4741924 : Nat := 4983230072969 + 3 ^ 40 * 4741924 * 2
def baseEnd_4741924 : Nat := 811628746363603478080765

theorem tailTrace_4741924 : CollatzResearch.WordTrace tailWord_4741924 prefixEnd_4741924 811628746363603478080765 := by
  unfold tailWord_4741924
  simp only [CollatzResearch.WordTrace]
  refine ⟨86476088436413339494184413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115301451248551119325579217 86476088436413339494184413)
  ·
    refine ⟨32428533163655002310319155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86476088436413339494184413 32428533163655002310319155)
    ·
      refine ⟨48642799745482503465478733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32428533163655002310319155 48642799745482503465478733)
      ·
        refine ⟨18241049904555938799554525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48642799745482503465478733 18241049904555938799554525)
        ·
          refine ⟨6840393714208477049832947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18241049904555938799554525 6840393714208477049832947)
          ·
            refine ⟨10260590571312715574749421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840393714208477049832947 10260590571312715574749421)
            ·
              refine ⟨3847721464242268340531033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10260590571312715574749421 3847721464242268340531033)
              ·
                refine ⟨2885791098181701255398275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847721464242268340531033 2885791098181701255398275)
                ·
                  refine ⟨4328686647272551883097413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885791098181701255398275 4328686647272551883097413)
                  ·
                    refine ⟨811628746363603478080765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328686647272551883097413 811628746363603478080765)
                    ·
                      rfl

theorem cell23_4741924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_4741924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741924 prefixEnd_4741924 := by exact prefixLift 4741924
  have htrace : WordTrace (prefixWord ++ tailWord_4741924) baseStart_4741924 baseEnd_4741924 := by
    simpa [prefixWord, tailWord_4741924, baseEnd_4741924] using wordTrace_append hprefix tailTrace_4741924
  have hstable : (prefixWord ++ tailWord_4741924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741924).length < 2 ^ (prefixWord ++ tailWord_4741924).sum := by decide
  have hdescent : baseEnd_4741924 < baseStart_4741924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4741950 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4741950 : Nat := 118140960795 + 4741950 * 2 ^ 59
def prefixEnd_4741950 : Nat := 4983230072969 + 3 ^ 40 * 4741950 * 2
def baseEnd_4741950 : Nat := 811633196529275777505725

theorem tailTrace_4741950 : CollatzResearch.WordTrace tailWord_4741950 prefixEnd_4741950 811633196529275777505725 := by
  unfold tailWord_4741950
  simp only [CollatzResearch.WordTrace]
  refine ⟨21619140646341560678601913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115302083447154990285876869 21619140646341560678601913)
  ·
    refine ⟨16214355484756170508951435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21619140646341560678601913 16214355484756170508951435)
    ·
      refine ⟨24321533227134255763427153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214355484756170508951435 24321533227134255763427153)
      ·
        refine ⟨18241149920350691822570365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24321533227134255763427153 18241149920350691822570365)
        ·
          refine ⟨6840431220131509433463887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18241149920350691822570365 6840431220131509433463887)
          ·
            refine ⟨10260646830197264150195831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840431220131509433463887 10260646830197264150195831)
            ·
              refine ⟨15390970245295896225293747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10260646830197264150195831 15390970245295896225293747)
              ·
                refine ⟨23086455367943844337940621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15390970245295896225293747 23086455367943844337940621)
                ·
                  refine ⟨8657420762978941626727733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23086455367943844337940621 8657420762978941626727733)
                  ·
                    refine ⟨811633196529275777505725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8657420762978941626727733 811633196529275777505725)
                    ·
                      rfl

theorem cell23_4741950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4741950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4741950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4741950 prefixEnd_4741950 := by exact prefixLift 4741950
  have htrace : WordTrace (prefixWord ++ tailWord_4741950) baseStart_4741950 baseEnd_4741950 := by
    simpa [prefixWord, tailWord_4741950, baseEnd_4741950] using wordTrace_append hprefix tailTrace_4741950
  have hstable : (prefixWord ++ tailWord_4741950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4741950).length < 2 ^ (prefixWord ++ tailWord_4741950).sum := by decide
  have hdescent : baseEnd_4741950 < baseStart_4741950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4741950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742003 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 3]
def baseStart_4742003 : Nat := 118140960795 + 4742003 * 2 ^ 59
def prefixEnd_4742003 : Nat := 4983230072969 + 3 ^ 40 * 4742003 * 2
def baseEnd_4742003 : Nat := 2434926804062515625154431

theorem tailTrace_4742003 : CollatzResearch.WordTrace tailWord_4742003 prefixEnd_4742003 2434926804062515625154431 := by
  unfold tailWord_4742003
  simp only [CollatzResearch.WordTrace]
  refine ⟨172955058239540475480494663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115303372159693650320329775 172955058239540475480494663)
  ·
    refine ⟨259432587359310713220741995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172955058239540475480494663 259432587359310713220741995)
    ·
      refine ⟨389148881038966069831112993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259432587359310713220741995 389148881038966069831112993)
      ·
        refine ⟨291861660779224552373334745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389148881038966069831112993 291861660779224552373334745)
        ·
          refine ⟨218896245584418414280001059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291861660779224552373334745 218896245584418414280001059)
          ·
            refine ⟨328344368376627621420001589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218896245584418414280001059 328344368376627621420001589)
            ·
              refine ⟨30782284535308839508125149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 328344368376627621420001589 30782284535308839508125149)
              ·
                refine ⟨11543356700740814815546931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30782284535308839508125149 11543356700740814815546931)
                ·
                  refine ⟨17315035051111222223320397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11543356700740814815546931 17315035051111222223320397)
                  ·
                    refine ⟨6493138144166708333745149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17315035051111222223320397 6493138144166708333745149)
                    ·
                      refine ⟨2434926804062515625154431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493138144166708333745149 2434926804062515625154431)
                      ·
                        rfl

theorem cell23_4742003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_4742003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742003 prefixEnd_4742003 := by exact prefixLift 4742003
  have htrace : WordTrace (prefixWord ++ tailWord_4742003) baseStart_4742003 baseEnd_4742003 := by
    simpa [prefixWord, tailWord_4742003, baseEnd_4742003] using wordTrace_append hprefix tailTrace_4742003
  have hstable : (prefixWord ++ tailWord_4742003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742003).length < 2 ^ (prefixWord ++ tailWord_4742003).sum := by decide
  have hdescent : baseEnd_4742003 < baseStart_4742003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742018 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4742018 : Nat := 118140960795 + 4742018 * 2 ^ 59
def prefixEnd_4742018 : Nat := 4983230072969 + 3 ^ 40 * 4742018 * 2
def baseEnd_4742018 : Nat := 811644835424111022155621

theorem tailTrace_4742018 : CollatzResearch.WordTrace tailWord_4742018 prefixEnd_4742018 811644835424111022155621 := by
  unfold tailWord_4742018
  simp only [CollatzResearch.WordTrace]
  refine ⟨43238901333621533260572677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115303736889657422028193805 43238901333621533260572677)
  ·
    refine ⟨8107294000054037486357377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43238901333621533260572677 8107294000054037486357377)
    ·
      refine ⟨6080470500040528114768033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8107294000054037486357377 6080470500040528114768033)
      ·
        refine ⟨4560352875030396086076025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6080470500040528114768033 4560352875030396086076025)
        ·
          refine ⟨3420264656272797064557019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4560352875030396086076025 3420264656272797064557019)
          ·
            refine ⟨5130396984409195596835529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420264656272797064557019 5130396984409195596835529)
            ·
              refine ⟨3847797738306896697626647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5130396984409195596835529 3847797738306896697626647)
              ·
                refine ⟨5771696607460345046439971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847797738306896697626647 5771696607460345046439971)
                ·
                  refine ⟨8657544911190517569659957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5771696607460345046439971 8657544911190517569659957)
                  ·
                    refine ⟨811644835424111022155621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8657544911190517569659957 811644835424111022155621)
                    ·
                      rfl

theorem cell23_4742018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4742018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742018 prefixEnd_4742018 := by exact prefixLift 4742018
  have htrace : WordTrace (prefixWord ++ tailWord_4742018) baseStart_4742018 baseEnd_4742018 := by
    simpa [prefixWord, tailWord_4742018, baseEnd_4742018] using wordTrace_append hprefix tailTrace_4742018
  have hstable : (prefixWord ++ tailWord_4742018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742018).length < 2 ^ (prefixWord ++ tailWord_4742018).sum := by decide
  have hdescent : baseEnd_4742018 < baseStart_4742018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742020 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_4742020 : Nat := 118140960795 + 4742020 * 2 ^ 59
def prefixEnd_4742020 : Nat := 4983230072969 + 3 ^ 40 * 4742020 * 2
def baseEnd_4742020 : Nat := 2434935533233642058641853

theorem tailTrace_4742020 : CollatzResearch.WordTrace tailWord_4742020 prefixEnd_4742020 2434935533233642058641853 := by
  unfold tailWord_4742020
  simp only [CollatzResearch.WordTrace]
  refine ⟨86477839140239443691931757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115303785520319258255909009 86477839140239443691931757)
  ·
    refine ⟨32429189677589791384474409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86477839140239443691931757 32429189677589791384474409)
    ·
      refine ⟨24321892258192343538355807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32429189677589791384474409 24321892258192343538355807)
      ·
        refine ⟨36482838387288515307533711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24321892258192343538355807 36482838387288515307533711)
        ·
          refine ⟨54724257580932772961300567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36482838387288515307533711 54724257580932772961300567)
          ·
            refine ⟨82086386371399159441950851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54724257580932772961300567 82086386371399159441950851)
            ·
              refine ⟨123129579557098739162926277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82086386371399159441950851 123129579557098739162926277)
              ·
                refine ⟨23086796166956013593048677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123129579557098739162926277 23086796166956013593048677)
                ·
                  refine ⟨4328774281304252548696627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23086796166956013593048677 4328774281304252548696627)
                  ·
                    refine ⟨6493161421956378823044941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4328774281304252548696627 6493161421956378823044941)
                    ·
                      refine ⟨2434935533233642058641853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493161421956378823044941 2434935533233642058641853)
                      ·
                        rfl

theorem cell23_4742020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_4742020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742020 prefixEnd_4742020 := by exact prefixLift 4742020
  have htrace : WordTrace (prefixWord ++ tailWord_4742020) baseStart_4742020 baseEnd_4742020 := by
    simpa [prefixWord, tailWord_4742020, baseEnd_4742020] using wordTrace_append hprefix tailTrace_4742020
  have hstable : (prefixWord ++ tailWord_4742020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742020).length < 2 ^ (prefixWord ++ tailWord_4742020).sum := by decide
  have hdescent : baseEnd_4742020 < baseStart_4742020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742024 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4742024 : Nat := 118140960795 + 4742024 * 2 ^ 59
def prefixEnd_4742024 : Nat := 4983230072969 + 3 ^ 40 * 4742024 * 2
def baseEnd_4742024 : Nat := 2434937587156260042991835

theorem tailTrace_4742024 : CollatzResearch.WordTrace tailWord_4742024 prefixEnd_4742024 2434937587156260042991835 := by
  unfold tailWord_4742024
  simp only [CollatzResearch.WordTrace]
  refine ⟨86477912086232198033504563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115303882781642930711339417 86477912086232198033504563)
  ·
    refine ⟨129716868129348297050256845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86477912086232198033504563 129716868129348297050256845)
    ·
      refine ⟨48643825548505611393846317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129716868129348297050256845 48643825548505611393846317)
      ·
        refine ⟨18241434580689604272692369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48643825548505611393846317 18241434580689604272692369)
        ·
          refine ⟨13681075935517203204519277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18241434580689604272692369 13681075935517203204519277)
          ·
            refine ⟨5130403475818951201694729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13681075935517203204519277 5130403475818951201694729)
            ·
              refine ⟨3847802606864213401271047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5130403475818951201694729 3847802606864213401271047)
              ·
                refine ⟨5771703910296320101906571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847802606864213401271047 5771703910296320101906571)
                ·
                  refine ⟨8657555865444480152859857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5771703910296320101906571 8657555865444480152859857)
                  ·
                    refine ⟨6493166899083360114644893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8657555865444480152859857 6493166899083360114644893)
                    ·
                      refine ⟨2434937587156260042991835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493166899083360114644893 2434937587156260042991835)
                      ·
                        rfl

theorem cell23_4742024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4742024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742024 prefixEnd_4742024 := by exact prefixLift 4742024
  have htrace : WordTrace (prefixWord ++ tailWord_4742024) baseStart_4742024 baseEnd_4742024 := by
    simpa [prefixWord, tailWord_4742024, baseEnd_4742024] using wordTrace_append hprefix tailTrace_4742024
  have hstable : (prefixWord ++ tailWord_4742024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742024).length < 2 ^ (prefixWord ++ tailWord_4742024).sum := by decide
  have hdescent : baseEnd_4742024 < baseStart_4742024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742037 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_4742037 : Nat := 118140960795 + 4742037 * 2 ^ 59
def prefixEnd_4742037 : Nat := 4983230072969 + 3 ^ 40 * 4742037 * 2
def baseEnd_4742037 : Nat := 2434944262404768492129275

theorem tailTrace_4742037 : CollatzResearch.WordTrace tailWord_4742037 prefixEnd_4742037 2434944262404768492129275 := by
  unfold tailWord_4742037
  simp only [CollatzResearch.WordTrace]
  refine ⟨172956298321417299287232365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115304198880944866191488243 172956298321417299287232365)
  ·
    refine ⟨64858611870531487232712137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172956298321417299287232365 64858611870531487232712137)
    ·
      refine ⟨48643958902898615424534103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64858611870531487232712137 48643958902898615424534103)
      ·
        refine ⟨72965938354347923136801155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48643958902898615424534103 72965938354347923136801155)
        ·
          refine ⟨109448907531521884705201733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72965938354347923136801155 109448907531521884705201733)
          ·
            refine ⟨20521670162160353382225325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109448907531521884705201733 20521670162160353382225325)
            ·
              refine ⟨7695626310810132518334497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20521670162160353382225325 7695626310810132518334497)
              ·
                refine ⟨5771719733107599388750873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7695626310810132518334497 5771719733107599388750873)
                ·
                  refine ⟨4328789799830699541563155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5771719733107599388750873 4328789799830699541563155)
                  ·
                    refine ⟨6493184699746049312344733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4328789799830699541563155 6493184699746049312344733)
                    ·
                      refine ⟨2434944262404768492129275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493184699746049312344733 2434944262404768492129275)
                      ·
                        rfl

theorem cell23_4742037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_4742037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742037 prefixEnd_4742037 := by exact prefixLift 4742037
  have htrace : WordTrace (prefixWord ++ tailWord_4742037) baseStart_4742037 baseEnd_4742037 := by
    simpa [prefixWord, tailWord_4742037, baseEnd_4742037] using wordTrace_append hprefix tailTrace_4742037
  have hstable : (prefixWord ++ tailWord_4742037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742037).length < 2 ^ (prefixWord ++ tailWord_4742037).sum := by decide
  have hdescent : baseEnd_4742037 < baseStart_4742037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742038 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4742038 : Nat := 118140960795 + 4742038 * 2 ^ 59
def prefixEnd_4742038 : Nat := 4983230072969 + 3 ^ 40 * 4742038 * 2
def baseEnd_4742038 : Nat := 2434944775885422988216771

theorem tailTrace_4742038 : CollatzResearch.WordTrace tailWord_4742038 prefixEnd_4742038 2434944775885422988216771 := by
  unfold tailWord_4742038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809770924650854778626173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115304223196275784305345845 10809770924650854778626173)
  ·
    refine ⟨4053664096744070541984815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10809770924650854778626173 4053664096744070541984815)
    ·
      refine ⟨6080496145116105812977223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4053664096744070541984815 6080496145116105812977223)
      ·
        refine ⟨9120744217674158719465835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6080496145116105812977223 9120744217674158719465835)
        ·
          refine ⟨13681116326511238079198753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9120744217674158719465835 13681116326511238079198753)
          ·
            refine ⟨10260837244883428559399065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13681116326511238079198753 10260837244883428559399065)
            ·
              refine ⟨7695627933662571419549299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10260837244883428559399065 7695627933662571419549299)
              ·
                refine ⟨11543441900493857129323949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7695627933662571419549299 11543441900493857129323949)
                ·
                  refine ⟨4328790712685196423496481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11543441900493857129323949 4328790712685196423496481)
                  ·
                    refine ⟨3246593034513897317622361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4328790712685196423496481 3246593034513897317622361)
                    ·
                      refine ⟨2434944775885422988216771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246593034513897317622361 2434944775885422988216771)
                      ·
                        rfl

theorem cell23_4742038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4742038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742038 prefixEnd_4742038 := by exact prefixLift 4742038
  have htrace : WordTrace (prefixWord ++ tailWord_4742038) baseStart_4742038 baseEnd_4742038 := by
    simpa [prefixWord, tailWord_4742038, baseEnd_4742038] using wordTrace_append hprefix tailTrace_4742038
  have hstable : (prefixWord ++ tailWord_4742038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742038).length < 2 ^ (prefixWord ++ tailWord_4742038).sum := by decide
  have hdescent : baseEnd_4742038 < baseStart_4742038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742100 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 7]
def baseStart_4742100 : Nat := 118140960795 + 4742100 * 2 ^ 59
def prefixEnd_4742100 : Nat := 4983230072969 + 3 ^ 40 * 4742100 * 2
def baseEnd_4742100 : Nat := 270552956854000193960165

theorem tailTrace_4742100 : CollatzResearch.WordTrace tailWord_4742100 prefixEnd_4742100 270552956854000193960165 := by
  unfold tailWord_4742100
  simp only [CollatzResearch.WordTrace]
  refine ⟨86479298060094530523387877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115305730746792707364517169 86479298060094530523387877)
  ·
    refine ⟨16214868386267724473135227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86479298060094530523387877 16214868386267724473135227)
    ·
      refine ⟨24322302579401586709702841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214868386267724473135227 24322302579401586709702841)
      ·
        refine ⟨18241726934551190032277131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24322302579401586709702841 18241726934551190032277131)
        ·
          refine ⟨27362590401826785048415697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18241726934551190032277131 27362590401826785048415697)
          ·
            refine ⟨20521942801370088786311773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27362590401826785048415697 20521942801370088786311773)
            ·
              refine ⟨7695728550513783294866915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20521942801370088786311773 7695728550513783294866915)
              ·
                refine ⟨11543592825770674942300373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7695728550513783294866915 11543592825770674942300373)
                ·
                  refine ⟨270552956854000193960165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11543592825770674942300373 270552956854000193960165)
                  ·
                    rfl

theorem cell23_4742100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_4742100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742100 prefixEnd_4742100 := by exact prefixLift 4742100
  have htrace : WordTrace (prefixWord ++ tailWord_4742100) baseStart_4742100 baseEnd_4742100 := by
    simpa [prefixWord, tailWord_4742100, baseEnd_4742100] using wordTrace_append hprefix tailTrace_4742100
  have hstable : (prefixWord ++ tailWord_4742100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742100).length < 2 ^ (prefixWord ++ tailWord_4742100).sum := by decide
  have hdescent : baseEnd_4742100 < baseStart_4742100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742113 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_4742113 : Nat := 118140960795 + 4742113 * 2 ^ 59
def prefixEnd_4742113 : Nat := 4983230072969 + 3 ^ 40 * 4742113 * 2
def baseEnd_4742113 : Nat := 811661095644836731592975

theorem tailTrace_4742113 : CollatzResearch.WordTrace tailWord_4742113 prefixEnd_4742113 811661095644836731592975 := by
  unfold tailWord_4742113
  simp only [CollatzResearch.WordTrace]
  refine ⟨172959070269141964266998993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115306046846094642844665995 172959070269141964266998993)
  ·
    refine ⟨129719302701856473200249245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172959070269141964266998993 129719302701856473200249245)
    ·
      refine ⟨48644738513196177450093467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129719302701856473200249245 48644738513196177450093467)
      ·
        refine ⟨72967107769794266175140201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48644738513196177450093467 72967107769794266175140201)
        ·
          refine ⟨54725330827345699631355151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72967107769794266175140201 54725330827345699631355151)
          ·
            refine ⟨82087996241018549447032727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54725330827345699631355151 82087996241018549447032727)
            ·
              refine ⟨123131994361527824170549091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82087996241018549447032727 123131994361527824170549091)
              ·
                refine ⟨184697991542291736255823637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123131994361527824170549091 184697991542291736255823637)
                ·
                  refine ⟨8657718353544925136991733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184697991542291736255823637 8657718353544925136991733)
                  ·
                    refine ⟨811661095644836731592975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8657718353544925136991733 811661095644836731592975)
                    ·
                      rfl

theorem cell23_4742113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_4742113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742113 prefixEnd_4742113 := by exact prefixLift 4742113
  have htrace : WordTrace (prefixWord ++ tailWord_4742113) baseStart_4742113 baseEnd_4742113 := by
    simpa [prefixWord, tailWord_4742113, baseEnd_4742113] using wordTrace_append hprefix tailTrace_4742113
  have hstable : (prefixWord ++ tailWord_4742113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742113).length < 2 ^ (prefixWord ++ tailWord_4742113).sum := by decide
  have hdescent : baseEnd_4742113 < baseStart_4742113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742132 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4742132 : Nat := 118140960795 + 4742132 * 2 ^ 59
def prefixEnd_4742132 : Nat := 4983230072969 + 3 ^ 40 * 4742132 * 2
def baseEnd_4742132 : Nat := 2434993043066945620441339

theorem tailTrace_4742132 : CollatzResearch.WordTrace tailWord_4742132 prefixEnd_4742132 2434993043066945620441339 := by
  unfold tailWord_4742132
  simp only [CollatzResearch.WordTrace]
  refine ⟨86479881628036565255970325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115306508837382087007960433 86479881628036565255970325)
  ·
    refine ⟨4053744451314213996373609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86479881628036565255970325 4053744451314213996373609)
    ·
      refine ⟨3040308338485660497280207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4053744451314213996373609 3040308338485660497280207)
      ·
        refine ⟨4560462507728490745920311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040308338485660497280207 4560462507728490745920311)
        ·
          refine ⟨6840693761592736118880467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560462507728490745920311 6840693761592736118880467)
          ·
            refine ⟨10261040642389104178320701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840693761592736118880467 10261040642389104178320701)
            ·
              refine ⟨3847890240895914066870263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10261040642389104178320701 3847890240895914066870263)
              ·
                refine ⟨5771835361343871100305395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847890240895914066870263 5771835361343871100305395)
                ·
                  refine ⟨8657753042015806650458093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5771835361343871100305395 8657753042015806650458093)
                  ·
                    refine ⟨3246657390755927493921785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8657753042015806650458093 3246657390755927493921785)
                    ·
                      refine ⟨2434993043066945620441339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246657390755927493921785 2434993043066945620441339)
                      ·
                        rfl

theorem cell23_4742132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4742132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742132 prefixEnd_4742132 := by exact prefixLift 4742132
  have htrace : WordTrace (prefixWord ++ tailWord_4742132) baseStart_4742132 baseEnd_4742132 := by
    simpa [prefixWord, tailWord_4742132, baseEnd_4742132] using wordTrace_append hprefix tailTrace_4742132
  have hstable : (prefixWord ++ tailWord_4742132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742132).length < 2 ^ (prefixWord ++ tailWord_4742132).sum := by decide
  have hdescent : baseEnd_4742132 < baseStart_4742132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742163 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4]
def baseStart_4742163 : Nat := 118140960795 + 4742163 * 2 ^ 59
def prefixEnd_4742163 : Nat := 4983230072969 + 3 ^ 40 * 4742163 * 2
def baseEnd_4742163 : Nat := 2435008960967234999153695

theorem tailTrace_4742163 : CollatzResearch.WordTrace tailWord_4742163 prefixEnd_4742163 2435008960967234999153695 := by
  unfold tailWord_4742163
  simp only [CollatzResearch.WordTrace]
  refine ⟨172960893918960822806319143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115307262612640548537546095 172960893918960822806319143)
  ·
    refine ⟨259441340878441234209478715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172960893918960822806319143 259441340878441234209478715)
    ·
      refine ⟨389162011317661851314218073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259441340878441234209478715 389162011317661851314218073)
      ·
        refine ⟨291871508488246388485663555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389162011317661851314218073 291871508488246388485663555)
        ·
          refine ⟨437807262732369582728495333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291871508488246388485663555 437807262732369582728495333)
          ·
            refine ⟨82088861762319296761592875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 437807262732369582728495333 82088861762319296761592875)
            ·
              refine ⟨123133292643478945142389313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82088861762319296761592875 123133292643478945142389313)
              ·
                refine ⟨92349969482609208856791985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123133292643478945142389313 92349969482609208856791985)
                ·
                  refine ⟨69262477111956906642593989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92349969482609208856791985 69262477111956906642593989)
                  ·
                    refine ⟨12986714458491919995486373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69262477111956906642593989 12986714458491919995486373)
                    ·
                      refine ⟨2435008960967234999153695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12986714458491919995486373 2435008960967234999153695)
                      ·
                        rfl

theorem cell23_4742163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_4742163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742163 prefixEnd_4742163 := by exact prefixLift 4742163
  have htrace : WordTrace (prefixWord ++ tailWord_4742163) baseStart_4742163 baseEnd_4742163 := by
    simpa [prefixWord, tailWord_4742163, baseEnd_4742163] using wordTrace_append hprefix tailTrace_4742163
  have hstable : (prefixWord ++ tailWord_4742163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742163).length < 2 ^ (prefixWord ++ tailWord_4742163).sum := by decide
  have hdescent : baseEnd_4742163 < baseStart_4742163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742167 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4742167 : Nat := 118140960795 + 4742167 * 2 ^ 59
def prefixEnd_4742167 : Nat := 4983230072969 + 3 ^ 40 * 4742167 * 2
def baseEnd_4742167 : Nat := 2435011014889852983503677

theorem tailTrace_4742167 : CollatzResearch.WordTrace tailWord_4742167 prefixEnd_4742167 2435011014889852983503677 := by
  unfold tailWord_4742167
  simp only [CollatzResearch.WordTrace]
  refine ⟨172961039810946331489464755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115307359873964220992976503 172961039810946331489464755)
  ·
    refine ⟨259441559716419497234197133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172961039810946331489464755 259441559716419497234197133)
    ·
      refine ⟨97290584893657311462823925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259441559716419497234197133 97290584893657311462823925)
      ·
        refine ⟨9120992333780372949639743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97290584893657311462823925 9120992333780372949639743)
        ·
          refine ⟨13681488500670559424459615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9120992333780372949639743 13681488500670559424459615)
          ·
            refine ⟨20522232751005839136689423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13681488500670559424459615 20522232751005839136689423)
            ·
              refine ⟨30783349126508758705034135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20522232751005839136689423 30783349126508758705034135)
              ·
                refine ⟨46175023689763138057551203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30783349126508758705034135 46175023689763138057551203)
                ·
                  refine ⟨69262535534644707086326805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46175023689763138057551203 69262535534644707086326805)
                  ·
                    refine ⟨3246681353186470644671569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69262535534644707086326805 3246681353186470644671569)
                    ·
                      refine ⟨2435011014889852983503677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246681353186470644671569 2435011014889852983503677)
                      ·
                        rfl

theorem cell23_4742167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4742167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742167 prefixEnd_4742167 := by exact prefixLift 4742167
  have htrace : WordTrace (prefixWord ++ tailWord_4742167) baseStart_4742167 baseEnd_4742167 := by
    simpa [prefixWord, tailWord_4742167, baseEnd_4742167] using wordTrace_append hprefix tailTrace_4742167
  have hstable : (prefixWord ++ tailWord_4742167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742167).length < 2 ^ (prefixWord ++ tailWord_4742167).sum := by decide
  have hdescent : baseEnd_4742167 < baseStart_4742167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742170 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_4742170 : Nat := 118140960795 + 4742170 * 2 ^ 59
def prefixEnd_4742170 : Nat := 4983230072969 + 3 ^ 40 * 4742170 * 2
def baseEnd_4742170 : Nat := 2435012555331816471766163

theorem tailTrace_4742170 : CollatzResearch.WordTrace tailWord_4742170 prefixEnd_4742170 2435012555331816471766163 := by
  unfold tailWord_4742170
  simp only [CollatzResearch.WordTrace]
  refine ⟨43240287307483865750455991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115307432819956975334549309 43240287307483865750455991)
  ·
    refine ⟨64860430961225798625683987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43240287307483865750455991 64860430961225798625683987)
    ·
      refine ⟨97290646441838697938525981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64860430961225798625683987 97290646441838697938525981)
      ·
        refine ⟨36483992415689511726947243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97290646441838697938525981 36483992415689511726947243)
        ·
          refine ⟨54725988623534267590420865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36483992415689511726947243 54725988623534267590420865)
          ·
            refine ⟨41044491467650700692815649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54725988623534267590420865 41044491467650700692815649)
            ·
              refine ⟨30783368600738025519611737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41044491467650700692815649 30783368600738025519611737)
              ·
                refine ⟨23087526450553519139708803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30783368600738025519611737 23087526450553519139708803)
                ·
                  refine ⟨34631289675830278709563205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23087526450553519139708803 34631289675830278709563205)
                  ·
                    refine ⟨6493366814218177258043101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34631289675830278709563205 6493366814218177258043101)
                    ·
                      refine ⟨2435012555331816471766163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493366814218177258043101 2435012555331816471766163)
                      ·
                        rfl

theorem cell23_4742170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_4742170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742170 prefixEnd_4742170 := by exact prefixLift 4742170
  have htrace : WordTrace (prefixWord ++ tailWord_4742170) baseStart_4742170 baseEnd_4742170 := by
    simpa [prefixWord, tailWord_4742170, baseEnd_4742170] using wordTrace_append hprefix tailTrace_4742170
  have hstable : (prefixWord ++ tailWord_4742170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742170).length < 2 ^ (prefixWord ++ tailWord_4742170).sum := by decide
  have hdescent : baseEnd_4742170 < baseStart_4742170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742177 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 3, 4]
def baseStart_4742177 : Nat := 118140960795 + 4742177 * 2 ^ 59
def prefixEnd_4742177 : Nat := 4983230072969 + 3 ^ 40 * 4742177 * 2
def baseEnd_4742177 : Nat := 811672049898799314792877

theorem tailTrace_4742177 : CollatzResearch.WordTrace tailWord_4742177 prefixEnd_4742177 811672049898799314792877 := by
  unfold tailWord_4742177
  simp only [CollatzResearch.WordTrace]
  refine ⟨172961404540910103197328785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115307603027273402131552523 172961404540910103197328785)
  ·
    refine ⟨129721053405682577397996589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172961404540910103197328785 129721053405682577397996589)
    ·
      refine ⟨48645395027130966524248721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129721053405682577397996589 48645395027130966524248721)
      ·
        refine ⟨36484046270348224893186541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48645395027130966524248721 36484046270348224893186541)
        ·
          refine ⟨13681517351380584334944953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36484046270348224893186541 13681517351380584334944953)
          ·
            refine ⟨10261138013535438251208715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13681517351380584334944953 10261138013535438251208715)
            ·
              refine ⟨15391707020303157376813073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10261138013535438251208715 15391707020303157376813073)
              ·
                refine ⟨11543780265227368032609805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15391707020303157376813073 11543780265227368032609805)
                ·
                  refine ⟨4328917599460263012228677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11543780265227368032609805 4328917599460263012228677)
                  ·
                    refine ⟨811672049898799314792877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328917599460263012228677 811672049898799314792877)
                    ·
                      rfl

theorem cell23_4742177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_4742177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742177 prefixEnd_4742177 := by exact prefixLift 4742177
  have htrace : WordTrace (prefixWord ++ tailWord_4742177) baseStart_4742177 baseEnd_4742177 := by
    simpa [prefixWord, tailWord_4742177, baseEnd_4742177] using wordTrace_append hprefix tailTrace_4742177
  have hstable : (prefixWord ++ tailWord_4742177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742177).length < 2 ^ (prefixWord ++ tailWord_4742177).sum := by decide
  have hdescent : baseEnd_4742177 < baseStart_4742177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742190 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_4742190 : Nat := 118140960795 + 4742190 * 2 ^ 59
def prefixEnd_4742190 : Nat := 4983230072969 + 3 ^ 40 * 4742190 * 2
def baseEnd_4742190 : Nat := 270558091660545154835119

theorem tailTrace_4742190 : CollatzResearch.WordTrace tailWord_4742190 prefixEnd_4742190 270558091660545154835119 := by
  unfold tailWord_4742190
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620234836232875802194003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115307919126575337611701349 21620234836232875802194003)
  ·
    refine ⟨32430352254349313703291005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21620234836232875802194003 32430352254349313703291005)
    ·
      refine ⟨12161382095380992638734127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32430352254349313703291005 12161382095380992638734127)
      ·
        refine ⟨18242073143071488958101191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161382095380992638734127 18242073143071488958101191)
        ·
          refine ⟨27363109714607233437151787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18242073143071488958101191 27363109714607233437151787)
          ·
            refine ⟨41044664571910850155727681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27363109714607233437151787 41044664571910850155727681)
            ·
              refine ⟨30783498428933137616795761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41044664571910850155727681 30783498428933137616795761)
              ·
                refine ⟨23087623821699853212596821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30783498428933137616795761 23087623821699853212596821)
                ·
                  refine ⟨270558091660545154835119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23087623821699853212596821 270558091660545154835119)
                  ·
                    rfl

theorem cell23_4742190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_4742190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742190 prefixEnd_4742190 := by exact prefixLift 4742190
  have htrace : WordTrace (prefixWord ++ tailWord_4742190) baseStart_4742190 baseEnd_4742190 := by
    simpa [prefixWord, tailWord_4742190, baseEnd_4742190] using wordTrace_append hprefix tailTrace_4742190
  have hstable : (prefixWord ++ tailWord_4742190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742190).length < 2 ^ (prefixWord ++ tailWord_4742190).sum := by decide
  have hdescent : baseEnd_4742190 < baseStart_4742190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742194 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_4742194 : Nat := 118140960795 + 4742194 * 2 ^ 59
def prefixEnd_4742194 : Nat := 4983230072969 + 3 ^ 40 * 4742194 * 2
def baseEnd_4742194 : Nat := 811674959622508125955351

theorem tailTrace_4742194 : CollatzResearch.WordTrace tailWord_4742194 prefixEnd_4742194 811674959622508125955351 := by
  unfold tailWord_4742194
  simp only [CollatzResearch.WordTrace]
  refine ⟨43240506145462128775174409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115308016387899010067131757 43240506145462128775174409)
  ·
    refine ⟨32430379609096596581380807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43240506145462128775174409 32430379609096596581380807)
    ·
      refine ⟨48645569413644894872071211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32430379609096596581380807 48645569413644894872071211)
      ·
        refine ⟨72968354120467342308106817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48645569413644894872071211 72968354120467342308106817)
        ·
          refine ⟨54726265590350506731080113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72968354120467342308106817 54726265590350506731080113)
          ·
            refine ⟨41044699192762880048310085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54726265590350506731080113 41044699192762880048310085)
            ·
              refine ⟨7695881098643040009058141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41044699192762880048310085 7695881098643040009058141)
              ·
                refine ⟨2885955411991140003396803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7695881098643040009058141 2885955411991140003396803)
                ·
                  refine ⟨4328933117986710005095205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885955411991140003396803 4328933117986710005095205)
                  ·
                    refine ⟨811674959622508125955351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328933117986710005095205 811674959622508125955351)
                    ·
                      rfl

theorem cell23_4742194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_4742194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742194 prefixEnd_4742194 := by exact prefixLift 4742194
  have htrace : WordTrace (prefixWord ++ tailWord_4742194) baseStart_4742194 baseEnd_4742194 := by
    simpa [prefixWord, tailWord_4742194, baseEnd_4742194] using wordTrace_append hprefix tailTrace_4742194
  have hstable : (prefixWord ++ tailWord_4742194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742194).length < 2 ^ (prefixWord ++ tailWord_4742194).sum := by decide
  have hdescent : baseEnd_4742194 < baseStart_4742194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742307 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 3]
def baseStart_4742307 : Nat := 118140960795 + 4742307 * 2 ^ 59
def prefixEnd_4742307 : Nat := 4983230072969 + 3 ^ 40 * 4742307 * 2
def baseEnd_4742307 : Nat := 2435082902181482435753033

theorem tailTrace_4742307 : CollatzResearch.WordTrace tailWord_4742307 prefixEnd_4742307 2435082902181482435753033 := by
  unfold tailWord_4742307
  simp only [CollatzResearch.WordTrace]
  refine ⟨172966146030439135399561175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115310764020292756933040783 172966146030439135399561175)
  ·
    refine ⟨259449219045658703099341763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172966146030439135399561175 259449219045658703099341763)
    ·
      refine ⟨389173828568488054649012645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259449219045658703099341763 389173828568488054649012645)
      ·
        refine ⟨72970092856591510246689871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389173828568488054649012645 72970092856591510246689871)
        ·
          refine ⟨109455139284887265370034807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72970092856591510246689871 109455139284887265370034807)
          ·
            refine ⟨164182708927330898055052211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109455139284887265370034807 164182708927330898055052211)
            ·
              refine ⟨246274063390996347082578317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164182708927330898055052211 246274063390996347082578317)
              ·
                refine ⟨92352773771623630155966869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246274063390996347082578317 92352773771623630155966869)
                ·
                  refine ⟨4329036270544857663560947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92352773771623630155966869 4329036270544857663560947)
                  ·
                    refine ⟨6493554405817286495341421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329036270544857663560947 6493554405817286495341421)
                    ·
                      refine ⟨2435082902181482435753033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493554405817286495341421 2435082902181482435753033)
                      ·
                        rfl

theorem cell23_4742307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_4742307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742307 prefixEnd_4742307 := by exact prefixLift 4742307
  have htrace : WordTrace (prefixWord ++ tailWord_4742307) baseStart_4742307 baseEnd_4742307 := by
    simpa [prefixWord, tailWord_4742307, baseEnd_4742307] using wordTrace_append hprefix tailTrace_4742307
  have hstable : (prefixWord ++ tailWord_4742307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742307).length < 2 ^ (prefixWord ++ tailWord_4742307).sum := by decide
  have hdescent : baseEnd_4742307 < baseStart_4742307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742338 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_4742338 : Nat := 118140960795 + 4742338 * 2 ^ 59
def prefixEnd_4742338 : Nat := 4983230072969 + 3 ^ 40 * 4742338 * 2
def baseEnd_4742338 : Nat := 2435098820081771814465391

theorem tailTrace_4742338 : CollatzResearch.WordTrace tailWord_4742338 prefixEnd_4742338 2435098820081771814465391 := by
  unfold tailWord_4742338
  simp only [CollatzResearch.WordTrace]
  refine ⟨43241819173331706923484917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115311517795551218462626445 43241819173331706923484917)
  ·
    refine ⟨4053920547499847524076711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43241819173331706923484917 4053920547499847524076711)
    ·
      refine ⟨6080880821249771286115067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4053920547499847524076711 6080880821249771286115067)
      ·
        refine ⟨9121321231874656929172601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6080880821249771286115067 9121321231874656929172601)
        ·
          refine ⟨6840990923905992696879451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9121321231874656929172601 6840990923905992696879451)
          ·
            refine ⟨10261486385858989045319177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840990923905992696879451 10261486385858989045319177)
            ·
              refine ⟨7696114789394241783989383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10261486385858989045319177 7696114789394241783989383)
              ·
                refine ⟨11544172184091362675984075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696114789394241783989383 11544172184091362675984075)
                ·
                  refine ⟨17316258276137044013976113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11544172184091362675984075 17316258276137044013976113)
                  ·
                    refine ⟨12987193707102783010482085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17316258276137044013976113 12987193707102783010482085)
                    ·
                      refine ⟨2435098820081771814465391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12987193707102783010482085 2435098820081771814465391)
                      ·
                        rfl

theorem cell23_4742338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_4742338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742338 prefixEnd_4742338 := by exact prefixLift 4742338
  have htrace : WordTrace (prefixWord ++ tailWord_4742338) baseStart_4742338 baseEnd_4742338 := by
    simpa [prefixWord, tailWord_4742338, baseEnd_4742338] using wordTrace_append hprefix tailTrace_4742338
  have hstable : (prefixWord ++ tailWord_4742338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742338).length < 2 ^ (prefixWord ++ tailWord_4742338).sum := by decide
  have hdescent : baseEnd_4742338 < baseStart_4742338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742342 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4742342 : Nat := 118140960795 + 4742342 * 2 ^ 59
def prefixEnd_4742342 : Nat := 4983230072969 + 3 ^ 40 * 4742342 * 2
def baseEnd_4742342 : Nat := 2435100874004389798815373

theorem tailTrace_4742342 : CollatzResearch.WordTrace tailWord_4742342 prefixEnd_4742342 2435100874004389798815373 := by
  unfold tailWord_4742342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405231955791010511783915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115311615056874890918056853 5405231955791010511783915)
  ·
    refine ⟨8107847933686515767675873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405231955791010511783915 8107847933686515767675873)
    ·
      refine ⟨6080885950264886825756905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8107847933686515767675873 6080885950264886825756905)
      ·
        refine ⟨4560664462698665119317679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6080885950264886825756905 4560664462698665119317679)
        ·
          refine ⟨6840996694047997678976519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560664462698665119317679 6840996694047997678976519)
          ·
            refine ⟨10261495041071996518464779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840996694047997678976519 10261495041071996518464779)
            ·
              refine ⟨15392242561607994777697169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10261495041071996518464779 15392242561607994777697169)
              ·
                refine ⟨11544181921205996083272877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15392242561607994777697169 11544181921205996083272877)
                ·
                  refine ⟨4329068220452248531227329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11544181921205996083272877 4329068220452248531227329)
                  ·
                    refine ⟨3246801165339186398420497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4329068220452248531227329 3246801165339186398420497)
                    ·
                      refine ⟨2435100874004389798815373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246801165339186398420497 2435100874004389798815373)
                      ·
                        rfl

theorem cell23_4742342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4742342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742342 prefixEnd_4742342 := by exact prefixLift 4742342
  have htrace : WordTrace (prefixWord ++ tailWord_4742342) baseStart_4742342 baseEnd_4742342 := by
    simpa [prefixWord, tailWord_4742342, baseEnd_4742342] using wordTrace_append hprefix tailTrace_4742342
  have hstable : (prefixWord ++ tailWord_4742342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742342).length < 2 ^ (prefixWord ++ tailWord_4742342).sum := by decide
  have hdescent : baseEnd_4742342 < baseStart_4742342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742368 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 1, 3, 2]
def baseStart_4742368 : Nat := 118140960795 + 4742368 * 2 ^ 59
def prefixEnd_4742368 : Nat := 4983230072969 + 3 ^ 40 * 4742368 * 2
def baseEnd_4742368 : Nat := 2435114224501406697090253

theorem tailTrace_4742368 : CollatzResearch.WordTrace tailWord_4742368 prefixEnd_4742368 2435114224501406697090253 := by
  unfold tailWord_4742368
  simp only [CollatzResearch.WordTrace]
  refine ⟨86484185441609071408765879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115312247255478761878354505 86484185441609071408765879)
  ·
    refine ⟨129726278162413607113148819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86484185441609071408765879 129726278162413607113148819)
    ·
      refine ⟨194589417243620410669723229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129726278162413607113148819 194589417243620410669723229)
      ·
        refine ⟨72971031466357654001146211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194589417243620410669723229 72971031466357654001146211)
        ·
          refine ⟨109456547199536481001719317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72971031466357654001146211 109456547199536481001719317)
          ·
            refine ⟨5130775649978272546955593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109456547199536481001719317 5130775649978272546955593)
            ·
              refine ⟨3848081737483704410216695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5130775649978272546955593 3848081737483704410216695)
              ·
                refine ⟨5772122606225556615325043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848081737483704410216695 5772122606225556615325043)
                ·
                  refine ⟨8658183909338334922987565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5772122606225556615325043 8658183909338334922987565)
                  ·
                    refine ⟨3246818966001875596120337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8658183909338334922987565 3246818966001875596120337)
                    ·
                      refine ⟨2435114224501406697090253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246818966001875596120337 2435114224501406697090253)
                      ·
                        rfl

theorem cell23_4742368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_4742368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742368 prefixEnd_4742368 := by exact prefixLift 4742368
  have htrace : WordTrace (prefixWord ++ tailWord_4742368) baseStart_4742368 baseEnd_4742368 := by
    simpa [prefixWord, tailWord_4742368, baseEnd_4742368] using wordTrace_append hprefix tailTrace_4742368
  have hstable : (prefixWord ++ tailWord_4742368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742368).length < 2 ^ (prefixWord ++ tailWord_4742368).sum := by decide
  have hdescent : baseEnd_4742368 < baseStart_4742368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742375 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4742375 : Nat := 118140960795 + 4742375 * 2 ^ 59
def prefixEnd_4742375 : Nat := 4983230072969 + 3 ^ 40 * 4742375 * 2
def baseEnd_4742375 : Nat := 2435117818865988169702721

theorem tailTrace_4742375 : CollatzResearch.WordTrace tailWord_4742375 prefixEnd_4742375 2435117818865988169702721 := by
  unfold tailWord_4742375
  simp only [CollatzResearch.WordTrace]
  refine ⟨172968626194192783013036579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115312417462795188675357719 172968626194192783013036579)
  ·
    refine ⟨259452939291289174519554869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172968626194192783013036579 259452939291289174519554869)
    ·
      refine ⟨24323713058558360111208269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259452939291289174519554869 24323713058558360111208269)
      ·
        refine ⟨9121392396959385041703101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24323713058558360111208269 9121392396959385041703101)
        ·
          refine ⟨3420522148859769390638663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9121392396959385041703101 3420522148859769390638663)
          ·
            refine ⟨5130783223289654085957995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420522148859769390638663 5130783223289654085957995)
            ·
              refine ⟨7696174834934481128936993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130783223289654085957995 7696174834934481128936993)
              ·
                refine ⟨5772131126200860846702745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7696174834934481128936993 5772131126200860846702745)
                ·
                  refine ⟨4329098344650645635027059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5772131126200860846702745 4329098344650645635027059)
                  ·
                    refine ⟨6493647516975968452540589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329098344650645635027059 6493647516975968452540589)
                    ·
                      refine ⟨2435117818865988169702721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6493647516975968452540589 2435117818865988169702721)
                      ·
                        rfl

theorem cell23_4742375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4742375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742375 prefixEnd_4742375 := by exact prefixLift 4742375
  have htrace : WordTrace (prefixWord ++ tailWord_4742375) baseStart_4742375 baseEnd_4742375 := by
    simpa [prefixWord, tailWord_4742375, baseEnd_4742375] using wordTrace_append hprefix tailTrace_4742375
  have hstable : (prefixWord ++ tailWord_4742375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742375).length < 2 ^ (prefixWord ++ tailWord_4742375).sum := by decide
  have hdescent : baseEnd_4742375 < baseStart_4742375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742387 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 7]
def baseStart_4742387 : Nat := 118140960795 + 4742387 * 2 ^ 59
def prefixEnd_4742387 : Nat := 4983230072969 + 3 ^ 40 * 4742387 * 2
def baseEnd_4742387 : Nat := 270569331181538013639185

theorem tailTrace_4742387 : CollatzResearch.WordTrace tailWord_4742387 prefixEnd_4742387 270569331181538013639185 := by
  unfold tailWord_4742387
  simp only [CollatzResearch.WordTrace]
  refine ⟨172969063870149309062473415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115312709246766206041648943 172969063870149309062473415)
  ·
    refine ⟨259453595805223963593710123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172969063870149309062473415 259453595805223963593710123)
    ·
      refine ⟨389180393707835945390565185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259453595805223963593710123 389180393707835945390565185)
      ·
        refine ⟨291885295280876959042923889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389180393707835945390565185 291885295280876959042923889)
        ·
          refine ⟨218913971460657719282192917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291885295280876959042923889 218913971460657719282192917)
          ·
            refine ⟨10261592412218330591352793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 218913971460657719282192917 10261592412218330591352793)
            ·
              refine ⟨7696194309163747943514595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10261592412218330591352793 7696194309163747943514595)
              ·
                refine ⟨11544291463745621915271893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696194309163747943514595 11544291463745621915271893)
                ·
                  refine ⟨270569331181538013639185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11544291463745621915271893 270569331181538013639185)
                  ·
                    rfl

theorem cell23_4742387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 7].length) (baseStart_4742387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742387 prefixEnd_4742387 := by exact prefixLift 4742387
  have htrace : WordTrace (prefixWord ++ tailWord_4742387) baseStart_4742387 baseEnd_4742387 := by
    simpa [prefixWord, tailWord_4742387, baseEnd_4742387] using wordTrace_append hprefix tailTrace_4742387
  have hstable : (prefixWord ++ tailWord_4742387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742387).length < 2 ^ (prefixWord ++ tailWord_4742387).sum := by decide
  have hdescent : baseEnd_4742387 < baseStart_4742387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742398 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4742398 : Nat := 118140960795 + 4742398 * 2 ^ 59
def prefixEnd_4742398 : Nat := 4983230072969 + 3 ^ 40 * 4742398 * 2
def baseEnd_4742398 : Nat := 2435129628921041579715115

theorem tailTrace_4742398 : CollatzResearch.WordTrace tailWord_4742398 prefixEnd_4742398 2435129628921041579715115 := by
  unfold tailWord_4742398
  simp only [CollatzResearch.WordTrace]
  refine ⟨21621183134138682242640481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115312976715406305294082565 21621183134138682242640481)
  ·
    refine ⟨16215887350604011681980361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21621183134138682242640481 16215887350604011681980361)
    ·
      refine ⟨12161915512953008761485271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16215887350604011681980361 12161915512953008761485271)
      ·
        refine ⟨18242873269429513142227907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161915512953008761485271 18242873269429513142227907)
        ·
          refine ⟨27364309904144269713341861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18242873269429513142227907 27364309904144269713341861)
          ·
            refine ⟨5130808107027050571251599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27364309904144269713341861 5130808107027050571251599)
            ·
              refine ⟨7696212160540575856877399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130808107027050571251599 7696212160540575856877399)
              ·
                refine ⟨11544318240810863785316099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696212160540575856877399 11544318240810863785316099)
                ·
                  refine ⟨17316477361216295677974149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11544318240810863785316099 17316477361216295677974149)
                  ·
                    refine ⟨3246839505228055439620153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17316477361216295677974149 3246839505228055439620153)
                    ·
                      refine ⟨2435129628921041579715115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246839505228055439620153 2435129628921041579715115)
                      ·
                        rfl

theorem cell23_4742398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4742398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742398 prefixEnd_4742398 := by exact prefixLift 4742398
  have htrace : WordTrace (prefixWord ++ tailWord_4742398) baseStart_4742398 baseEnd_4742398 := by
    simpa [prefixWord, tailWord_4742398, baseEnd_4742398] using wordTrace_append hprefix tailTrace_4742398
  have hstable : (prefixWord ++ tailWord_4742398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742398).length < 2 ^ (prefixWord ++ tailWord_4742398).sum := by decide
  have hdescent : baseEnd_4742398 < baseStart_4742398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742417 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_4742417 : Nat := 118140960795 + 4742417 * 2 ^ 59
def prefixEnd_4742417 : Nat := 4983230072969 + 3 ^ 40 * 4742417 * 2
def baseEnd_4742417 : Nat := 811713128351159001792509

theorem tailTrace_4742417 : CollatzResearch.WordTrace tailWord_4742417 prefixEnd_4742417 811713128351159001792509 := by
  unfold tailWord_4742417
  simp only [CollatzResearch.WordTrace]
  refine ⟨172970158060040624186065505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115313438706693749457377003 172970158060040624186065505)
  ·
    refine ⟨129727618545030468139549129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172970158060040624186065505 129727618545030468139549129)
    ·
      refine ⟨97295713908772851104661847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129727618545030468139549129 97295713908772851104661847)
      ·
        refine ⟨145943570863159276656992771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97295713908772851104661847 145943570863159276656992771)
        ·
          refine ⟨218915356294738914985489157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145943570863159276656992771 218915356294738914985489157)
          ·
            refine ⟨41046629305263546559779217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218915356294738914985489157 41046629305263546559779217)
            ·
              refine ⟨30784971978947659919834413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41046629305263546559779217 30784971978947659919834413)
              ·
                refine ⟨11544364492105372469937905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30784971978947659919834413 11544364492105372469937905)
                ·
                  refine ⟨8658273369079029352453429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11544364492105372469937905 8658273369079029352453429)
                  ·
                    refine ⟨811713128351159001792509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8658273369079029352453429 811713128351159001792509)
                    ·
                      rfl

theorem cell23_4742417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_4742417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742417 prefixEnd_4742417 := by exact prefixLift 4742417
  have htrace : WordTrace (prefixWord ++ tailWord_4742417) baseStart_4742417 baseEnd_4742417 := by
    simpa [prefixWord, tailWord_4742417, baseEnd_4742417] using wordTrace_append hprefix tailTrace_4742417
  have hstable : (prefixWord ++ tailWord_4742417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742417).length < 2 ^ (prefixWord ++ tailWord_4742417).sum := by decide
  have hdescent : baseEnd_4742417 < baseStart_4742417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742481 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 1, 4]
def baseStart_4742481 : Nat := 118140960795 + 4742481 * 2 ^ 59
def prefixEnd_4742481 : Nat := 4983230072969 + 3 ^ 40 * 4742481 * 2
def baseEnd_4742481 : Nat := 811724082605121584992411

theorem tailTrace_4742481 : CollatzResearch.WordTrace tailWord_4742481 prefixEnd_4742481 811724082605121584992411 := by
  unfold tailWord_4742481
  simp only [CollatzResearch.WordTrace]
  refine ⟨172972492331808763116395297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115314994887872508744263531 172972492331808763116395297)
  ·
    refine ⟨129729369248856572337296473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172972492331808763116395297 129729369248856572337296473)
    ·
      refine ⟨97297026936642429252972355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129729369248856572337296473 97297026936642429252972355)
      ·
        refine ⟨145945540404963643879458533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97297026936642429252972355 145945540404963643879458533)
        ·
          refine ⟨27364788825930683227398475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145945540404963643879458533 27364788825930683227398475)
          ·
            refine ⟨41047183238896024841097713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27364788825930683227398475 41047183238896024841097713)
            ·
              refine ⟨30785387429172018630823285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41047183238896024841097713 30785387429172018630823285)
              ·
                refine ⟨2886130071484876746639683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30785387429172018630823285 2886130071484876746639683)
                ·
                  refine ⟨4329195107227315119959525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886130071484876746639683 4329195107227315119959525)
                  ·
                    refine ⟨811724082605121584992411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329195107227315119959525 811724082605121584992411)
                    ·
                      rfl

theorem cell23_4742481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_4742481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742481 prefixEnd_4742481 := by exact prefixLift 4742481
  have htrace : WordTrace (prefixWord ++ tailWord_4742481) baseStart_4742481 baseEnd_4742481 := by
    simpa [prefixWord, tailWord_4742481, baseEnd_4742481] using wordTrace_append hprefix tailTrace_4742481
  have hstable : (prefixWord ++ tailWord_4742481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742481).length < 2 ^ (prefixWord ++ tailWord_4742481).sum := by decide
  have hdescent : baseEnd_4742481 < baseStart_4742481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742498 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4742498 : Nat := 118140960795 + 4742498 * 2 ^ 59
def prefixEnd_4742498 : Nat := 4983230072969 + 3 ^ 40 * 4742498 * 2
def baseEnd_4742498 : Nat := 811726992328830396154885

theorem tailTrace_4742498 : CollatzResearch.WordTrace tailWord_4742498 prefixEnd_4742498 811726992328830396154885 := by
  unfold tailWord_4742498
  simp only [CollatzResearch.WordTrace]
  refine ⟨43243278093186793754941037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115315408248498116679842765 43243278093186793754941037)
  ·
    refine ⟨16216229284945047658102889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43243278093186793754941037 16216229284945047658102889)
    ·
      refine ⟨12162171963708785743577167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16216229284945047658102889 12162171963708785743577167)
      ·
        refine ⟨18243257945563178615365751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12162171963708785743577167 18243257945563178615365751)
        ·
          refine ⟨27364886918344767923048627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243257945563178615365751 27364886918344767923048627)
          ·
            refine ⟨41047330377517151884572941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27364886918344767923048627 41047330377517151884572941)
            ·
              refine ⟨15392748891568931956714853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41047330377517151884572941 15392748891568931956714853)
              ·
                refine ⟨2886140417169174741884035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15392748891568931956714853 2886140417169174741884035)
                ·
                  refine ⟨4329210625753762112826053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886140417169174741884035 4329210625753762112826053)
                  ·
                    refine ⟨811726992328830396154885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329210625753762112826053 811726992328830396154885)
                    ·
                      rfl

theorem cell23_4742498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4742498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742498 prefixEnd_4742498 := by exact prefixLift 4742498
  have htrace : WordTrace (prefixWord ++ tailWord_4742498) baseStart_4742498 baseEnd_4742498 := by
    simpa [prefixWord, tailWord_4742498, baseEnd_4742498] using wordTrace_append hprefix tailTrace_4742498
  have hstable : (prefixWord ++ tailWord_4742498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742498).length < 2 ^ (prefixWord ++ tailWord_4742498).sum := by decide
  have hdescent : baseEnd_4742498 < baseStart_4742498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742524 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_4742524 : Nat := 118140960795 + 4742524 * 2 ^ 59
def prefixEnd_4742524 : Nat := 4983230072969 + 3 ^ 40 * 4742524 * 2
def baseEnd_4742524 : Nat := 811731442494502695579845

theorem tailTrace_4742524 : CollatzResearch.WordTrace tailWord_4742524 prefixEnd_4742524 811731442494502695579845 := by
  unfold tailWord_4742524
  simp only [CollatzResearch.WordTrace]
  refine ⟨86487030335326490730105313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115316040447101987640140417 86487030335326490730105313)
  ·
    refine ⟨64865272751494868047578985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86487030335326490730105313 64865272751494868047578985)
    ·
      refine ⟨48648954563621151035684239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64865272751494868047578985 48648954563621151035684239)
      ·
        refine ⟨72973431845431726553526359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48648954563621151035684239 72973431845431726553526359)
        ·
          refine ⟨109460147768147589830289539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72973431845431726553526359 109460147768147589830289539)
          ·
            refine ⟨164190221652221384745434309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109460147768147589830289539 164190221652221384745434309)
            ·
              refine ⟨30785666559791509639768933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164190221652221384745434309 30785666559791509639768933)
              ·
                refine ⟨5772312479960908057456675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30785666559791509639768933 5772312479960908057456675)
                ·
                  refine ⟨8658468719941362086185013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5772312479960908057456675 8658468719941362086185013)
                  ·
                    refine ⟨811731442494502695579845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8658468719941362086185013 811731442494502695579845)
                    ·
                      rfl

theorem cell23_4742524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_4742524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742524 prefixEnd_4742524 := by exact prefixLift 4742524
  have htrace : WordTrace (prefixWord ++ tailWord_4742524) baseStart_4742524 baseEnd_4742524 := by
    simpa [prefixWord, tailWord_4742524, baseEnd_4742524] using wordTrace_append hprefix tailTrace_4742524
  have hstable : (prefixWord ++ tailWord_4742524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742524).length < 2 ^ (prefixWord ++ tailWord_4742524).sum := by decide
  have hdescent : baseEnd_4742524 < baseStart_4742524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742531 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 1, 5, 2]
def baseStart_4742531 : Nat := 118140960795 + 4742531 * 2 ^ 59
def prefixEnd_4742531 : Nat := 4983230072969 + 3 ^ 40 * 4742531 * 2
def baseEnd_4742531 : Nat := 2435197921848089559352003

theorem tailTrace_4742531 : CollatzResearch.WordTrace tailWord_4742531 prefixEnd_4742531 2435197921848089559352003 := by
  unfold tailWord_4742531
  simp only [CollatzResearch.WordTrace]
  refine ⟨172974315981627621655715447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115316210654418414437143631 172974315981627621655715447)
  ·
    refine ⟨259461473972441432483573171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172974315981627621655715447 259461473972441432483573171)
    ·
      refine ⟨389192210958662148725359757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259461473972441432483573171 389192210958662148725359757)
      ·
        refine ⟨145947079109498305772009909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389192210958662148725359757 145947079109498305772009909)
        ·
          refine ⟨13682538666515466166125929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145947079109498305772009909 13682538666515466166125929)
          ·
            refine ⟨10261903999886599624594447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13682538666515466166125929 10261903999886599624594447)
            ·
              refine ⟨15392855999829899436891671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10261903999886599624594447 15392855999829899436891671)
              ·
                refine ⟨23089283999744849155337507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15392855999829899436891671 23089283999744849155337507)
                ·
                  refine ⟨34633925999617273733006261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23089283999744849155337507 34633925999617273733006261)
                  ·
                    refine ⟨3246930562464119412469337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34633925999617273733006261 3246930562464119412469337)
                    ·
                      refine ⟨2435197921848089559352003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246930562464119412469337 2435197921848089559352003)
                      ·
                        rfl

theorem cell23_4742531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_4742531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742531 prefixEnd_4742531 := by exact prefixLift 4742531
  have htrace : WordTrace (prefixWord ++ tailWord_4742531) baseStart_4742531 baseEnd_4742531 := by
    simpa [prefixWord, tailWord_4742531, baseEnd_4742531] using wordTrace_append hprefix tailTrace_4742531
  have hstable : (prefixWord ++ tailWord_4742531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742531).length < 2 ^ (prefixWord ++ tailWord_4742531).sum := by decide
  have hdescent : baseEnd_4742531 < baseStart_4742531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742547 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5]
def baseStart_4742547 : Nat := 118140960795 + 4742547 * 2 ^ 59
def prefixEnd_4742547 : Nat := 4983230072969 + 3 ^ 40 * 4742547 * 2
def baseEnd_4742547 : Nat := 2435206137538561496751929

theorem tailTrace_4742547 : CollatzResearch.WordTrace tailWord_4742547 prefixEnd_4742547 2435206137538561496751929 := by
  unfold tailWord_4742547
  simp only [CollatzResearch.WordTrace]
  refine ⟨172974899549569656388297895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115316599699713104258865263 172974899549569656388297895)
  ·
    refine ⟨259462349324354484582446843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172974899549569656388297895 259462349324354484582446843)
    ·
      refine ⟨389193523986531726873670265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259462349324354484582446843 389193523986531726873670265)
      ·
        refine ⟨291895142989898795155252699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389193523986531726873670265 291895142989898795155252699)
        ·
          refine ⟨437842714484848192732879049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291895142989898795155252699 437842714484848192732879049)
          ·
            refine ⟨328382035863636144549659287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437842714484848192732879049 328382035863636144549659287)
            ·
              refine ⟨492573053795454216824488931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328382035863636144549659287 492573053795454216824488931)
              ·
                refine ⟨738859580693181325236733397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492573053795454216824488931 738859580693181325236733397)
                ·
                  refine ⟨17317021422496437310235939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 738859580693181325236733397 17317021422496437310235939)
                  ·
                    refine ⟨25975532133744655965353909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17317021422496437310235939 25975532133744655965353909)
                    ·
                      refine ⟨2435206137538561496751929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25975532133744655965353909 2435206137538561496751929)
                      ·
                        rfl

theorem cell23_4742547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_4742547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742547 prefixEnd_4742547 := by exact prefixLift 4742547
  have htrace : WordTrace (prefixWord ++ tailWord_4742547) baseStart_4742547 baseEnd_4742547 := by
    simpa [prefixWord, tailWord_4742547, baseEnd_4742547] using wordTrace_append hprefix tailTrace_4742547
  have hstable : (prefixWord ++ tailWord_4742547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742547).length < 2 ^ (prefixWord ++ tailWord_4742547).sum := by decide
  have hdescent : baseEnd_4742547 < baseStart_4742547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742584 : List Nat := [2, 1, 2, 1, 2, 2, 6, 7]
def baseStart_4742584 : Nat := 118140960795 + 4742584 * 2 ^ 59
def prefixEnd_4742584 : Nat := 4983230072969 + 3 ^ 40 * 4742584 * 2
def baseEnd_4742584 : Nat := 90193523567510290814417

theorem tailTrace_4742584 : CollatzResearch.WordTrace tailWord_4742584 prefixEnd_4742584 90193523567510290814417 := by
  unfold tailWord_4742584
  simp only [CollatzResearch.WordTrace]
  refine ⟨86488124525217805853697403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115317499366957074471596537 86488124525217805853697403)
  ·
    refine ⟨129732186787826708780546105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86488124525217805853697403 129732186787826708780546105)
    ·
      refine ⟨97299140090870031585409579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129732186787826708780546105 97299140090870031585409579)
      ·
        refine ⟨145948710136305047378114369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97299140090870031585409579 145948710136305047378114369)
        ·
          refine ⟨109461532602228785533585777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145948710136305047378114369 109461532602228785533585777)
          ·
            refine ⟨82096149451671589150189333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109461532602228785533585777 82096149451671589150189333)
            ·
              refine ⟨3848257005547105741415125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82096149451671589150189333 3848257005547105741415125)
              ·
                refine ⟨90193523567510290814417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3848257005547105741415125 90193523567510290814417)
                ·
                  rfl

theorem cell23_4742584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 7].length) (baseStart_4742584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742584 prefixEnd_4742584 := by exact prefixLift 4742584
  have htrace : WordTrace (prefixWord ++ tailWord_4742584) baseStart_4742584 baseEnd_4742584 := by
    simpa [prefixWord, tailWord_4742584, baseEnd_4742584] using wordTrace_append hprefix tailTrace_4742584
  have hstable : (prefixWord ++ tailWord_4742584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742584).length < 2 ^ (prefixWord ++ tailWord_4742584).sum := by decide
  have hdescent : baseEnd_4742584 < baseStart_4742584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742595 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 1, 2, 2]
def baseStart_4742595 : Nat := 118140960795 + 4742595 * 2 ^ 59
def prefixEnd_4742595 : Nat := 4983230072969 + 3 ^ 40 * 4742595 * 2
def baseEnd_4742595 : Nat := 2435230784609977308951709

theorem tailTrace_4742595 : CollatzResearch.WordTrace tailWord_4742595 prefixEnd_4742595 2435230784609977308951709 := by
  unfold tailWord_4742595
  simp only [CollatzResearch.WordTrace]
  refine ⟨172976650253395760586045239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115317766835597173724030159 172976650253395760586045239)
  ·
    refine ⟨259464975380093640879067859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172976650253395760586045239 259464975380093640879067859)
    ·
      refine ⟨389197463070140461318601789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259464975380093640879067859 389197463070140461318601789)
      ·
        refine ⟨145949048651302672994475671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389197463070140461318601789 145949048651302672994475671)
        ·
          refine ⟨218923572976954009491713507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145949048651302672994475671 218923572976954009491713507)
          ·
            refine ⟨328385359465431014237570261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218923572976954009491713507 328385359465431014237570261)
            ·
              refine ⟨7696531862471039396193053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 328385359465431014237570261 7696531862471039396193053)
              ·
                refine ⟨2886199448426639773572395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7696531862471039396193053 2886199448426639773572395)
                ·
                  refine ⟨4329299172639959660358593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886199448426639773572395 4329299172639959660358593)
                  ·
                    refine ⟨3246974379479969745268945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4329299172639959660358593 3246974379479969745268945)
                    ·
                      refine ⟨2435230784609977308951709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246974379479969745268945 2435230784609977308951709)
                      ·
                        rfl

theorem cell23_4742595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_4742595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742595 prefixEnd_4742595 := by exact prefixLift 4742595
  have htrace : WordTrace (prefixWord ++ tailWord_4742595) baseStart_4742595 baseEnd_4742595 := by
    simpa [prefixWord, tailWord_4742595, baseEnd_4742595] using wordTrace_append hprefix tailTrace_4742595
  have hstable : (prefixWord ++ tailWord_4742595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742595).length < 2 ^ (prefixWord ++ tailWord_4742595).sum := by decide
  have hdescent : baseEnd_4742595 < baseStart_4742595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742612 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_4742612 : Nat := 118140960795 + 4742612 * 2 ^ 59
def prefixEnd_4742612 : Nat := 4983230072969 + 3 ^ 40 * 4742612 * 2
def baseEnd_4742612 : Nat := 2435239513781103742439131

theorem tailTrace_4742612 : CollatzResearch.WordTrace tailWord_4742612 prefixEnd_4742612 2435239513781103742439131 := by
  unfold tailWord_4742612
  simp only [CollatzResearch.WordTrace]
  refine ⟨86488635147167086244707045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115318180196222781659609393 86488635147167086244707045)
  ·
    refine ⟨16216619090093828670882571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86488635147167086244707045 16216619090093828670882571)
    ·
      refine ⟨24324928635140743006323857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216619090093828670882571 24324928635140743006323857)
      ·
        refine ⟨18243696476355557254742893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24324928635140743006323857 18243696476355557254742893)
        ·
          refine ⟨6841386178633333970528585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18243696476355557254742893 6841386178633333970528585)
          ·
            refine ⟨5131039633975000477896439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6841386178633333970528585 5131039633975000477896439)
            ·
              refine ⟨7696559450962500716844659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5131039633975000477896439 7696559450962500716844659)
              ·
                refine ⟨11544839176443751075266989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696559450962500716844659 11544839176443751075266989)
                ·
                  refine ⟨4329314691166406653225121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11544839176443751075266989 4329314691166406653225121)
                  ·
                    refine ⟨3246986018374804989918841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4329314691166406653225121 3246986018374804989918841)
                    ·
                      refine ⟨2435239513781103742439131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3246986018374804989918841 2435239513781103742439131)
                      ·
                        rfl

theorem cell23_4742612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_4742612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742612 prefixEnd_4742612 := by exact prefixLift 4742612
  have htrace : WordTrace (prefixWord ++ tailWord_4742612) baseStart_4742612 baseEnd_4742612 := by
    simpa [prefixWord, tailWord_4742612, baseEnd_4742612] using wordTrace_append hprefix tailTrace_4742612
  have hstable : (prefixWord ++ tailWord_4742612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742612).length < 2 ^ (prefixWord ++ tailWord_4742612).sum := by decide
  have hdescent : baseEnd_4742612 < baseStart_4742612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742638 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_4742638 : Nat := 118140960795 + 4742638 * 2 ^ 59
def prefixEnd_4742638 : Nat := 4983230072969 + 3 ^ 40 * 4742638 * 2
def baseEnd_4742638 : Nat := 2435252864278120640714011

theorem tailTrace_4742638 : CollatzResearch.WordTrace tailWord_4742638 prefixEnd_4742638 2435252864278120640714011 := by
  unfold tailWord_4742638
  simp only [CollatzResearch.WordTrace]
  refine ⟨21622277324029997366232571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115318812394826652619907045 21622277324029997366232571)
  ·
    refine ⟨32433415986044996049348857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21622277324029997366232571 32433415986044996049348857)
    ·
      refine ⟨24325061989533747037011643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32433415986044996049348857 24325061989533747037011643)
      ·
        refine ⟨36487592984300620555517465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24325061989533747037011643 36487592984300620555517465)
        ·
          refine ⟨27365694738225465416638099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36487592984300620555517465 27365694738225465416638099)
          ·
            refine ⟨41048542107338198124957149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27365694738225465416638099 41048542107338198124957149)
            ·
              refine ⟨15393203290251824296858931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41048542107338198124957149 15393203290251824296858931)
              ·
                refine ⟨23089804935377736445288397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15393203290251824296858931 23089804935377736445288397)
                ·
                  refine ⟨8658676850766651166983149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23089804935377736445288397 8658676850766651166983149)
                  ·
                    refine ⟨3247003819037494187618681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8658676850766651166983149 3247003819037494187618681)
                    ·
                      refine ⟨2435252864278120640714011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247003819037494187618681 2435252864278120640714011)
                      ·
                        rfl

theorem cell23_4742638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_4742638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742638 prefixEnd_4742638 := by exact prefixLift 4742638
  have htrace : WordTrace (prefixWord ++ tailWord_4742638) baseStart_4742638 baseEnd_4742638 := by
    simpa [prefixWord, tailWord_4742638, baseEnd_4742638] using wordTrace_append hprefix tailTrace_4742638
  have hstable : (prefixWord ++ tailWord_4742638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742638).length < 2 ^ (prefixWord ++ tailWord_4742638).sum := by decide
  have hdescent : baseEnd_4742638 < baseStart_4742638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742651 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 1, 4, 2]
def baseStart_4742651 : Nat := 118140960795 + 4742651 * 2 ^ 59
def prefixEnd_4742651 : Nat := 4983230072969 + 3 ^ 40 * 4742651 * 2
def baseEnd_4742651 : Nat := 2435259539526629089851451

theorem tailTrace_4742651 : CollatzResearch.WordTrace tailWord_4742651 prefixEnd_4742651 2435259539526629089851451 := by
  unfold tailWord_4742651
  simp only [CollatzResearch.WordTrace]
  refine ⟨172978692741192882150083807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115319128494128588100055871 172978692741192882150083807)
  ·
    refine ⟨259468039111789323225125711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172978692741192882150083807 259468039111789323225125711)
    ·
      refine ⟨389202058667683984837688567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259468039111789323225125711 389202058667683984837688567)
      ·
        refine ⟨583803088001525977256532851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389202058667683984837688567 583803088001525977256532851)
        ·
          refine ⟨875704632002288965884799277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583803088001525977256532851 875704632002288965884799277)
          ·
            refine ⟨328389237000858362206799729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 875704632002288965884799277 328389237000858362206799729)
            ·
              refine ⟨246291927750643771655099797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328389237000858362206799729 246291927750643771655099797)
              ·
                refine ⟨11544934113311426796332803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 246291927750643771655099797 11544934113311426796332803)
                ·
                  refine ⟨17317401169967140194499205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11544934113311426796332803 17317401169967140194499205)
                  ·
                    refine ⟨3247012719368838786468601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17317401169967140194499205 3247012719368838786468601)
                    ·
                      refine ⟨2435259539526629089851451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247012719368838786468601 2435259539526629089851451)
                      ·
                        rfl

theorem cell23_4742651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4, 2].length) (baseStart_4742651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742651 prefixEnd_4742651 := by exact prefixLift 4742651
  have htrace : WordTrace (prefixWord ++ tailWord_4742651) baseStart_4742651 baseEnd_4742651 := by
    simpa [prefixWord, tailWord_4742651, baseEnd_4742651] using wordTrace_append hprefix tailTrace_4742651
  have hstable : (prefixWord ++ tailWord_4742651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742651).length < 2 ^ (prefixWord ++ tailWord_4742651).sum := by decide
  have hdescent : baseEnd_4742651 < baseStart_4742651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742685 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_4742685 : Nat := 118140960795 + 4742685 * 2 ^ 59
def prefixEnd_4742685 : Nat := 4983230072969 + 3 ^ 40 * 4742685 * 2
def baseEnd_4742685 : Nat := 2435276997868881956826295

theorem tailTrace_4742685 : CollatzResearch.WordTrace tailWord_4742685 prefixEnd_4742685 2435276997868881956826295 := by
  unfold tailWord_4742685
  simp only [CollatzResearch.WordTrace]
  refine ⟨172979932823069705956821509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115319955215379803971214339 172979932823069705956821509)
  ·
    refine ⟨32433737404325569866904033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172979932823069705956821509 32433737404325569866904033)
    ·
      refine ⟨24325303053244177400178025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32433737404325569866904033 24325303053244177400178025)
      ·
        refine ⟨18243977289933133050133519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24325303053244177400178025 18243977289933133050133519)
        ·
          refine ⟨27365965934899699575200279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243977289933133050133519 27365965934899699575200279)
          ·
            refine ⟨41048948902349549362800419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27365965934899699575200279 41048948902349549362800419)
            ·
              refine ⟨61573423353524324044200629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41048948902349549362800419 61573423353524324044200629)
              ·
                refine ⟨5772508439392905379143809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61573423353524324044200629 5772508439392905379143809)
                ·
                  refine ⟨4329381329544679034357857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5772508439392905379143809 4329381329544679034357857)
                  ·
                    refine ⟨3247035997158509275768393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4329381329544679034357857 3247035997158509275768393)
                    ·
                      refine ⟨2435276997868881956826295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247035997158509275768393 2435276997868881956826295)
                      ·
                        rfl

theorem cell23_4742685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_4742685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742685 prefixEnd_4742685 := by exact prefixLift 4742685
  have htrace : WordTrace (prefixWord ++ tailWord_4742685) baseStart_4742685 baseEnd_4742685 := by
    simpa [prefixWord, tailWord_4742685, baseEnd_4742685] using wordTrace_append hprefix tailTrace_4742685
  have hstable : (prefixWord ++ tailWord_4742685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742685).length < 2 ^ (prefixWord ++ tailWord_4742685).sum := by decide
  have hdescent : baseEnd_4742685 < baseStart_4742685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742691 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 7]
def baseStart_4742691 : Nat := 118140960795 + 4742691 * 2 ^ 59
def prefixEnd_4742691 : Nat := 4983230072969 + 3 ^ 40 * 4742691 * 2
def baseEnd_4742691 : Nat := 270586675416978770372363

theorem tailTrace_4742691 : CollatzResearch.WordTrace tailWord_4742691 prefixEnd_4742691 270586675416978770372363 := by
  unfold tailWord_4742691
  simp only [CollatzResearch.WordTrace]
  refine ⟨172980151661047968981539927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115320101107365312654359951 172980151661047968981539927)
  ·
    refine ⟨259470227491571953472309891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172980151661047968981539927 259470227491571953472309891)
    ·
      refine ⟨389205341237357930208464837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259470227491571953472309891 389205341237357930208464837)
      ·
        refine ⟨72976001482004611914087157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389205341237357930208464837 72976001482004611914087157)
        ·
          refine ⟨6841500138937932366945671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72976001482004611914087157 6841500138937932366945671)
          ·
            refine ⟨10262250208406898550418507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6841500138937932366945671 10262250208406898550418507)
            ·
              refine ⟨15393375312610347825627761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262250208406898550418507 15393375312610347825627761)
              ·
                refine ⟨11545031484457760869220821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15393375312610347825627761 11545031484457760869220821)
                ·
                  refine ⟨270586675416978770372363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11545031484457760869220821 270586675416978770372363)
                  ·
                    rfl

theorem cell23_4742691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 7].length) (baseStart_4742691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742691 prefixEnd_4742691 := by exact prefixLift 4742691
  have htrace : WordTrace (prefixWord ++ tailWord_4742691) baseStart_4742691 baseEnd_4742691 := by
    simpa [prefixWord, tailWord_4742691, baseEnd_4742691] using wordTrace_append hprefix tailTrace_4742691
  have hstable : (prefixWord ++ tailWord_4742691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742691).length < 2 ^ (prefixWord ++ tailWord_4742691).sum := by decide
  have hdescent : baseEnd_4742691 < baseStart_4742691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742721 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4742721 : Nat := 118140960795 + 4742721 * 2 ^ 59
def prefixEnd_4742721 : Nat := 4983230072969 + 3 ^ 40 * 4742721 * 2
def baseEnd_4742721 : Nat := 811765161057481271992043

theorem tailTrace_4742721 : CollatzResearch.WordTrace tailWord_4742721 prefixEnd_4742721 811765161057481271992043 := by
  unfold tailWord_4742721
  simp only [CollatzResearch.WordTrace]
  refine ⟨172981245850939284105132017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115320830567292856070088011 172981245850939284105132017)
  ·
    refine ⟨129735934388204463078849013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172981245850939284105132017 129735934388204463078849013)
    ·
      refine ⟨12162743848894168413642095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129735934388204463078849013 12162743848894168413642095)
      ·
        refine ⟨18244115773341252620463143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12162743848894168413642095 18244115773341252620463143)
        ·
          refine ⟨27366173660011878930694715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18244115773341252620463143 27366173660011878930694715)
          ·
            refine ⟨41049260490017818396042073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27366173660011878930694715 41049260490017818396042073)
            ·
              refine ⟨30786945367513363797031555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41049260490017818396042073 30786945367513363797031555)
              ·
                refine ⟨46180418051270045695547333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30786945367513363797031555 46180418051270045695547333)
                ·
                  refine ⟨8658828384613133567915125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46180418051270045695547333 8658828384613133567915125)
                  ·
                    refine ⟨811765161057481271992043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8658828384613133567915125 811765161057481271992043)
                    ·
                      rfl

theorem cell23_4742721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4742721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742721 prefixEnd_4742721 := by exact prefixLift 4742721
  have htrace : WordTrace (prefixWord ++ tailWord_4742721) baseStart_4742721 baseEnd_4742721 := by
    simpa [prefixWord, tailWord_4742721, baseEnd_4742721] using wordTrace_append hprefix tailTrace_4742721
  have hstable : (prefixWord ++ tailWord_4742721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742721).length < 2 ^ (prefixWord ++ tailWord_4742721).sum := by decide
  have hdescent : baseEnd_4742721 < baseStart_4742721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742761 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_4742761 : Nat := 118140960795 + 4742761 * 2 ^ 59
def prefixEnd_4742761 : Nat := 4983230072969 + 3 ^ 40 * 4742761 * 2
def baseEnd_4742761 : Nat := 2435316022398623659475945

theorem tailTrace_4742761 : CollatzResearch.WordTrace tailWord_4742761 prefixEnd_4742761 2435316022398623659475945 := by
  unfold tailWord_4742761
  simp only [CollatzResearch.WordTrace]
  refine ⟨172982704770794370936588137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115321803180529580624392091 172982704770794370936588137)
  ·
    refine ⟨129737028578095778202441103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172982704770794370936588137 129737028578095778202441103)
    ·
      refine ⟨194605542867143667303661655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129737028578095778202441103 194605542867143667303661655)
      ·
        refine ⟨291908314300715500955492483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194605542867143667303661655 291908314300715500955492483)
        ·
          refine ⟨437862471451073251433238725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291908314300715500955492483 437862471451073251433238725)
          ·
            refine ⟨82099213397076234643732261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 437862471451073251433238725 82099213397076234643732261)
            ·
              refine ⟨15393602511951793995699799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82099213397076234643732261 15393602511951793995699799)
              ·
                refine ⟨23090403767927690993549699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15393602511951793995699799 23090403767927690993549699)
                ·
                  refine ⟨34635605651891536490324549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23090403767927690993549699 34635605651891536490324549)
                  ·
                    refine ⟨6494176059729663091935853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34635605651891536490324549 6494176059729663091935853)
                    ·
                      refine ⟨2435316022398623659475945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494176059729663091935853 2435316022398623659475945)
                      ·
                        rfl

theorem cell23_4742761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_4742761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742761 prefixEnd_4742761 := by exact prefixLift 4742761
  have htrace : WordTrace (prefixWord ++ tailWord_4742761) baseStart_4742761 baseEnd_4742761 := by
    simpa [prefixWord, tailWord_4742761, baseEnd_4742761] using wordTrace_append hprefix tailTrace_4742761
  have hstable : (prefixWord ++ tailWord_4742761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742761).length < 2 ^ (prefixWord ++ tailWord_4742761).sum := by decide
  have hdescent : baseEnd_4742761 < baseStart_4742761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742781 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 8]
def baseStart_4742781 : Nat := 118140960795 + 4742781 * 2 ^ 59
def prefixEnd_4742781 : Nat := 4983230072969 + 3 ^ 40 * 4742781 * 2
def baseEnd_4742781 : Nat := 270591810223523731247317

theorem tailTrace_4742781 : CollatzResearch.WordTrace tailWord_4742781 prefixEnd_4742781 270591810223523731247317 := by
  unfold tailWord_4742781
  simp only [CollatzResearch.WordTrace]
  refine ⟨172983434230721914352316197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115322289487147942901544131 172983434230721914352316197)
  ·
    refine ⟨32434393918260358941059287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172983434230721914352316197 32434393918260358941059287)
    ·
      refine ⟨48651590877390538411588931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32434393918260358941059287 48651590877390538411588931)
      ·
        refine ⟨72977386316085807617383397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48651590877390538411588931 72977386316085807617383397)
        ·
          refine ⟨13683259934266088928259387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72977386316085807617383397 13683259934266088928259387)
          ·
            refine ⟨20524889901399133392389081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13683259934266088928259387 20524889901399133392389081)
            ·
              refine ⟨15393667426049350044291811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20524889901399133392389081 15393667426049350044291811)
              ·
                refine ⟨23090501139074025066437717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15393667426049350044291811 23090501139074025066437717)
                ·
                  refine ⟨270591810223523731247317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23090501139074025066437717 270591810223523731247317)
                  ·
                    rfl

theorem cell23_4742781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_4742781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742781 prefixEnd_4742781 := by exact prefixLift 4742781
  have htrace : WordTrace (prefixWord ++ tailWord_4742781) baseStart_4742781 baseEnd_4742781 := by
    simpa [prefixWord, tailWord_4742781, baseEnd_4742781] using wordTrace_append hprefix tailTrace_4742781
  have hstable : (prefixWord ++ tailWord_4742781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742781).length < 2 ^ (prefixWord ++ tailWord_4742781).sum := by decide
  have hdescent : baseEnd_4742781 < baseStart_4742781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742785 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 3, 4]
def baseStart_4742785 : Nat := 118140960795 + 4742785 * 2 ^ 59
def prefixEnd_4742785 : Nat := 4983230072969 + 3 ^ 40 * 4742785 * 2
def baseEnd_4742785 : Nat := 811776115311443855191945

theorem tailTrace_4742785 : CollatzResearch.WordTrace tailWord_4742785 prefixEnd_4742785 811776115311443855191945 := by
  unfold tailWord_4742785
  simp only [CollatzResearch.WordTrace]
  refine ⟨172983580122707423035461809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115322386748471615356974539 172983580122707423035461809)
  ·
    refine ⟨129737685092030567276596357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172983580122707423035461809 129737685092030567276596357)
    ·
      refine ⟨24325815954755731364361817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129737685092030567276596357 24325815954755731364361817)
      ·
        refine ⟨18244361966066798523271363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24325815954755731364361817 18244361966066798523271363)
        ·
          refine ⟨27366542949100197784907045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18244361966066798523271363 27366542949100197784907045)
          ·
            refine ⟨5131226802956287084670071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27366542949100197784907045 5131226802956287084670071)
            ·
              refine ⟨7696840204434430627005107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5131226802956287084670071 7696840204434430627005107)
              ·
                refine ⟨11545260306651645940507661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696840204434430627005107 11545260306651645940507661)
                ·
                  refine ⟨4329472614994367227690373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11545260306651645940507661 4329472614994367227690373)
                  ·
                    refine ⟨811776115311443855191945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329472614994367227690373 811776115311443855191945)
                    ·
                      rfl

theorem cell23_4742785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_4742785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742785 prefixEnd_4742785 := by exact prefixLift 4742785
  have htrace : WordTrace (prefixWord ++ tailWord_4742785) baseStart_4742785 baseEnd_4742785 := by
    simpa [prefixWord, tailWord_4742785, baseEnd_4742785] using wordTrace_append hprefix tailTrace_4742785
  have hstable : (prefixWord ++ tailWord_4742785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742785).length < 2 ^ (prefixWord ++ tailWord_4742785).sum := by decide
  have hdescent : baseEnd_4742785 < baseStart_4742785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742798 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_4742798 : Nat := 118140960795 + 4742798 * 2 ^ 59
def prefixEnd_4742798 : Nat := 4983230072969 + 3 ^ 40 * 4742798 * 2
def baseEnd_4742798 : Nat := 270592780131426668301475

theorem tailTrace_4742798 : CollatzResearch.WordTrace tailWord_4742798 prefixEnd_4742798 270592780131426668301475 := by
  unfold tailWord_4742798
  simp only [CollatzResearch.WordTrace]
  refine ⟨21623006783957540781960631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115322702847773550837123365 21623006783957540781960631)
  ·
    refine ⟨32434510175936311172940947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21623006783957540781960631 32434510175936311172940947)
    ·
      refine ⟨48651765263904466759411421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32434510175936311172940947 48651765263904466759411421)
      ·
        refine ⟨18244411973964175034779283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48651765263904466759411421 18244411973964175034779283)
        ·
          refine ⟨27366617960946262552168925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18244411973964175034779283 27366617960946262552168925)
          ·
            refine ⟨10262481735354848457063347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27366617960946262552168925 10262481735354848457063347)
            ·
              refine ⟨15393722603032272685595021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262481735354848457063347 15393722603032272685595021)
              ·
                refine ⟨5772645976137102257098133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15393722603032272685595021 5772645976137102257098133)
                ·
                  refine ⟨270592780131426668301475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5772645976137102257098133 270592780131426668301475)
                  ·
                    rfl

theorem cell23_4742798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_4742798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742798 prefixEnd_4742798 := by exact prefixLift 4742798
  have htrace : WordTrace (prefixWord ++ tailWord_4742798) baseStart_4742798 baseEnd_4742798 := by
    simpa [prefixWord, tailWord_4742798, baseEnd_4742798] using wordTrace_append hprefix tailTrace_4742798
  have hstable : (prefixWord ++ tailWord_4742798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742798).length < 2 ^ (prefixWord ++ tailWord_4742798).sum := by decide
  have hdescent : baseEnd_4742798 < baseStart_4742798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742842 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3]
def baseStart_4742842 : Nat := 118140960795 + 4742842 * 2 ^ 59
def prefixEnd_4742842 : Nat := 4983230072969 + 3 ^ 40 * 4742842 * 2
def baseEnd_4742842 : Nat := 2435357614331637842563073

theorem tailTrace_4742842 : CollatzResearch.WordTrace tailWord_4742842 prefixEnd_4742842 2435357614331637842563073 := by
  unfold tailWord_4742842
  simp only [CollatzResearch.WordTrace]
  refine ⟨43246414770875230442571695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115323772722333947846857853 43246414770875230442571695)
  ·
    refine ⟨64869622156312845663857543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43246414770875230442571695 64869622156312845663857543)
    ·
      refine ⟨97304433234469268495786315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64869622156312845663857543 97304433234469268495786315)
      ·
        refine ⟨145956649851703902743679473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97304433234469268495786315 145956649851703902743679473)
        ·
          refine ⟨109467487388777927057759605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145956649851703902743679473 109467487388777927057759605)
          ·
            refine ⟨10262576942697930661664963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109467487388777927057759605 10262576942697930661664963)
            ·
              refine ⟨15393865414046895992497445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262576942697930661664963 15393865414046895992497445)
              ·
                refine ⟨2886349765133792998593271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15393865414046895992497445 2886349765133792998593271)
                ·
                  refine ⟨4329524647700689497889907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886349765133792998593271 4329524647700689497889907)
                  ·
                    refine ⟨6494286971551034246834861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329524647700689497889907 6494286971551034246834861)
                    ·
                      refine ⟨2435357614331637842563073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494286971551034246834861 2435357614331637842563073)
                      ·
                        rfl

theorem cell23_4742842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_4742842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742842 prefixEnd_4742842 := by exact prefixLift 4742842
  have htrace : WordTrace (prefixWord ++ tailWord_4742842) baseStart_4742842 baseEnd_4742842 := by
    simpa [prefixWord, tailWord_4742842, baseEnd_4742842] using wordTrace_append hprefix tailTrace_4742842
  have hstable : (prefixWord ++ tailWord_4742842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742842).length < 2 ^ (prefixWord ++ tailWord_4742842).sum := by decide
  have hdescent : baseEnd_4742842 < baseStart_4742842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742865 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 5, 2, 2]
def baseStart_4742865 : Nat := 118140960795 + 4742865 * 2 ^ 59
def prefixEnd_4742865 : Nat := 4983230072969 + 3 ^ 40 * 4742865 * 2
def baseEnd_4742865 : Nat := 2435369424386691252575467

theorem tailTrace_4742865 : CollatzResearch.WordTrace tailWord_4742865 prefixEnd_4742865 2435369424386691252575467 := by
  unfold tailWord_4742865
  simp only [CollatzResearch.WordTrace]
  refine ⟨172986497962417596698374049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115324331974945064465582699 172986497962417596698374049)
  ·
    refine ⟨129739873471813197523780537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172986497962417596698374049 129739873471813197523780537)
    ·
      refine ⟨97304905103859898142835403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129739873471813197523780537 97304905103859898142835403)
      ·
        refine ⟨145957357655789847214253105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97304905103859898142835403 145957357655789847214253105)
        ·
          refine ⟨109468018241842385410689829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145957357655789847214253105 109468018241842385410689829)
          ·
            refine ⟨20525253420345447264504343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109468018241842385410689829 20525253420345447264504343)
            ·
              refine ⟨30787880130518170896756515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20525253420345447264504343 30787880130518170896756515)
              ·
                refine ⟨46181820195777256345134773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30787880130518170896756515 46181820195777256345134773)
                ·
                  refine ⟨4329545643354117782356385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46181820195777256345134773 4329545643354117782356385)
                  ·
                    refine ⟨3247159232515588336767289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4329545643354117782356385 3247159232515588336767289)
                    ·
                      refine ⟨2435369424386691252575467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247159232515588336767289 2435369424386691252575467)
                      ·
                        rfl

theorem cell23_4742865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_4742865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742865 prefixEnd_4742865 := by exact prefixLift 4742865
  have htrace : WordTrace (prefixWord ++ tailWord_4742865) baseStart_4742865 baseEnd_4742865 := by
    simpa [prefixWord, tailWord_4742865, baseEnd_4742865] using wordTrace_append hprefix tailTrace_4742865
  have hstable : (prefixWord ++ tailWord_4742865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742865).length < 2 ^ (prefixWord ++ tailWord_4742865).sum := by decide
  have hdescent : baseEnd_4742865 < baseStart_4742865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742876 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4742876 : Nat := 118140960795 + 4742876 * 2 ^ 59
def prefixEnd_4742876 : Nat := 4983230072969 + 3 ^ 40 * 4742876 * 2
def baseEnd_4742876 : Nat := 2435375072673890709537917

theorem tailTrace_4742876 : CollatzResearch.WordTrace tailWord_4742876 prefixEnd_4742876 2435375072673890709537917 := by
  unfold tailWord_4742876
  simp only [CollatzResearch.WordTrace]
  refine ⟨86493449582688872788512241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115324599443585163718016321 86493449582688872788512241)
  ·
    refine ⟨64870087187016654591384181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86493449582688872788512241 64870087187016654591384181)
    ·
      refine ⟨6081570673782811367942267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64870087187016654591384181 6081570673782811367942267)
      ·
        refine ⟨9122356010674217051913401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081570673782811367942267 9122356010674217051913401)
        ·
          refine ⟨6841767008005662788935051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9122356010674217051913401 6841767008005662788935051)
          ·
            refine ⟨10262650512008494183402577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6841767008005662788935051 10262650512008494183402577)
            ·
              refine ⟨7696987884006370637551933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10262650512008494183402577 7696987884006370637551933)
              ·
                refine ⟨2886370456502388989081975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7696987884006370637551933 2886370456502388989081975)
                ·
                  refine ⟨4329555684753583483622963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886370456502388989081975 4329555684753583483622963)
                  ·
                    refine ⟨6494333527130375225434445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329555684753583483622963 6494333527130375225434445)
                    ·
                      refine ⟨2435375072673890709537917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494333527130375225434445 2435375072673890709537917)
                      ·
                        rfl

theorem cell23_4742876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4742876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742876 prefixEnd_4742876 := by exact prefixLift 4742876
  have htrace : WordTrace (prefixWord ++ tailWord_4742876) baseStart_4742876 baseEnd_4742876 := by
    simpa [prefixWord, tailWord_4742876, baseEnd_4742876] using wordTrace_append hprefix tailTrace_4742876
  have hstable : (prefixWord ++ tailWord_4742876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742876).length < 2 ^ (prefixWord ++ tailWord_4742876).sum := by decide
  have hdescent : baseEnd_4742876 < baseStart_4742876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742885 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_4742885 : Nat := 118140960795 + 4742885 * 2 ^ 59
def prefixEnd_4742885 : Nat := 4983230072969 + 3 ^ 40 * 4742885 * 2
def baseEnd_4742885 : Nat := 2435379693999781174325375

theorem tailTrace_4742885 : CollatzResearch.WordTrace tailWord_4742885 prefixEnd_4742885 2435379693999781174325375 := by
  unfold tailWord_4742885
  simp only [CollatzResearch.WordTrace]
  refine ⟨172987227422345140114102109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115324818281563426742734739 172987227422345140114102109)
  ·
    refine ⟨64870210283379427542788291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172987227422345140114102109 64870210283379427542788291)
    ·
      refine ⟨97305315425069141314182437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64870210283379427542788291 97305315425069141314182437)
      ·
        refine ⟨18244746642200463996409207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97305315425069141314182437 18244746642200463996409207)
        ·
          refine ⟨27367119963300695994613811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18244746642200463996409207 27367119963300695994613811)
          ·
            refine ⟨41050679944951043991920717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27367119963300695994613811 41050679944951043991920717)
            ·
              refine ⟨15394004979356641496970269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41050679944951043991920717 15394004979356641496970269)
              ·
                refine ⟨5772751867258740561363851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15394004979356641496970269 5772751867258740561363851)
                ·
                  refine ⟨8659127800888110842045777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5772751867258740561363851 8659127800888110842045777)
                  ·
                    refine ⟨6494345850666083131534333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8659127800888110842045777 6494345850666083131534333)
                    ·
                      refine ⟨2435379693999781174325375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494345850666083131534333 2435379693999781174325375)
                      ·
                        rfl

theorem cell23_4742885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_4742885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742885 prefixEnd_4742885 := by exact prefixLift 4742885
  have htrace : WordTrace (prefixWord ++ tailWord_4742885) baseStart_4742885 baseEnd_4742885 := by
    simpa [prefixWord, tailWord_4742885, baseEnd_4742885] using wordTrace_append hprefix tailTrace_4742885
  have hstable : (prefixWord ++ tailWord_4742885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742885).length < 2 ^ (prefixWord ++ tailWord_4742885).sum := by decide
  have hdescent : baseEnd_4742885 < baseStart_4742885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742915 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 3]
def baseStart_4742915 : Nat := 118140960795 + 4742915 * 2 ^ 59
def prefixEnd_4742915 : Nat := 4983230072969 + 3 ^ 40 * 4742915 * 2
def baseEnd_4742915 : Nat := 2435395098419416056950237

theorem tailTrace_4742915 : CollatzResearch.WordTrace tailWord_4742915 prefixEnd_4742915 2435395098419416056950237 := by
  unfold tailWord_4742915
  simp only [CollatzResearch.WordTrace]
  refine ⟨172988321612236455237694199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115325547741490970158462799 172988321612236455237694199)
  ·
    refine ⟨259482482418354682856541299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172988321612236455237694199 259482482418354682856541299)
    ·
      refine ⟨389223723627532024284811949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259482482418354682856541299 389223723627532024284811949)
      ·
        refine ⟨145958896360324509106804481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389223723627532024284811949 145958896360324509106804481)
        ·
          refine ⟨109469172270243381830103361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145958896360324509106804481 109469172270243381830103361)
          ·
            refine ⟨82101879202682536372577521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109469172270243381830103361 82101879202682536372577521)
            ·
              refine ⟨61576409402011902279433141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82101879202682536372577521 61576409402011902279433141)
              ·
                refine ⟨5772788381438615838696857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61576409402011902279433141 5772788381438615838696857)
                ·
                  refine ⟨4329591286078961879022643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5772788381438615838696857 4329591286078961879022643)
                  ·
                    refine ⟨6494386929118442818533965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329591286078961879022643 6494386929118442818533965)
                    ·
                      refine ⟨2435395098419416056950237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494386929118442818533965 2435395098419416056950237)
                      ·
                        rfl

theorem cell23_4742915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_4742915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742915 prefixEnd_4742915 := by exact prefixLift 4742915
  have htrace : WordTrace (prefixWord ++ tailWord_4742915) baseStart_4742915 baseEnd_4742915 := by
    simpa [prefixWord, tailWord_4742915, baseEnd_4742915] using wordTrace_append hprefix tailTrace_4742915
  have hstable : (prefixWord ++ tailWord_4742915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742915).length < 2 ^ (prefixWord ++ tailWord_4742915).sum := by decide
  have hdescent : baseEnd_4742915 < baseStart_4742915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742931 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 4, 6]
def baseStart_4742931 : Nat := 118140960795 + 4742931 * 2 ^ 59
def prefixEnd_4742931 : Nat := 4983230072969 + 3 ^ 40 * 4742931 * 2
def baseEnd_4742931 : Nat := 811801104703295998116721

theorem tailTrace_4742931 : CollatzResearch.WordTrace tailWord_4742931 prefixEnd_4742931 811801104703295998116721 := by
  unfold tailWord_4742931
  simp only [CollatzResearch.WordTrace]
  refine ⟨172988905180178489970276647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115325936786785659980184431 172988905180178489970276647)
  ·
    refine ⟨259483357770267734955414971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172988905180178489970276647 259483357770267734955414971)
    ·
      refine ⟨389225036655401602433122457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259483357770267734955414971 389225036655401602433122457)
      ·
        refine ⟨291918777491551201824841843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389225036655401602433122457 291918777491551201824841843)
        ·
          refine ⟨437878166237326802737262765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291918777491551201824841843 437878166237326802737262765)
          ·
            refine ⟨164204312338997551026473537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 437878166237326802737262765 164204312338997551026473537)
            ·
              refine ⟨123153234254248163269855153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164204312338997551026473537 123153234254248163269855153)
              ·
                refine ⟨92364925690686122452391365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123153234254248163269855153 92364925690686122452391365)
                ·
                  refine ⟨17318423567003647959823381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92364925690686122452391365 17318423567003647959823381)
                  ·
                    refine ⟨811801104703295998116721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17318423567003647959823381 811801104703295998116721)
                    ·
                      rfl

theorem cell23_4742931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 6].length) (baseStart_4742931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742931 prefixEnd_4742931 := by exact prefixLift 4742931
  have htrace : WordTrace (prefixWord ++ tailWord_4742931) baseStart_4742931 baseEnd_4742931 := by
    simpa [prefixWord, tailWord_4742931, baseEnd_4742931] using wordTrace_append hprefix tailTrace_4742931
  have hstable : (prefixWord ++ tailWord_4742931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742931).length < 2 ^ (prefixWord ++ tailWord_4742931).sum := by decide
  have hdescent : baseEnd_4742931 < baseStart_4742931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742955 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 8, 2, 2]
def baseStart_4742955 : Nat := 118140960795 + 4742955 * 2 ^ 59
def prefixEnd_4742955 : Nat := 4983230072969 + 3 ^ 40 * 4742955 * 2
def baseEnd_4742955 : Nat := 2435415637645595900450053

theorem tailTrace_4742955 : CollatzResearch.WordTrace tailWord_4742955 prefixEnd_4742955 2435415637645595900450053 := by
  unfold tailWord_4742955
  simp only [CollatzResearch.WordTrace]
  refine ⟨172989780532091542069150319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115326520354727694712766879 172989780532091542069150319)
  ·
    refine ⟨259484670798137313103725479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172989780532091542069150319 259484670798137313103725479)
    ·
      refine ⟨389227006197205969655588219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259484670798137313103725479 389227006197205969655588219)
      ·
        refine ⟨583840509295808954483382329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389227006197205969655588219 583840509295808954483382329)
        ·
          refine ⟨437880381971856715862536747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583840509295808954483382329 437880381971856715862536747)
          ·
            refine ⟨656820572957785073793805121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437880381971856715862536747 656820572957785073793805121)
            ·
              refine ⟨492615429718338805345353841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656820572957785073793805121 492615429718338805345353841)
              ·
                refine ⟨369461572288754104009015381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492615429718338805345353841 369461572288754104009015381)
                ·
                  refine ⟨4329627800258837156355649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 369461572288754104009015381 4329627800258837156355649)
                  ·
                    refine ⟨3247220850194127867266737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4329627800258837156355649 3247220850194127867266737)
                    ·
                      refine ⟨2435415637645595900450053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247220850194127867266737 2435415637645595900450053)
                      ·
                        rfl

theorem cell23_4742955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 2, 2].length) (baseStart_4742955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742955 prefixEnd_4742955 := by exact prefixLift 4742955
  have htrace : WordTrace (prefixWord ++ tailWord_4742955) baseStart_4742955 baseEnd_4742955 := by
    simpa [prefixWord, tailWord_4742955, baseEnd_4742955] using wordTrace_append hprefix tailTrace_4742955
  have hstable : (prefixWord ++ tailWord_4742955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742955).length < 2 ^ (prefixWord ++ tailWord_4742955).sum := by decide
  have hdescent : baseEnd_4742955 < baseStart_4742955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742966 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4742966 : Nat := 118140960795 + 4742966 * 2 ^ 59
def prefixEnd_4742966 : Nat := 4983230072969 + 3 ^ 40 * 4742966 * 2
def baseEnd_4742966 : Nat := 2435421285932795357412503

theorem tailTrace_4742966 : CollatzResearch.WordTrace tailWord_4742966 prefixEnd_4742966 2435421285932795357412503 := by
  unfold tailWord_4742966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811886358440730684237547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115326787823367793965200501 10811886358440730684237547)
  ·
    refine ⟨16217829537661096026356321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811886358440730684237547 16217829537661096026356321)
    ·
      refine ⟨12163372153245822019767241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16217829537661096026356321 12163372153245822019767241)
      ·
        refine ⟨9122529114934366514825431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12163372153245822019767241 9122529114934366514825431)
        ·
          refine ⟨13683793672401549772238147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122529114934366514825431 13683793672401549772238147)
          ·
            refine ⟨20525690508602324658357221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13683793672401549772238147 20525690508602324658357221)
            ·
              refine ⟨3848566970362935873441979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20525690508602324658357221 3848566970362935873441979)
              ·
                refine ⟨5772850455544403810162969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848566970362935873441979 5772850455544403810162969)
                ·
                  refine ⟨4329637841658302857622227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5772850455544403810162969 4329637841658302857622227)
                  ·
                    refine ⟨6494456762487454286433341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329637841658302857622227 6494456762487454286433341)
                    ·
                      refine ⟨2435421285932795357412503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494456762487454286433341 2435421285932795357412503)
                      ·
                        rfl

theorem cell23_4742966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4742966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742966 prefixEnd_4742966 := by exact prefixLift 4742966
  have htrace : WordTrace (prefixWord ++ tailWord_4742966) baseStart_4742966 baseEnd_4742966 := by
    simpa [prefixWord, tailWord_4742966, baseEnd_4742966] using wordTrace_append hprefix tailTrace_4742966
  have hstable : (prefixWord ++ tailWord_4742966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742966).length < 2 ^ (prefixWord ++ tailWord_4742966).sum := by decide
  have hdescent : baseEnd_4742966 < baseStart_4742966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4742989 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_4742989 : Nat := 118140960795 + 4742989 * 2 ^ 59
def prefixEnd_4742989 : Nat := 4983230072969 + 3 ^ 40 * 4742989 * 2
def baseEnd_4742989 : Nat := 2435433095987848767424897

theorem tailTrace_4742989 : CollatzResearch.WordTrace tailWord_4742989 prefixEnd_4742989 2435433095987848767424897 := by
  unfold tailWord_4742989
  simp only [CollatzResearch.WordTrace]
  refine ⟨172991020613968365875888021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115327347075978910583925347 172991020613968365875888021)
  ·
    refine ⟨8108954091279767150432251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172991020613968365875888021 8108954091279767150432251)
    ·
      refine ⟨12163431136919650725648377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8108954091279767150432251 12163431136919650725648377)
      ·
        refine ⟨9122573352689738044236283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12163431136919650725648377 9122573352689738044236283)
        ·
          refine ⟨13683860029034607066354425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122573352689738044236283 13683860029034607066354425)
          ·
            refine ⟨10262895021775955299765819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13683860029034607066354425 10262895021775955299765819)
            ·
              refine ⟨15394342532663932949648729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262895021775955299765819 15394342532663932949648729)
              ·
                refine ⟨11545756899497949712236547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15394342532663932949648729 11545756899497949712236547)
                ·
                  refine ⟨17318635349246924568354821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11545756899497949712236547 17318635349246924568354821)
                  ·
                    refine ⟨3247244127983798356566529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17318635349246924568354821 3247244127983798356566529)
                    ·
                      refine ⟨2435433095987848767424897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247244127983798356566529 2435433095987848767424897)
                      ·
                        rfl

theorem cell23_4742989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_4742989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4742989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4742989 prefixEnd_4742989 := by exact prefixLift 4742989
  have htrace : WordTrace (prefixWord ++ tailWord_4742989) baseStart_4742989 baseEnd_4742989 := by
    simpa [prefixWord, tailWord_4742989, baseEnd_4742989] using wordTrace_append hprefix tailTrace_4742989
  have hstable : (prefixWord ++ tailWord_4742989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4742989).length < 2 ^ (prefixWord ++ tailWord_4742989).sum := by decide
  have hdescent : baseEnd_4742989 < baseStart_4742989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4742989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743012 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 5]
def baseStart_4743012 : Nat := 118140960795 + 4743012 * 2 ^ 59
def prefixEnd_4743012 : Nat := 4983230072969 + 3 ^ 40 * 4743012 * 2
def baseEnd_4743012 : Nat := 270604989560322464159699

theorem tailTrace_4743012 : CollatzResearch.WordTrace tailWord_4743012 prefixEnd_4743012 270604989560322464159699 := by
  unfold tailWord_4743012
  simp only [CollatzResearch.WordTrace]
  refine ⟨86495929746442520401987645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115327906328590027202650193 86495929746442520401987645)
  ·
    refine ⟨32435973654915945150745367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86495929746442520401987645 32435973654915945150745367)
    ·
      refine ⟨48653960482373917726118051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32435973654915945150745367 48653960482373917726118051)
      ·
        refine ⟨72980940723560876589177077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48653960482373917726118051 72980940723560876589177077)
        ·
          refine ⟨6841963192833832180235351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72980940723560876589177077 6841963192833832180235351)
          ·
            refine ⟨10262944789250748270353027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6841963192833832180235351 10262944789250748270353027)
            ·
              refine ⟨15394417183876122405529541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262944789250748270353027 15394417183876122405529541)
              ·
                refine ⟨2886453221976772951036789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15394417183876122405529541 2886453221976772951036789)
                ·
                  refine ⟨270604989560322464159699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2886453221976772951036789 270604989560322464159699)
                  ·
                    rfl

theorem cell23_4743012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_4743012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743012 prefixEnd_4743012 := by exact prefixLift 4743012
  have htrace : WordTrace (prefixWord ++ tailWord_4743012) baseStart_4743012 baseEnd_4743012 := by
    simpa [prefixWord, tailWord_4743012, baseEnd_4743012] using wordTrace_append hprefix tailTrace_4743012
  have hstable : (prefixWord ++ tailWord_4743012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743012).length < 2 ^ (prefixWord ++ tailWord_4743012).sum := by decide
  have hdescent : baseEnd_4743012 < baseStart_4743012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743015 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_4743015 : Nat := 118140960795 + 4743015 * 2 ^ 59
def prefixEnd_4743015 : Nat := 4983230072969 + 3 ^ 40 * 4743015 * 2
def baseEnd_4743015 : Nat := 2435446446484865665699777

theorem tailTrace_4743015 : CollatzResearch.WordTrace tailWord_4743015 prefixEnd_4743015 2435446446484865665699777 := by
  unfold tailWord_4743015
  simp only [CollatzResearch.WordTrace]
  refine ⟨172991968911874172316334499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115327979274582781544222999 172991968911874172316334499)
  ·
    refine ⟨259487953367811258474501749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172991968911874172316334499 259487953367811258474501749)
    ·
      refine ⟨24326995628232305481984539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259487953367811258474501749 24326995628232305481984539)
      ·
        refine ⟨36490493442348458222976809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24326995628232305481984539 36490493442348458222976809)
        ·
          refine ⟨27367870081761343667232607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36490493442348458222976809 27367870081761343667232607)
          ·
            refine ⟨41051805122642015500848911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27367870081761343667232607 41051805122642015500848911)
            ·
              refine ⟨61577707683963023251273367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41051805122642015500848911 61577707683963023251273367)
              ·
                refine ⟨92366561525944534876910051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61577707683963023251273367 92366561525944534876910051)
                ·
                  refine ⟨138549842288916802315365077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92366561525944534876910051 138549842288916802315365077)
                  ·
                    refine ⟨3247261928646487554266369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138549842288916802315365077 3247261928646487554266369)
                    ·
                      refine ⟨2435446446484865665699777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247261928646487554266369 2435446446484865665699777)
                      ·
                        rfl

theorem cell23_4743015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_4743015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743015 prefixEnd_4743015 := by exact prefixLift 4743015
  have htrace : WordTrace (prefixWord ++ tailWord_4743015) baseStart_4743015 baseEnd_4743015 := by
    simpa [prefixWord, tailWord_4743015, baseEnd_4743015] using wordTrace_append hprefix tailTrace_4743015
  have hstable : (prefixWord ++ tailWord_4743015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743015).length < 2 ^ (prefixWord ++ tailWord_4743015).sum := by decide
  have hdescent : baseEnd_4743015 < baseStart_4743015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743022 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4743022 : Nat := 118140960795 + 4743022 * 2 ^ 59
def prefixEnd_4743022 : Nat := 4983230072969 + 3 ^ 40 * 4743022 * 2
def baseEnd_4743022 : Nat := 2435450040849447138312245

theorem tailTrace_4743022 : CollatzResearch.WordTrace tailWord_4743022 prefixEnd_4743022 2435450040849447138312245 := by
  unfold tailWord_4743022
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624028027856101563979915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115328149481899208341226213 21624028027856101563979915)
  ·
    refine ⟨32436042041784152345969873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21624028027856101563979915 32436042041784152345969873)
    ·
      refine ⟨24327031531338114259477405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32436042041784152345969873 24327031531338114259477405)
      ·
        refine ⟨9122636824251792847304027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24327031531338114259477405 9122636824251792847304027)
        ·
          refine ⟨13683955236377689270956041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122636824251792847304027 13683955236377689270956041)
          ·
            refine ⟨10262966427283266953217031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13683955236377689270956041 10262966427283266953217031)
            ·
              refine ⟨15394449640924900429825547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262966427283266953217031 15394449640924900429825547)
              ·
                refine ⟨23091674461387350644738321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15394449640924900429825547 23091674461387350644738321)
                ·
                  refine ⟨17318755846040512983553741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23091674461387350644738321 17318755846040512983553741)
                  ·
                    refine ⟨6494533442265192368832653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17318755846040512983553741 6494533442265192368832653)
                    ·
                      refine ⟨2435450040849447138312245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494533442265192368832653 2435450040849447138312245)
                      ·
                        rfl

theorem cell23_4743022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4743022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743022 prefixEnd_4743022 := by exact prefixLift 4743022
  have htrace : WordTrace (prefixWord ++ tailWord_4743022) baseStart_4743022 baseEnd_4743022 := by
    simpa [prefixWord, tailWord_4743022, baseEnd_4743022] using wordTrace_append hprefix tailTrace_4743022
  have hstable : (prefixWord ++ tailWord_4743022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743022).length < 2 ^ (prefixWord ++ tailWord_4743022).sum := by decide
  have hdescent : baseEnd_4743022 < baseStart_4743022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743045 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 6, 2]
def baseStart_4743045 : Nat := 118140960795 + 4743045 * 2 ^ 59
def prefixEnd_4743045 : Nat := 4983230072969 + 3 ^ 40 * 4743045 * 2
def baseEnd_4743045 : Nat := 2435461850904500548324639

theorem tailTrace_4743045 : CollatzResearch.WordTrace tailWord_4743045 prefixEnd_4743045 2435461850904500548324639 := by
  unfold tailWord_4743045
  simp only [CollatzResearch.WordTrace]
  refine ⟨172993063101765487439926589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115328708734510324959951059 172993063101765487439926589)
  ·
    refine ⟨64872398663162057789972471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172993063101765487439926589 64872398663162057789972471)
    ·
      refine ⟨97308597994743086684958707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64872398663162057789972471 97308597994743086684958707)
      ·
        refine ⟨145962896992114630027438061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97308597994743086684958707 145962896992114630027438061)
        ·
          refine ⟨54736086372042986260289273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145962896992114630027438061 54736086372042986260289273)
          ·
            refine ⟨41052064779032239695216955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54736086372042986260289273 41052064779032239695216955)
            ·
              refine ⟨61578097168548359542825433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41052064779032239695216955 61578097168548359542825433)
              ·
                refine ⟨46183572876411269657119075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61578097168548359542825433 46183572876411269657119075)
                ·
                  refine ⟨69275359314616904485678613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46183572876411269657119075 69275359314616904485678613)
                  ·
                    refine ⟨3247282467872667397766185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69275359314616904485678613 3247282467872667397766185)
                    ·
                      refine ⟨2435461850904500548324639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247282467872667397766185 2435461850904500548324639)
                      ·
                        rfl

theorem cell23_4743045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_4743045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743045 prefixEnd_4743045 := by exact prefixLift 4743045
  have htrace : WordTrace (prefixWord ++ tailWord_4743045) baseStart_4743045 baseEnd_4743045 := by
    simpa [prefixWord, tailWord_4743045, baseEnd_4743045] using wordTrace_append hprefix tailTrace_4743045
  have hstable : (prefixWord ++ tailWord_4743045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743045).length < 2 ^ (prefixWord ++ tailWord_4743045).sum := by decide
  have hdescent : baseEnd_4743045 < baseStart_4743045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743065 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_4743065 : Nat := 118140960795 + 4743065 * 2 ^ 59
def prefixEnd_4743065 : Nat := 4983230072969 + 3 ^ 40 * 4743065 * 2
def baseEnd_4743065 : Nat := 2435472120517590470074547

theorem tailTrace_4743065 : CollatzResearch.WordTrace tailWord_4743065 prefixEnd_4743065 2435472120517590470074547 := by
  unfold tailWord_4743065
  simp only [CollatzResearch.WordTrace]
  refine ⟨172993792561693030855654649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115329195041128687237103099 172993792561693030855654649)
  ·
    refine ⟨129745344421269773141740987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172993792561693030855654649 129745344421269773141740987)
    ·
      refine ⟨194618016631904659712611481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129745344421269773141740987 194618016631904659712611481)
      ·
        refine ⟨145963512473928494784458611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194618016631904659712611481 145963512473928494784458611)
        ·
          refine ⟨218945268710892742176687917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145963512473928494784458611 218945268710892742176687917)
          ·
            refine ⟨82104475766584778316257969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218945268710892742176687917 82104475766584778316257969)
            ·
              refine ⟨61578356824938583737193477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82104475766584778316257969 61578356824938583737193477)
              ·
                refine ⟨11545941904675984450723777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61578356824938583737193477 11545941904675984450723777)
                ·
                  refine ⟨8659456428506988338042833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11545941904675984450723777 8659456428506988338042833)
                  ·
                    refine ⟨6494592321380241253532125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8659456428506988338042833 6494592321380241253532125)
                    ·
                      refine ⟨2435472120517590470074547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6494592321380241253532125 2435472120517590470074547)
                      ·
                        rfl

theorem cell23_4743065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_4743065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743065 prefixEnd_4743065 := by exact prefixLift 4743065
  have htrace : WordTrace (prefixWord ++ tailWord_4743065) baseStart_4743065 baseEnd_4743065 := by
    simpa [prefixWord, tailWord_4743065, baseEnd_4743065] using wordTrace_append hprefix tailTrace_4743065
  have hstable : (prefixWord ++ tailWord_4743065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743065).length < 2 ^ (prefixWord ++ tailWord_4743065).sum := by decide
  have hdescent : baseEnd_4743065 < baseStart_4743065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743115 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 1, 5]
def baseStart_4743115 : Nat := 118140960795 + 4743115 * 2 ^ 59
def prefixEnd_4743115 : Nat := 4983230072969 + 3 ^ 40 * 4743115 * 2
def baseEnd_4743115 : Nat := 811832598183438424816439

theorem tailTrace_4743115 : CollatzResearch.WordTrace tailWord_4743115 prefixEnd_4743115 811832598183438424816439 := by
  unfold tailWord_4743115
  simp only [CollatzResearch.WordTrace]
  refine ⟨172995616211511889394974799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115330410807674592929983199 172995616211511889394974799)
  ·
    refine ⟨259493424317267834092462199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172995616211511889394974799 259493424317267834092462199)
    ·
      refine ⟨389240136475901751138693299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259493424317267834092462199 389240136475901751138693299)
      ·
        refine ⟨583860204713852626708039949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389240136475901751138693299 583860204713852626708039949)
        ·
          refine ⟨218947576767694735015514981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 583860204713852626708039949 218947576767694735015514981)
          ·
            refine ⟨41052670643942762815409059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218947576767694735015514981 41052670643942762815409059)
            ·
              refine ⟨61579005965914144223113589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41052670643942762815409059 61579005965914144223113589)
              ·
                refine ⟨5773031809304451020916899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61579005965914144223113589 5773031809304451020916899)
                ·
                  refine ⟨8659547713956676531375349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773031809304451020916899 8659547713956676531375349)
                  ·
                    refine ⟨811832598183438424816439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8659547713956676531375349 811832598183438424816439)
                    ·
                      rfl

theorem cell23_4743115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 5].length) (baseStart_4743115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743115 prefixEnd_4743115 := by exact prefixLift 4743115
  have htrace : WordTrace (prefixWord ++ tailWord_4743115) baseStart_4743115 baseEnd_4743115 := by
    simpa [prefixWord, tailWord_4743115, baseEnd_4743115] using wordTrace_append hprefix tailTrace_4743115
  have hstable : (prefixWord ++ tailWord_4743115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743115).length < 2 ^ (prefixWord ++ tailWord_4743115).sum := by decide
  have hdescent : baseEnd_4743115 < baseStart_4743115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743149 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_4743149 : Nat := 118140960795 + 4743149 * 2 ^ 59
def prefixEnd_4743149 : Nat := 4983230072969 + 3 ^ 40 * 4743149 * 2
def baseEnd_4743149 : Nat := 811838417630856047141387

theorem tailTrace_4743149 : CollatzResearch.WordTrace tailWord_4743149 prefixEnd_4743149 811838417630856047141387 := by
  unfold tailWord_4743149
  simp only [CollatzResearch.WordTrace]
  refine ⟨172996856293388713201712501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115331237528925808801141667 172996856293388713201712501)
  ·
    refine ⟨16218455277505191862660547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172996856293388713201712501 16218455277505191862660547)
    ·
      refine ⟨24327682916257787793990821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16218455277505191862660547 24327682916257787793990821)
      ·
        refine ⟨4561440546798335211373279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24327682916257787793990821 4561440546798335211373279)
        ·
          refine ⟨6842160820197502817059919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561440546798335211373279 6842160820197502817059919)
          ·
            refine ⟨10263241230296254225589879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842160820197502817059919 10263241230296254225589879)
            ·
              refine ⟨15394861845444381338384819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10263241230296254225589879 15394861845444381338384819)
              ·
                refine ⟨23092292768166572007577229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15394861845444381338384819 23092292768166572007577229)
                ·
                  refine ⟨8659609788062464502841461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23092292768166572007577229 8659609788062464502841461)
                  ·
                    refine ⟨811838417630856047141387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8659609788062464502841461 811838417630856047141387)
                    ·
                      rfl

theorem cell23_4743149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_4743149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743149 prefixEnd_4743149 := by exact prefixLift 4743149
  have htrace : WordTrace (prefixWord ++ tailWord_4743149) baseStart_4743149 baseEnd_4743149 := by
    simpa [prefixWord, tailWord_4743149, baseEnd_4743149] using wordTrace_append hprefix tailTrace_4743149
  have hstable : (prefixWord ++ tailWord_4743149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743149).length < 2 ^ (prefixWord ++ tailWord_4743149).sum := by decide
  have hdescent : baseEnd_4743149 < baseStart_4743149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743152 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4]
def baseStart_4743152 : Nat := 118140960795 + 4743152 * 2 ^ 59
def prefixEnd_4743152 : Nat := 4983230072969 + 3 ^ 40 * 4743152 * 2
def baseEnd_4743152 : Nat := 2435516793334531629686647

theorem tailTrace_4743152 : CollatzResearch.WordTrace tailWord_4743152 prefixEnd_4743152 2435516793334531629686647 := by
  unfold tailWord_4743152
  simp only [CollatzResearch.WordTrace]
  refine ⟨86498482856188922357035855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115331310474918563142714473 86498482856188922357035855)
  ·
    refine ⟨129747724284283383535553783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86498482856188922357035855 129747724284283383535553783)
    ·
      refine ⟨194621586426425075303330675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129747724284283383535553783 194621586426425075303330675)
      ·
        refine ⟨291932379639637612954996013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194621586426425075303330675 291932379639637612954996013)
        ·
          refine ⟨109474642364864104858123505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291932379639637612954996013 109474642364864104858123505)
          ·
            refine ⟨82105981773648078643592629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109474642364864104858123505 82105981773648078643592629)
            ·
              refine ⟨7697435791279507372836809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82105981773648078643592629 7697435791279507372836809)
              ·
                refine ⟨5773076843459630529627607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7697435791279507372836809 5773076843459630529627607)
                ·
                  refine ⟨8659615265189445794441411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773076843459630529627607 8659615265189445794441411)
                  ·
                    refine ⟨12989422897784168691662117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8659615265189445794441411 12989422897784168691662117)
                    ·
                      refine ⟨2435516793334531629686647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12989422897784168691662117 2435516793334531629686647)
                      ·
                        rfl

theorem cell23_4743152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_4743152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743152 prefixEnd_4743152 := by exact prefixLift 4743152
  have htrace : WordTrace (prefixWord ++ tailWord_4743152) baseStart_4743152 baseEnd_4743152 := by
    simpa [prefixWord, tailWord_4743152, baseEnd_4743152] using wordTrace_append hprefix tailTrace_4743152
  have hstable : (prefixWord ++ tailWord_4743152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743152).length < 2 ^ (prefixWord ++ tailWord_4743152).sum := by decide
  have hdescent : baseEnd_4743152 < baseStart_4743152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743165 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4743165 : Nat := 118140960795 + 4743165 * 2 ^ 59
def prefixEnd_4743165 : Nat := 4983230072969 + 3 ^ 40 * 4743165 * 2
def baseEnd_4743165 : Nat := 2435523468583040078824087

theorem tailTrace_4743165 : CollatzResearch.WordTrace tailWord_4743165 prefixEnd_4743165 2435523468583040078824087 := by
  unfold tailWord_4743165
  simp only [CollatzResearch.WordTrace]
  refine ⟨172997439861330747934294949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115331626574220498622863299 172997439861330747934294949)
  ·
    refine ⟨32437019973999515237680303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172997439861330747934294949 32437019973999515237680303)
    ·
      refine ⟨48655529960999272856520455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32437019973999515237680303 48655529960999272856520455)
      ·
        refine ⟨72983294941498909284780683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48655529960999272856520455 72983294941498909284780683)
        ·
          refine ⟨109474942412248363927171025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72983294941498909284780683 109474942412248363927171025)
          ·
            refine ⟨82106206809186272945378269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109474942412248363927171025 82106206809186272945378269)
            ·
              refine ⟨30789827553444852354516851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82106206809186272945378269 30789827553444852354516851)
              ·
                refine ⟨46184741330167278531775277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30789827553444852354516851 46184741330167278531775277)
                ·
                  refine ⟨17319277998812729449415729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46184741330167278531775277 17319277998812729449415729)
                  ·
                    refine ⟨12989458499109547087061797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17319277998812729449415729 12989458499109547087061797)
                    ·
                      refine ⟨2435523468583040078824087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12989458499109547087061797 2435523468583040078824087)
                      ·
                        rfl

theorem cell23_4743165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4743165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743165 prefixEnd_4743165 := by exact prefixLift 4743165
  have htrace : WordTrace (prefixWord ++ tailWord_4743165) baseStart_4743165 baseEnd_4743165 := by
    simpa [prefixWord, tailWord_4743165, baseEnd_4743165] using wordTrace_append hprefix tailTrace_4743165
  have hstable : (prefixWord ++ tailWord_4743165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743165).length < 2 ^ (prefixWord ++ tailWord_4743165).sum := by decide
  have hdescent : baseEnd_4743165 < baseStart_4743165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743166 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4743166 : Nat := 118140960795 + 4743166 * 2 ^ 59
def prefixEnd_4743166 : Nat := 4983230072969 + 3 ^ 40 * 4743166 * 2
def baseEnd_4743166 : Nat := 811841327354564858303861

theorem tailTrace_4743166 : CollatzResearch.WordTrace tailWord_4743166 prefixEnd_4743166 811841327354564858303861 := by
  unfold tailWord_4743166
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624684541790890638135169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115331650889551416736720901 21624684541790890638135169)
  ·
    refine ⟨16218513406343167978601377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21624684541790890638135169 16218513406343167978601377)
    ·
      refine ⟨12163885054757375983951033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16218513406343167978601377 12163885054757375983951033)
      ·
        refine ⟨9122913791068031987963275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12163885054757375983951033 9122913791068031987963275)
        ·
          refine ⟨13684370686602047981944913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122913791068031987963275 13684370686602047981944913)
          ·
            refine ⟨10263278014951535986458685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13684370686602047981944913 10263278014951535986458685)
            ·
              refine ⟨3848729255606825994922007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10263278014951535986458685 3848729255606825994922007)
              ·
                refine ⟨5773093883410238992383011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848729255606825994922007 5773093883410238992383011)
                ·
                  refine ⟨8659640825115358488574517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773093883410238992383011 8659640825115358488574517)
                  ·
                    refine ⟨811841327354564858303861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8659640825115358488574517 811841327354564858303861)
                    ·
                      rfl

theorem cell23_4743166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4743166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743166 prefixEnd_4743166 := by exact prefixLift 4743166
  have htrace : WordTrace (prefixWord ++ tailWord_4743166) baseStart_4743166 baseEnd_4743166 := by
    simpa [prefixWord, tailWord_4743166, baseEnd_4743166] using wordTrace_append hprefix tailTrace_4743166
  have hstable : (prefixWord ++ tailWord_4743166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743166).length < 2 ^ (prefixWord ++ tailWord_4743166).sum := by decide
  have hdescent : baseEnd_4743166 < baseStart_4743166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743169 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_4743169 : Nat := 118140960795 + 4743169 * 2 ^ 59
def prefixEnd_4743169 : Nat := 4983230072969 + 3 ^ 40 * 4743169 * 2
def baseEnd_4743169 : Nat := 2435525522505658063174069

theorem tailTrace_4743169 : CollatzResearch.WordTrace tailWord_4743169 prefixEnd_4743169 2435525522505658063174069 := by
  unfold tailWord_4743169
  simp only [CollatzResearch.WordTrace]
  refine ⟨172997585753316256617440561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115331723835544171078293707 172997585753316256617440561)
  ·
    refine ⟨129748189314987192463080421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172997585753316256617440561 129748189314987192463080421)
    ·
      refine ⟨24327785496560098586827579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129748189314987192463080421 24327785496560098586827579)
      ·
        refine ⟨36491678244840147880241369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24327785496560098586827579 36491678244840147880241369)
        ·
          refine ⟨27368758683630110910181027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36491678244840147880241369 27368758683630110910181027)
          ·
            refine ⟨41053138025445166365271541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27368758683630110910181027 41053138025445166365271541)
            ·
              refine ⟨3848731689885484346744207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41053138025445166365271541 3848731689885484346744207)
              ·
                refine ⟨5773097534828226520116311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848731689885484346744207 5773097534828226520116311)
                ·
                  refine ⟨8659646302242339780174467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773097534828226520116311 8659646302242339780174467)
                  ·
                    refine ⟨12989469453363509670261701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8659646302242339780174467 12989469453363509670261701)
                    ·
                      refine ⟨2435525522505658063174069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12989469453363509670261701 2435525522505658063174069)
                      ·
                        rfl

theorem cell23_4743169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_4743169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743169 prefixEnd_4743169 := by exact prefixLift 4743169
  have htrace : WordTrace (prefixWord ++ tailWord_4743169) baseStart_4743169 baseEnd_4743169 := by
    simpa [prefixWord, tailWord_4743169, baseEnd_4743169] using wordTrace_append hprefix tailTrace_4743169
  have hstable : (prefixWord ++ tailWord_4743169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743169).length < 2 ^ (prefixWord ++ tailWord_4743169).sum := by decide
  have hdescent : baseEnd_4743169 < baseStart_4743169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743174 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4743174 : Nat := 118140960795 + 4743174 * 2 ^ 59
def prefixEnd_4743174 : Nat := 4983230072969 + 3 ^ 40 * 4743174 * 2
def baseEnd_4743174 : Nat := 811842696636310181203849

theorem tailTrace_4743174 : CollatzResearch.WordTrace tailWord_4743174 prefixEnd_4743174 811842696636310181203849 := by
  unfold tailWord_4743174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406180253696816952230393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115331845412198761647581717 5406180253696816952230393)
  ·
    refine ⟨4054635190272612714172795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5406180253696816952230393 4054635190272612714172795)
    ·
      refine ⟨6081952785408919071259193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054635190272612714172795 6081952785408919071259193)
      ·
        refine ⟨4561464589056689303444395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6081952785408919071259193 4561464589056689303444395)
        ·
          refine ⟨6842196883585033955166593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561464589056689303444395 6842196883585033955166593)
          ·
            refine ⟨5131647662688775466374945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6842196883585033955166593 5131647662688775466374945)
            ·
              refine ⟨3848735747016581599781209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5131647662688775466374945 3848735747016581599781209)
              ·
                refine ⟨2886551810262436199835907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3848735747016581599781209 2886551810262436199835907)
                ·
                  refine ⟨4329827715393654299753861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886551810262436199835907 4329827715393654299753861)
                  ·
                    refine ⟨811842696636310181203849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329827715393654299753861 811842696636310181203849)
                    ·
                      rfl

theorem cell23_4743174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4743174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743174 prefixEnd_4743174 := by exact prefixLift 4743174
  have htrace : WordTrace (prefixWord ++ tailWord_4743174) baseStart_4743174 baseEnd_4743174 := by
    simpa [prefixWord, tailWord_4743174, baseEnd_4743174] using wordTrace_append hprefix tailTrace_4743174
  have hstable : (prefixWord ++ tailWord_4743174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743174).length < 2 ^ (prefixWord ++ tailWord_4743174).sum := by decide
  have hdescent : baseEnd_4743174 < baseStart_4743174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743220 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4743220 : Nat := 118140960795 + 4743220 * 2 ^ 59
def prefixEnd_4743220 : Nat := 4983230072969 + 3 ^ 40 * 4743220 * 2
def baseEnd_4743220 : Nat := 2435551710019037363636335

theorem tailTrace_4743220 : CollatzResearch.WordTrace tailWord_4743220 prefixEnd_4743220 2435551710019037363636335 := by
  unfold tailWord_4743220
  simp only [CollatzResearch.WordTrace]
  refine ⟨86499722938065746163773557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115332963917420994885031409 86499722938065746163773557)
  ·
    refine ⟨8109349025443663702853771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86499722938065746163773557 8109349025443663702853771)
    ·
      refine ⟨12164023538165495554280657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8109349025443663702853771 12164023538165495554280657)
      ·
        refine ⟨9123017653624121665710493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12164023538165495554280657 9123017653624121665710493)
        ·
          refine ⟨3421131620109045624641435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9123017653624121665710493 3421131620109045624641435)
          ·
            refine ⟨5131697430163568436962153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421131620109045624641435 5131697430163568436962153)
            ·
              refine ⟨3848773072622676327721615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5131697430163568436962153 3848773072622676327721615)
              ·
                refine ⟨5773159608934014491582423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848773072622676327721615 5773159608934014491582423)
                ·
                  refine ⟨8659739413401021737373635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773159608934014491582423 8659739413401021737373635)
                  ·
                    refine ⟨12989609120101532606060453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8659739413401021737373635 12989609120101532606060453)
                    ·
                      refine ⟨2435551710019037363636335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12989609120101532606060453 2435551710019037363636335)
                      ·
                        rfl

theorem cell23_4743220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4743220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743220 prefixEnd_4743220 := by exact prefixLift 4743220
  have htrace : WordTrace (prefixWord ++ tailWord_4743220) baseStart_4743220 baseEnd_4743220 := by
    simpa [prefixWord, tailWord_4743220, baseEnd_4743220] using wordTrace_append hprefix tailTrace_4743220
  have hstable : (prefixWord ++ tailWord_4743220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743220).length < 2 ^ (prefixWord ++ tailWord_4743220).sum := by decide
  have hdescent : baseEnd_4743220 < baseStart_4743220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743329 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 2, 5]
def baseStart_4743329 : Nat := 118140960795 + 4743329 * 2 ^ 59
def prefixEnd_4743329 : Nat := 4983230072969 + 3 ^ 40 * 4743329 * 2
def baseEnd_4743329 : Nat := 811869226470125812391111

theorem tailTrace_4743329 : CollatzResearch.WordTrace tailWord_4743329 prefixEnd_4743329 811869226470125812391111 := by
  unfold tailWord_4743329
  simp only [CollatzResearch.WordTrace]
  refine ⟨173003421432736603943265041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115335614288491069295510027 173003421432736603943265041)
  ·
    refine ⟨129752566074552452957448781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173003421432736603943265041 129752566074552452957448781)
    ·
      refine ⟨48657212277957169859043293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129752566074552452957448781 48657212277957169859043293)
      ·
        refine ⟨18246454604233938697141235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48657212277957169859043293 18246454604233938697141235)
        ·
          refine ⟨27369681906350908045711853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18246454604233938697141235 27369681906350908045711853)
          ·
            refine ⟨10263630714881590517141945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27369681906350908045711853 10263630714881590517141945)
            ·
              refine ⟨7697723036161192887856459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10263630714881590517141945 7697723036161192887856459)
              ·
                refine ⟨11546584554241789331784689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7697723036161192887856459 11546584554241789331784689)
                ·
                  refine ⟨8659938415681341998838517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11546584554241789331784689 8659938415681341998838517)
                  ·
                    refine ⟨811869226470125812391111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8659938415681341998838517 811869226470125812391111)
                    ·
                      rfl

theorem cell23_4743329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_4743329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743329 prefixEnd_4743329 := by exact prefixLift 4743329
  have htrace : WordTrace (prefixWord ++ tailWord_4743329) baseStart_4743329 baseEnd_4743329 := by
    simpa [prefixWord, tailWord_4743329, baseEnd_4743329] using wordTrace_append hprefix tailTrace_4743329
  have hstable : (prefixWord ++ tailWord_4743329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743329).length < 2 ^ (prefixWord ++ tailWord_4743329).sum := by decide
  have hdescent : baseEnd_4743329 < baseStart_4743329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743456 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4743456 : Nat := 118140960795 + 4743456 * 2 ^ 59
def prefixEnd_4743456 : Nat := 4983230072969 + 3 ^ 40 * 4743456 * 2
def baseEnd_4743456 : Nat := 2435672891453498440285249

theorem tailTrace_4743456 : CollatzResearch.WordTrace tailWord_4743456 prefixEnd_4743456 2435672891453498440285249 := by
  unfold tailWord_4743456
  simp only [CollatzResearch.WordTrace]
  refine ⟨86504026751638252316569111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115338702335517669755425481 86504026751638252316569111)
  ·
    refine ⟨129756040127457378474853667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86504026751638252316569111 129756040127457378474853667)
    ·
      refine ⟨194634060191186067712280501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129756040127457378474853667 194634060191186067712280501)
      ·
        refine ⟨18246943142923693848026297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194634060191186067712280501 18246943142923693848026297)
        ·
          refine ⟨13685207357192770386019723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18246943142923693848026297 13685207357192770386019723)
          ·
            refine ⟨20527811035789155579029585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685207357192770386019723 20527811035789155579029585)
            ·
              refine ⟨15395858276841866684272189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20527811035789155579029585 15395858276841866684272189)
              ·
                refine ⟨5773446853815700006602071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15395858276841866684272189 5773446853815700006602071)
                ·
                  refine ⟨8660170280723550009903107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773446853815700006602071 8660170280723550009903107)
                  ·
                    refine ⟨12990255421085325014854661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8660170280723550009903107 12990255421085325014854661)
                    ·
                      refine ⟨2435672891453498440285249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12990255421085325014854661 2435672891453498440285249)
                      ·
                        rfl

theorem cell23_4743456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4743456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743456 prefixEnd_4743456 := by exact prefixLift 4743456
  have htrace : WordTrace (prefixWord ++ tailWord_4743456) baseStart_4743456 baseEnd_4743456 := by
    simpa [prefixWord, tailWord_4743456, baseEnd_4743456] using wordTrace_append hprefix tailTrace_4743456
  have hstable : (prefixWord ++ tailWord_4743456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743456).length < 2 ^ (prefixWord ++ tailWord_4743456).sum := by decide
  have hdescent : baseEnd_4743456 < baseStart_4743456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743459 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 5]
def baseStart_4743459 : Nat := 118140960795 + 4743459 * 2 ^ 59
def prefixEnd_4743459 : Nat := 4983230072969 + 3 ^ 40 * 4743459 * 2
def baseEnd_4743459 : Nat := 2435674431895461928547735

theorem tailTrace_4743459 : CollatzResearch.WordTrace tailWord_4743459 prefixEnd_4743459 2435674431895461928547735 := by
  unfold tailWord_4743459
  simp only [CollatzResearch.WordTrace]
  refine ⟨173008162922265636145497431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115338775281510424096998287 173008162922265636145497431)
  ·
    refine ⟨259512244383398454218246147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173008162922265636145497431 259512244383398454218246147)
    ·
      refine ⟨389268366575097681327369221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259512244383398454218246147 389268366575097681327369221)
      ·
        refine ⟨72987818732830815248881729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389268366575097681327369221 72987818732830815248881729)
        ·
          refine ⟨54740864049623111436661297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72987818732830815248881729 54740864049623111436661297)
          ·
            refine ⟨41055648037217333577495973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54740864049623111436661297 41055648037217333577495973)
            ·
              refine ⟨7697934006978250045780495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41055648037217333577495973 7697934006978250045780495)
              ·
                refine ⟨11546901010467375068670743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7697934006978250045780495 11546901010467375068670743)
                ·
                  refine ⟨17320351515701062603006115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11546901010467375068670743 17320351515701062603006115)
                  ·
                    refine ⟨25980527273551593904509173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17320351515701062603006115 25980527273551593904509173)
                    ·
                      refine ⟨2435674431895461928547735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25980527273551593904509173 2435674431895461928547735)
                      ·
                        rfl

theorem cell23_4743459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_4743459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743459 prefixEnd_4743459 := by exact prefixLift 4743459
  have htrace : WordTrace (prefixWord ++ tailWord_4743459) baseStart_4743459 baseEnd_4743459 := by
    simpa [prefixWord, tailWord_4743459, baseEnd_4743459] using wordTrace_append hprefix tailTrace_4743459
  have hstable : (prefixWord ++ tailWord_4743459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743459).length < 2 ^ (prefixWord ++ tailWord_4743459).sum := by decide
  have hdescent : baseEnd_4743459 < baseStart_4743459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743476 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4743476 : Nat := 118140960795 + 4743476 * 2 ^ 59
def prefixEnd_4743476 : Nat := 4983230072969 + 3 ^ 40 * 4743476 * 2
def baseEnd_4743476 : Nat := 2435683161066588362035157

theorem tailTrace_4743476 : CollatzResearch.WordTrace tailWord_4743476 prefixEnd_4743476 2435683161066588362035157 := by
  unfold tailWord_4743476
  simp only [CollatzResearch.WordTrace]
  refine ⟨86504391481602024024433141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115339188642136032032577521 86504391481602024024433141)
  ·
    refine ⟨8109786701400189752290607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86504391481602024024433141 8109786701400189752290607)
    ·
      refine ⟨12164680052100284628435911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8109786701400189752290607 12164680052100284628435911)
      ·
        refine ⟨18247020078150426942653867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12164680052100284628435911 18247020078150426942653867)
        ·
          refine ⟨27370530117225640413980801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18247020078150426942653867 27370530117225640413980801)
          ·
            refine ⟨20527897587919230310485601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27370530117225640413980801 20527897587919230310485601)
            ·
              refine ⟨15395923190939422732864201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20527897587919230310485601 15395923190939422732864201)
              ·
                refine ⟨11546942393204567049648151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15395923190939422732864201 11546942393204567049648151)
                ·
                  refine ⟨17320413589806850574472227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11546942393204567049648151 17320413589806850574472227)
                  ·
                    refine ⟨25980620384710275861708341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17320413589806850574472227 25980620384710275861708341)
                    ·
                      refine ⟨2435683161066588362035157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25980620384710275861708341 2435683161066588362035157)
                      ·
                        rfl

theorem cell23_4743476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4743476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743476 prefixEnd_4743476 := by exact prefixLift 4743476
  have htrace : WordTrace (prefixWord ++ tailWord_4743476) baseStart_4743476 baseEnd_4743476 := by
    simpa [prefixWord, tailWord_4743476, baseEnd_4743476] using wordTrace_append hprefix tailTrace_4743476
  have hstable : (prefixWord ++ tailWord_4743476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743476).length < 2 ^ (prefixWord ++ tailWord_4743476).sum := by decide
  have hdescent : baseEnd_4743476 < baseStart_4743476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743506 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_4743506 : Nat := 118140960795 + 4743506 * 2 ^ 59
def prefixEnd_4743506 : Nat := 4983230072969 + 3 ^ 40 * 4743506 * 2
def baseEnd_4743506 : Nat := 2435698565486223244660019

theorem tailTrace_4743506 : CollatzResearch.WordTrace tailWord_4743506 prefixEnd_4743506 2435698565486223244660019 := by
  unfold tailWord_4743506
  simp only [CollatzResearch.WordTrace]
  refine ⟨43252469288273840793114593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115339918102063575448305581 43252469288273840793114593)
  ·
    refine ⟨32439351966205380594835945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43252469288273840793114593 32439351966205380594835945)
    ·
      refine ⟨24329513974654035446126959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32439351966205380594835945 24329513974654035446126959)
      ·
        refine ⟨36494270961981053169190439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24329513974654035446126959 36494270961981053169190439)
        ·
          refine ⟨54741406442971579753785659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36494270961981053169190439 54741406442971579753785659)
          ·
            refine ⟨82112109664457369630678489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54741406442971579753785659 82112109664457369630678489)
            ·
              refine ⟨61584082248343027223008867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82112109664457369630678489 61584082248343027223008867)
              ·
                refine ⟨92376123372514540834513301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61584082248343027223008867 92376123372514540834513301)
                ·
                  refine ⟨4330130783086619101617811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92376123372514540834513301 4330130783086619101617811)
                  ·
                    refine ⟨6495196174629928652426717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4330130783086619101617811 6495196174629928652426717)
                    ·
                      refine ⟨2435698565486223244660019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495196174629928652426717 2435698565486223244660019)
                      ·
                        rfl

theorem cell23_4743506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_4743506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743506 prefixEnd_4743506 := by exact prefixLift 4743506
  have htrace : WordTrace (prefixWord ++ tailWord_4743506) baseStart_4743506 baseEnd_4743506 := by
    simpa [prefixWord, tailWord_4743506, baseEnd_4743506] using wordTrace_append hprefix tailTrace_4743506
  have hstable : (prefixWord ++ tailWord_4743506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743506).length < 2 ^ (prefixWord ++ tailWord_4743506).sum := by decide
  have hdescent : baseEnd_4743506 < baseStart_4743506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743523 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 3]
def baseStart_4743523 : Nat := 118140960795 + 4743523 * 2 ^ 59
def prefixEnd_4743523 : Nat := 4983230072969 + 3 ^ 40 * 4743523 * 2
def baseEnd_4743523 : Nat := 2435707294657349678147441

theorem tailTrace_4743523 : CollatzResearch.WordTrace tailWord_4743523 prefixEnd_4743523 2435707294657349678147441 := by
  unfold tailWord_4743523
  simp only [CollatzResearch.WordTrace]
  refine ⟨173010497194033775075827223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115340331462689183383884815 173010497194033775075827223)
  ·
    refine ⟨259515745791050662613740835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173010497194033775075827223 259515745791050662613740835)
    ·
      refine ⟨389273618686575993920611253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259515745791050662613740835 389273618686575993920611253)
      ·
        refine ⟨36494401751866499430057305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 389273618686575993920611253 36494401751866499430057305)
        ·
          refine ⟨27370801313899874572542979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36494401751866499430057305 27370801313899874572542979)
          ·
            refine ⟨41056201970849811858814469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27370801313899874572542979 41056201970849811858814469)
            ·
              refine ⟨7698037869534339723527713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41056201970849811858814469 7698037869534339723527713)
              ·
                refine ⟨5773528402150754792645785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7698037869534339723527713 5773528402150754792645785)
                ·
                  refine ⟨4330146301613066094484339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5773528402150754792645785 4330146301613066094484339)
                  ·
                    refine ⟨6495219452419599141726509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4330146301613066094484339 6495219452419599141726509)
                    ·
                      refine ⟨2435707294657349678147441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495219452419599141726509 2435707294657349678147441)
                      ·
                        rfl

theorem cell23_4743523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_4743523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743523 prefixEnd_4743523 := by exact prefixLift 4743523
  have htrace : WordTrace (prefixWord ++ tailWord_4743523) baseStart_4743523 baseEnd_4743523 := by
    simpa [prefixWord, tailWord_4743523, baseEnd_4743523] using wordTrace_append hprefix tailTrace_4743523
  have hstable : (prefixWord ++ tailWord_4743523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743523).length < 2 ^ (prefixWord ++ tailWord_4743523).sum := by decide
  have hdescent : baseEnd_4743523 < baseStart_4743523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743559 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_4743559 : Nat := 118140960795 + 4743559 * 2 ^ 59
def prefixEnd_4743559 : Nat := 4983230072969 + 3 ^ 40 * 4743559 * 2
def baseEnd_4743559 : Nat := 2435725779960911537297275

theorem tailTrace_4743559 : CollatzResearch.WordTrace tailWord_4743559 prefixEnd_4743559 2435725779960911537297275 := by
  unfold tailWord_4743559
  simp only [CollatzResearch.WordTrace]
  refine ⟨173011810221903353224137731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115341206814602235482758487 173011810221903353224137731)
  ·
    refine ⟨259517715332855029836206597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173011810221903353224137731 259517715332855029836206597)
    ·
      refine ⟨48659571624910318094288737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259517715332855029836206597 48659571624910318094288737)
      ·
        refine ⟨36494678718682738570716553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48659571624910318094288737 36494678718682738570716553)
        ·
          refine ⟨27371009039012053928037415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36494678718682738570716553 27371009039012053928037415)
          ·
            refine ⟨41056513558518080892056123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27371009039012053928037415 41056513558518080892056123)
            ·
              refine ⟨61584770337777121338084185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41056513558518080892056123 61584770337777121338084185)
              ·
                refine ⟨46188577753332841003563139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61584770337777121338084185 46188577753332841003563139)
                ·
                  refine ⟨69282866629999261505344709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46188577753332841003563139 69282866629999261505344709)
                  ·
                    refine ⟨12990537493124861532252133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69282866629999261505344709 12990537493124861532252133)
                    ·
                      refine ⟨2435725779960911537297275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12990537493124861532252133 2435725779960911537297275)
                      ·
                        rfl

theorem cell23_4743559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_4743559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743559 prefixEnd_4743559 := by exact prefixLift 4743559
  have htrace : WordTrace (prefixWord ++ tailWord_4743559) baseStart_4743559 baseEnd_4743559 := by
    simpa [prefixWord, tailWord_4743559, baseEnd_4743559] using wordTrace_append hprefix tailTrace_4743559
  have hstable : (prefixWord ++ tailWord_4743559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743559).length < 2 ^ (prefixWord ++ tailWord_4743559).sum := by decide
  have hdescent : baseEnd_4743559 < baseStart_4743559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743574 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4743574 : Nat := 118140960795 + 4743574 * 2 ^ 59
def prefixEnd_4743574 : Nat := 4983230072969 + 3 ^ 40 * 4743574 * 2
def baseEnd_4743574 : Nat := 2435733482170728978609707

theorem tailTrace_4743574 : CollatzResearch.WordTrace tailWord_4743574 prefixEnd_4743574 2435733482170728978609707 := by
  unfold tailWord_4743574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813272332303063174120861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115341571544566007190622517 10813272332303063174120861)
  ·
    refine ⟨4054977124613648690295323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10813272332303063174120861 4054977124613648690295323)
    ·
      refine ⟨6082465686920473035442985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054977124613648690295323 6082465686920473035442985)
      ·
        refine ⟨4561849265190354776582239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6082465686920473035442985 4561849265190354776582239)
        ·
          refine ⟨6842773897785532164873359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561849265190354776582239 6842773897785532164873359)
          ·
            refine ⟨10264160846678298247310039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842773897785532164873359 10264160846678298247310039)
            ·
              refine ⟨15396241270017447370965059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10264160846678298247310039 15396241270017447370965059)
              ·
                refine ⟨23094361905026171056447589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15396241270017447370965059 23094361905026171056447589)
                ·
                  refine ⟨4330192857192407073083923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23094361905026171056447589 4330192857192407073083923)
                  ·
                    refine ⟨6495289285788610609625885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4330192857192407073083923 6495289285788610609625885)
                    ·
                      refine ⟨2435733482170728978609707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495289285788610609625885 2435733482170728978609707)
                      ·
                        rfl

theorem cell23_4743574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4743574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743574 prefixEnd_4743574 := by exact prefixLift 4743574
  have htrace : WordTrace (prefixWord ++ tailWord_4743574) baseStart_4743574 baseEnd_4743574 := by
    simpa [prefixWord, tailWord_4743574, baseEnd_4743574] using wordTrace_append hprefix tailTrace_4743574
  have hstable : (prefixWord ++ tailWord_4743574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743574).length < 2 ^ (prefixWord ++ tailWord_4743574).sum := by decide
  have hdescent : baseEnd_4743574 < baseStart_4743574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743576 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4743576 : Nat := 118140960795 + 4743576 * 2 ^ 59
def prefixEnd_4743576 : Nat := 4983230072969 + 3 ^ 40 * 4743576 * 2
def baseEnd_4743576 : Nat := 2435734509132037970784697

theorem tailTrace_4743576 : CollatzResearch.WordTrace tailWord_4743576 prefixEnd_4743576 2435734509132037970784697 := by
  unfold tailWord_4743576
  simp only [CollatzResearch.WordTrace]
  refine ⟨86506215131420882563753291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115341620175227843418337721 86506215131420882563753291)
  ·
    refine ⟨129759322697131323845629937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86506215131420882563753291 129759322697131323845629937)
    ·
      refine ⟨97319492022848492884222453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129759322697131323845629937 97319492022848492884222453)
      ·
        refine ⟨9123702377142046207895855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97319492022848492884222453 9123702377142046207895855)
        ·
          refine ⟨13685553565713069311843783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9123702377142046207895855 13685553565713069311843783)
          ·
            refine ⟨20528330348569603967765675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685553565713069311843783 20528330348569603967765675)
            ·
              refine ⟨30792495522854405951648513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20528330348569603967765675 30792495522854405951648513)
              ·
                refine ⟨23094371642140804463736385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30792495522854405951648513 23094371642140804463736385)
                ·
                  refine ⟨17320778731605603347802289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23094371642140804463736385 17320778731605603347802289)
                  ·
                    refine ⟨12990584048704202510851717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17320778731605603347802289 12990584048704202510851717)
                    ·
                      refine ⟨2435734509132037970784697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12990584048704202510851717 2435734509132037970784697)
                      ·
                        rfl

theorem cell23_4743576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4743576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743576 prefixEnd_4743576 := by exact prefixLift 4743576
  have htrace : WordTrace (prefixWord ++ tailWord_4743576) baseStart_4743576 baseEnd_4743576 := by
    simpa [prefixWord, tailWord_4743576, baseEnd_4743576] using wordTrace_append hprefix tailTrace_4743576
  have hstable : (prefixWord ++ tailWord_4743576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743576).length < 2 ^ (prefixWord ++ tailWord_4743576).sum := by decide
  have hdescent : baseEnd_4743576 < baseStart_4743576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743586 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_4743586 : Nat := 118140960795 + 4743586 * 2 ^ 59
def prefixEnd_4743586 : Nat := 4983230072969 + 3 ^ 40 * 4743586 * 2
def baseEnd_4743586 : Nat := 270637738215398103517739

theorem tailTrace_4743586 : CollatzResearch.WordTrace tailWord_4743586 prefixEnd_4743586 270637738215398103517739 := by
  unfold tailWord_4743586
  simp only [CollatzResearch.WordTrace]
  refine ⟨43253198748201384208842653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115341863328537024556913741 43253198748201384208842653)
  ·
    refine ⟨16219949530575519078315995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43253198748201384208842653 16219949530575519078315995)
    ·
      refine ⟨24329924295863278617473993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16219949530575519078315995 24329924295863278617473993)
      ·
        refine ⟨18247443221897458963105495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24329924295863278617473993 18247443221897458963105495)
        ·
          refine ⟨27371164832846188444658243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18247443221897458963105495 27371164832846188444658243)
          ·
            refine ⟨41056747249269282666987365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27371164832846188444658243 41056747249269282666987365)
            ·
              refine ⟨7698140109237990500060131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41056747249269282666987365 7698140109237990500060131)
              ·
                refine ⟨11547210163856985750090197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7698140109237990500060131 11547210163856985750090197)
                ·
                  refine ⟨270637738215398103517739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11547210163856985750090197 270637738215398103517739)
                  ·
                    rfl

theorem cell23_4743586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_4743586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743586 prefixEnd_4743586 := by exact prefixLift 4743586
  have htrace : WordTrace (prefixWord ++ tailWord_4743586) baseStart_4743586 baseEnd_4743586 := by
    simpa [prefixWord, tailWord_4743586, baseEnd_4743586] using wordTrace_append hprefix tailTrace_4743586
  have hstable : (prefixWord ++ tailWord_4743586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743586).length < 2 ^ (prefixWord ++ tailWord_4743586).sum := by decide
  have hdescent : baseEnd_4743586 < baseStart_4743586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743597 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_4743597 : Nat := 118140960795 + 4743597 * 2 ^ 59
def prefixEnd_4743597 : Nat := 4983230072969 + 3 ^ 40 * 4743597 * 2
def baseEnd_4743597 : Nat := 2435745292225782388622101

theorem tailTrace_4743597 : CollatzResearch.WordTrace tailWord_4743597 prefixEnd_4743597 2435745292225782388622101 := by
  unfold tailWord_4743597
  simp only [CollatzResearch.WordTrace]
  refine ⟨173013196195765685714021045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115342130797177123809347363 173013196195765685714021045)
  ·
    refine ⟨16219987143353033035689473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173013196195765685714021045 16219987143353033035689473)
    ·
      refine ⟨12164990357514774776767105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16219987143353033035689473 12164990357514774776767105)
      ·
        refine ⟨9123742768136081082575329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12164990357514774776767105 9123742768136081082575329)
        ·
          refine ⟨6842807076102060811931497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9123742768136081082575329 6842807076102060811931497)
          ·
            refine ⟨5132105307076545608948623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6842807076102060811931497 5132105307076545608948623)
            ·
              refine ⟨7698157960614818413422935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132105307076545608948623 7698157960614818413422935)
              ·
                refine ⟨11547236940922227620134403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7698157960614818413422935 11547236940922227620134403)
                ·
                  refine ⟨17320855411383341430201605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11547236940922227620134403 17320855411383341430201605)
                  ·
                    refine ⟨3247660389634376518162801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17320855411383341430201605 3247660389634376518162801)
                    ·
                      refine ⟨2435745292225782388622101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247660389634376518162801 2435745292225782388622101)
                      ·
                        rfl

theorem cell23_4743597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_4743597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743597 prefixEnd_4743597 := by exact prefixLift 4743597
  have htrace : WordTrace (prefixWord ++ tailWord_4743597) baseStart_4743597 baseEnd_4743597 := by
    simpa [prefixWord, tailWord_4743597, baseEnd_4743597] using wordTrace_append hprefix tailTrace_4743597
  have hstable : (prefixWord ++ tailWord_4743597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743597).length < 2 ^ (prefixWord ++ tailWord_4743597).sum := by decide
  have hdescent : baseEnd_4743597 < baseStart_4743597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743706 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_4743706 : Nat := 118140960795 + 4743706 * 2 ^ 59
def prefixEnd_4743706 : Nat := 4983230072969 + 3 ^ 40 * 4743706 * 2
def baseEnd_4743706 : Nat := 811933753872374154053033

theorem tailTrace_4743706 : CollatzResearch.WordTrace tailWord_4743706 prefixEnd_4743706 811933753872374154053033 := by
  unfold tailWord_4743706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43254292938092699332434743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115344781168247198219825981 43254292938092699332434743)
  ·
    refine ⟨64881439407139048998652115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43254292938092699332434743 64881439407139048998652115)
    ·
      refine ⟨97322159110708573497978173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64881439407139048998652115 97322159110708573497978173)
      ·
        refine ⟨36495809666515715061741815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97322159110708573497978173 36495809666515715061741815)
        ·
          refine ⟨54743714499773572592612723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36495809666515715061741815 54743714499773572592612723)
          ·
            refine ⟨82115571749660358888919085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54743714499773572592612723 82115571749660358888919085)
            ·
              refine ⟨30793339406122634583344657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82115571749660358888919085 30793339406122634583344657)
              ·
                refine ⟨23095004554591975937508493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30793339406122634583344657 23095004554591975937508493)
                ·
                  refine ⟨8660626707971990976565685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23095004554591975937508493 8660626707971990976565685)
                  ·
                    refine ⟨811933753872374154053033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8660626707971990976565685 811933753872374154053033)
                    ·
                      rfl

theorem cell23_4743706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_4743706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743706 prefixEnd_4743706 := by exact prefixLift 4743706
  have htrace : WordTrace (prefixWord ++ tailWord_4743706) baseStart_4743706 baseEnd_4743706 := by
    simpa [prefixWord, tailWord_4743706, baseEnd_4743706] using wordTrace_append hprefix tailTrace_4743706
  have hstable : (prefixWord ++ tailWord_4743706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743706).length < 2 ^ (prefixWord ++ tailWord_4743706).sum := by decide
  have hdescent : baseEnd_4743706 < baseStart_4743706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743713 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4743713 : Nat := 118140960795 + 4743713 * 2 ^ 59
def prefixEnd_4743713 : Nat := 4983230072969 + 3 ^ 40 * 4743713 * 2
def baseEnd_4743713 : Nat := 2435804855981703934771567

theorem tailTrace_4743713 : CollatzResearch.WordTrace tailWord_4743713 prefixEnd_4743713 2435804855981703934771567 := by
  unfold tailWord_4743713
  simp only [CollatzResearch.WordTrace]
  refine ⟨173017427063345437525243793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115344951375563625016829195 173017427063345437525243793)
  ·
    refine ⟨129763070297509078143932845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173017427063345437525243793 129763070297509078143932845)
    ·
      refine ⟨48661151361565904303974817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129763070297509078143932845 48661151361565904303974817)
      ·
        refine ⟨36495863521174428227981113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48661151361565904303974817 36495863521174428227981113)
        ·
          refine ⟨27371897640880821170985835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36495863521174428227981113 27371897640880821170985835)
          ·
            refine ⟨41057846461321231756478753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27371897640880821170985835 41057846461321231756478753)
            ·
              refine ⟨30793384845990923817359065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41057846461321231756478753 30793384845990923817359065)
              ·
                refine ⟨23095038634493192863019299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30793384845990923817359065 23095038634493192863019299)
                ·
                  refine ⟨34642557951739789294528949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23095038634493192863019299 34642557951739789294528949)
                  ·
                    refine ⟨3247739807975605246362089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34642557951739789294528949 3247739807975605246362089)
                    ·
                      refine ⟨2435804855981703934771567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247739807975605246362089 2435804855981703934771567)
                      ·
                        rfl

theorem cell23_4743713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4743713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743713 prefixEnd_4743713 := by exact prefixLift 4743713
  have htrace : WordTrace (prefixWord ++ tailWord_4743713) baseStart_4743713 baseEnd_4743713 := by
    simpa [prefixWord, tailWord_4743713, baseEnd_4743713] using wordTrace_append hprefix tailTrace_4743713
  have hstable : (prefixWord ++ tailWord_4743713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743713).length < 2 ^ (prefixWord ++ tailWord_4743713).sum := by decide
  have hdescent : baseEnd_4743713 < baseStart_4743713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743720 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4743720 : Nat := 118140960795 + 4743720 * 2 ^ 59
def prefixEnd_4743720 : Nat := 4983230072969 + 3 ^ 40 * 4743720 * 2
def baseEnd_4743720 : Nat := 2435808450346285407384035

theorem tailTrace_4743720 : CollatzResearch.WordTrace tailWord_4743720 prefixEnd_4743720 2435808450346285407384035 := by
  unfold tailWord_4743720
  simp only [CollatzResearch.WordTrace]
  refine ⟨86508841187160038860374307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115345121582880051813832409 86508841187160038860374307)
  ·
    refine ⟨129763261780740058290561461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86508841187160038860374307 129763261780740058290561461)
    ·
      refine ⟨12165305791944380464740137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129763261780740058290561461 12165305791944380464740137)
      ·
        refine ⟨9123979343958285348555103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12165305791944380464740137 9123979343958285348555103)
        ·
          refine ⟨13685969015937428022832655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9123979343958285348555103 13685969015937428022832655)
          ·
            refine ⟨20528953523906142034248983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685969015937428022832655 20528953523906142034248983)
            ·
              refine ⟨30793430285859213051373475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20528953523906142034248983 30793430285859213051373475)
              ·
                refine ⟨46190145428788819577060213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30793430285859213051373475 46190145428788819577060213)
                ·
                  refine ⟨4330326133948951835349395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46190145428788819577060213 4330326133948951835349395)
                  ·
                    refine ⟨6495489200923427753024093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4330326133948951835349395 6495489200923427753024093)
                    ·
                      refine ⟨2435808450346285407384035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495489200923427753024093 2435808450346285407384035)
                      ·
                        rfl

theorem cell23_4743720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4743720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743720 prefixEnd_4743720 := by exact prefixLift 4743720
  have htrace : WordTrace (prefixWord ++ tailWord_4743720) baseStart_4743720 baseEnd_4743720 := by
    simpa [prefixWord, tailWord_4743720, baseEnd_4743720] using wordTrace_append hprefix tailTrace_4743720
  have hstable : (prefixWord ++ tailWord_4743720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743720).length < 2 ^ (prefixWord ++ tailWord_4743720).sum := by decide
  have hdescent : baseEnd_4743720 < baseStart_4743720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743730 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_4743730 : Nat := 118140960795 + 4743730 * 2 ^ 59
def prefixEnd_4743730 : Nat := 4983230072969 + 3 ^ 40 * 4743730 * 2
def baseEnd_4743730 : Nat := 2435813585152830368258989

theorem tailTrace_4743730 : CollatzResearch.WordTrace tailWord_4743730 prefixEnd_4743730 2435813585152830368258989 := by
  unfold tailWord_4743730
  simp only [CollatzResearch.WordTrace]
  refine ⟨43254511776070962357153161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115345364736189232952408429 43254511776070962357153161)
  ·
    refine ⟨32440883832053221767864871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43254511776070962357153161 32440883832053221767864871)
    ·
      refine ⟨48661325748079832651797307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32440883832053221767864871 48661325748079832651797307)
      ·
        refine ⟨72991988622119748977695961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48661325748079832651797307 72991988622119748977695961)
        ·
          refine ⟨54743991466589811733271971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72991988622119748977695961 54743991466589811733271971)
          ·
            refine ⟨82115987199884717599907957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54743991466589811733271971 82115987199884717599907957)
            ·
              refine ⟨7698373799989192274991371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82115987199884717599907957 7698373799989192274991371)
              ·
                refine ⟨11547560699983788412487057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7698373799989192274991371 11547560699983788412487057)
                ·
                  refine ⟨8660670524987841309365293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11547560699983788412487057 8660670524987841309365293)
                  ·
                    refine ⟨3247751446870440491011985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8660670524987841309365293 3247751446870440491011985)
                    ·
                      refine ⟨2435813585152830368258989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247751446870440491011985 2435813585152830368258989)
                      ·
                        rfl

theorem cell23_4743730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_4743730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743730 prefixEnd_4743730 := by exact prefixLift 4743730
  have htrace : WordTrace (prefixWord ++ tailWord_4743730) baseStart_4743730 baseEnd_4743730 := by
    simpa [prefixWord, tailWord_4743730, baseEnd_4743730] using wordTrace_append hprefix tailTrace_4743730
  have hstable : (prefixWord ++ tailWord_4743730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743730).length < 2 ^ (prefixWord ++ tailWord_4743730).sum := by decide
  have hdescent : baseEnd_4743730 < baseStart_4743730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743736 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_4743736 : Nat := 118140960795 + 4743736 * 2 ^ 59
def prefixEnd_4743736 : Nat := 4983230072969 + 3 ^ 40 * 4743736 * 2
def baseEnd_4743736 : Nat := 811938888678919114927987

theorem tailTrace_4743736 : CollatzResearch.WordTrace tailWord_4743736 prefixEnd_4743736 811938888678919114927987 := by
  unfold tailWord_4743736
  simp only [CollatzResearch.WordTrace]
  refine ⟨86509132971131056226665531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115345510628174741635554041 86509132971131056226665531)
  ·
    refine ⟨129763699456696584339998297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86509132971131056226665531 129763699456696584339998297)
    ·
      refine ⟨97322774592522438254998723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129763699456696584339998297 97322774592522438254998723)
      ·
        refine ⟨145984161888783657382498085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97322774592522438254998723 145984161888783657382498085)
        ·
          refine ⟨27372030354146935759218391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145984161888783657382498085 27372030354146935759218391)
          ·
            refine ⟨41058045531220403638827587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27372030354146935759218391 41058045531220403638827587)
            ·
              refine ⟨61587068296830605458241381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41058045531220403638827587 61587068296830605458241381)
              ·
                refine ⟨11547575305655738523420259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61587068296830605458241381 11547575305655738523420259)
                ·
                  refine ⟨17321362958483607785130389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11547575305655738523420259 17321362958483607785130389)
                  ·
                    refine ⟨811938888678919114927987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17321362958483607785130389 811938888678919114927987)
                    ·
                      rfl

theorem cell23_4743736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_4743736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743736 prefixEnd_4743736 := by exact prefixLift 4743736
  have htrace : WordTrace (prefixWord ++ tailWord_4743736) baseStart_4743736 baseEnd_4743736 := by
    simpa [prefixWord, tailWord_4743736, baseEnd_4743736] using wordTrace_append hprefix tailTrace_4743736
  have hstable : (prefixWord ++ tailWord_4743736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743736).length < 2 ^ (prefixWord ++ tailWord_4743736).sum := by decide
  have hdescent : baseEnd_4743736 < baseStart_4743736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743737 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4743737 : Nat := 118140960795 + 4743737 * 2 ^ 59
def prefixEnd_4743737 : Nat := 4983230072969 + 3 ^ 40 * 4743737 * 2
def baseEnd_4743737 : Nat := 2435817179517411840871457

theorem tailTrace_4743737 : CollatzResearch.WordTrace tailWord_4743737 prefixEnd_4743737 2435817179517411840871457 := by
  unfold tailWord_4743737
  simp only [CollatzResearch.WordTrace]
  refine ⟨173018302415258489624117465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115345534943505659749411643 173018302415258489624117465)
  ·
    refine ⟨129763726811443867218088099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173018302415258489624117465 129763726811443867218088099)
    ·
      refine ⟨194645590217165800827132149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129763726811443867218088099 194645590217165800827132149)
      ·
        refine ⟨18248024082859293827543639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194645590217165800827132149 18248024082859293827543639)
        ·
          refine ⟨27372036124288940741315459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18248024082859293827543639 27372036124288940741315459)
          ·
            refine ⟨41058054186433411111973189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27372036124288940741315459 41058054186433411111973189)
            ·
              refine ⟨7698385159956264583494973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41058054186433411111973189 7698385159956264583494973)
              ·
                refine ⟨2886894434983599218810615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7698385159956264583494973 2886894434983599218810615)
                ·
                  refine ⟨4330341652475398828215923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886894434983599218810615 4330341652475398828215923)
                  ·
                    refine ⟨6495512478713098242323885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4330341652475398828215923 6495512478713098242323885)
                    ·
                      refine ⟨2435817179517411840871457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495512478713098242323885 2435817179517411840871457)
                      ·
                        rfl

theorem cell23_4743737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4743737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743737 prefixEnd_4743737 := by exact prefixLift 4743737
  have htrace : WordTrace (prefixWord ++ tailWord_4743737) baseStart_4743737 baseEnd_4743737 := by
    simpa [prefixWord, tailWord_4743737, baseEnd_4743737] using wordTrace_append hprefix tailTrace_4743737
  have hstable : (prefixWord ++ tailWord_4743737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743737).length < 2 ^ (prefixWord ++ tailWord_4743737).sum := by decide
  have hdescent : baseEnd_4743737 < baseStart_4743737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743740 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_4743740 : Nat := 118140960795 + 4743740 * 2 ^ 59
def prefixEnd_4743740 : Nat := 4983230072969 + 3 ^ 40 * 4743740 * 2
def baseEnd_4743740 : Nat := 811939573319791776377981

theorem tailTrace_4743740 : CollatzResearch.WordTrace tailWord_4743740 prefixEnd_4743740 811939573319791776377981 := by
  unfold tailWord_4743740
  simp only [CollatzResearch.WordTrace]
  refine ⟨86509205917123810568238337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115345607889498414090984449 86509205917123810568238337)
  ·
    refine ⟨64881904437842857926178753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86509205917123810568238337 64881904437842857926178753)
    ·
      refine ⟨48661428328382143444634065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64881904437842857926178753 48661428328382143444634065)
      ·
        refine ⟨36496071246286607583475549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48661428328382143444634065 36496071246286607583475549)
        ·
          refine ⟨13686026717357477843803331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36496071246286607583475549 13686026717357477843803331)
          ·
            refine ⟨20529040076036216765704997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13686026717357477843803331 20529040076036216765704997)
            ·
              refine ⟨3849195014256790643569687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20529040076036216765704997 3849195014256790643569687)
              ·
                refine ⟨5773792521385185965354531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849195014256790643569687 5773792521385185965354531)
                ·
                  refine ⟨8660688782077778948031797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773792521385185965354531 8660688782077778948031797)
                  ·
                    refine ⟨811939573319791776377981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8660688782077778948031797 811939573319791776377981)
                    ·
                      rfl

theorem cell23_4743740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_4743740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743740 prefixEnd_4743740 := by exact prefixLift 4743740
  have htrace : WordTrace (prefixWord ++ tailWord_4743740) baseStart_4743740 baseEnd_4743740 := by
    simpa [prefixWord, tailWord_4743740, baseEnd_4743740] using wordTrace_append hprefix tailTrace_4743740
  have hstable : (prefixWord ++ tailWord_4743740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743740).length < 2 ^ (prefixWord ++ tailWord_4743740).sum := by decide
  have hdescent : baseEnd_4743740 < baseStart_4743740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743743 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 4]
def baseStart_4743743 : Nat := 118140960795 + 4743743 * 2 ^ 59
def prefixEnd_4743743 : Nat := 4983230072969 + 3 ^ 40 * 4743743 * 2
def baseEnd_4743743 : Nat := 2435820260401338817396429

theorem tailTrace_4743743 : CollatzResearch.WordTrace tailWord_4743743 prefixEnd_4743743 2435820260401338817396429 := by
  unfold tailWord_4743743
  simp only [CollatzResearch.WordTrace]
  refine ⟨173018521253236752648835883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115345680835491168432557255 173018521253236752648835883)
  ·
    refine ⟨259527781879855128973253825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173018521253236752648835883 259527781879855128973253825)
    ·
      refine ⟨194645836409891346729940369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259527781879855128973253825 194645836409891346729940369)
      ·
        refine ⟨145984377307418510047455277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194645836409891346729940369 145984377307418510047455277)
        ·
          refine ⟨54744141490281941267795729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145984377307418510047455277 54744141490281941267795729)
          ·
            refine ⟨41058106117711455950846797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54744141490281941267795729 41058106117711455950846797)
            ·
              refine ⟨15396789794141795981567549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41058106117711455950846797 15396789794141795981567549)
              ·
                refine ⟨5773796172803173493087831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15396789794141795981567549 5773796172803173493087831)
                ·
                  refine ⟨8660694259204760239631747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773796172803173493087831 8660694259204760239631747)
                  ·
                    refine ⟨12991041388807140359447621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8660694259204760239631747 12991041388807140359447621)
                    ·
                      refine ⟨2435820260401338817396429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12991041388807140359447621 2435820260401338817396429)
                      ·
                        rfl

theorem cell23_4743743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_4743743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743743 prefixEnd_4743743 := by exact prefixLift 4743743
  have htrace : WordTrace (prefixWord ++ tailWord_4743743) baseStart_4743743 baseEnd_4743743 := by
    simpa [prefixWord, tailWord_4743743, baseEnd_4743743] using wordTrace_append hprefix tailTrace_4743743
  have hstable : (prefixWord ++ tailWord_4743743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743743).length < 2 ^ (prefixWord ++ tailWord_4743743).sum := by decide
  have hdescent : baseEnd_4743743 < baseStart_4743743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743756 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4743756 : Nat := 118140960795 + 4743756 * 2 ^ 59
def prefixEnd_4743756 : Nat := 4983230072969 + 3 ^ 40 * 4743756 * 2
def baseEnd_4743756 : Nat := 2435826935649847266533869

theorem tailTrace_4743756 : CollatzResearch.WordTrace tailWord_4743756 prefixEnd_4743756 2435826935649847266533869 := by
  unfold tailWord_4743756
  simp only [CollatzResearch.WordTrace]
  refine ⟨86509497701094827934529561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115345996934793103912706081 86509497701094827934529561)
  ·
    refine ⟨64882123275821120950897171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86509497701094827934529561 64882123275821120950897171)
    ·
      refine ⟨97323184913731681426345757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64882123275821120950897171 97323184913731681426345757)
      ·
        refine ⟨36496194342649380534879659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97323184913731681426345757 36496194342649380534879659)
        ·
          refine ⟨54744291513974070802319489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36496194342649380534879659 54744291513974070802319489)
          ·
            refine ⟨41058218635480553101739617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54744291513974070802319489 41058218635480553101739617)
            ·
              refine ⟨30793663976610414826304713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41058218635480553101739617 30793663976610414826304713)
              ·
                refine ⟨23095247982457811119728535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30793663976610414826304713 23095247982457811119728535)
                ·
                  refine ⟨34642871973686716679592803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23095247982457811119728535 34642871973686716679592803)
                  ·
                    refine ⟨51964307960530075019389205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34642871973686716679592803 51964307960530075019389205)
                    ·
                      refine ⟨2435826935649847266533869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51964307960530075019389205 2435826935649847266533869)
                      ·
                        rfl

theorem cell23_4743756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4743756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743756 prefixEnd_4743756 := by exact prefixLift 4743756
  have htrace : WordTrace (prefixWord ++ tailWord_4743756) baseStart_4743756 baseEnd_4743756 := by
    simpa [prefixWord, tailWord_4743756, baseEnd_4743756] using wordTrace_append hprefix tailTrace_4743756
  have hstable : (prefixWord ++ tailWord_4743756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743756).length < 2 ^ (prefixWord ++ tailWord_4743756).sum := by decide
  have hdescent : baseEnd_4743756 < baseStart_4743756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743780 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_4743780 : Nat := 118140960795 + 4743780 * 2 ^ 59
def prefixEnd_4743780 : Nat := 4983230072969 + 3 ^ 40 * 4743780 * 2
def baseEnd_4743780 : Nat := 2435839259185555172633759

theorem tailTrace_4743780 : CollatzResearch.WordTrace tailWord_4743780 prefixEnd_4743780 2435839259185555172633759 := by
  unfold tailWord_4743780
  simp only [CollatzResearch.WordTrace]
  refine ⟨86509935377051353983966397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115346580502735138645288529 86509935377051353983966397)
  ·
    refine ⟨32441225766394257743987399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86509935377051353983966397 32441225766394257743987399)
    ·
      refine ⟨48661838649591386615981099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32441225766394257743987399 48661838649591386615981099)
      ·
        refine ⟨72992757974387079923971649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48661838649591386615981099 72992757974387079923971649)
        ·
          refine ⟨54744568480790309942978737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72992757974387079923971649 54744568480790309942978737)
          ·
            refine ⟨41058426360592732457234053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54744568480790309942978737 41058426360592732457234053)
            ·
              refine ⟨7698454942611137335731385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41058426360592732457234053 7698454942611137335731385)
              ·
                refine ⟨5773841206958353001798539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7698454942611137335731385 5773841206958353001798539)
                ·
                  refine ⟨8660761810437529502697809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773841206958353001798539 8660761810437529502697809)
                  ·
                    refine ⟨6495571357828147127023357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8660761810437529502697809 6495571357828147127023357)
                    ·
                      refine ⟨2435839259185555172633759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495571357828147127023357 2435839259185555172633759)
                      ·
                        rfl

theorem cell23_4743780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_4743780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743780 prefixEnd_4743780 := by exact prefixLift 4743780
  have htrace : WordTrace (prefixWord ++ tailWord_4743780) baseStart_4743780 baseEnd_4743780 := by
    simpa [prefixWord, tailWord_4743780, baseEnd_4743780] using wordTrace_append hprefix tailTrace_4743780
  have hstable : (prefixWord ++ tailWord_4743780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743780).length < 2 ^ (prefixWord ++ tailWord_4743780).sum := by decide
  have hdescent : baseEnd_4743780 < baseStart_4743780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743837 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_4743837 : Nat := 118140960795 + 4743837 * 2 ^ 59
def prefixEnd_4743837 : Nat := 4983230072969 + 3 ^ 40 * 4743837 * 2
def baseEnd_4743837 : Nat := 2435868527582861449620997

theorem tailTrace_4743837 : CollatzResearch.WordTrace tailWord_4743837 prefixEnd_4743837 2435868527582861449620997 := by
  unfold tailWord_4743837
  simp only [CollatzResearch.WordTrace]
  refine ⟨173021949714896206702757765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115347966476597471135171843 173021949714896206702757765)
  ·
    refine ⟨32441615571543038756767081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173021949714896206702757765 32441615571543038756767081)
    ·
      refine ⟨24331211678657279067575311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32441615571543038756767081 24331211678657279067575311)
      ·
        refine ⟨36496817517985918601362967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24331211678657279067575311 36496817517985918601362967)
        ·
          refine ⟨54745226276978877902044451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36496817517985918601362967 54745226276978877902044451)
          ·
            refine ⟨82117839415468316853066677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54745226276978877902044451 82117839415468316853066677)
            ·
              refine ⟨7698547445200154704975001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82117839415468316853066677 7698547445200154704975001)
              ·
                refine ⟨5773910583900116028731251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7698547445200154704975001 5773910583900116028731251)
                ·
                  refine ⟨8660865875850174043096877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773910583900116028731251 8660865875850174043096877)
                  ·
                    refine ⟨3247824703443815266161329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8660865875850174043096877 3247824703443815266161329)
                    ·
                      refine ⟨2435868527582861449620997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247824703443815266161329 2435868527582861449620997)
                      ·
                        rfl

theorem cell23_4743837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_4743837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743837 prefixEnd_4743837 := by exact prefixLift 4743837
  have htrace : WordTrace (prefixWord ++ tailWord_4743837) baseStart_4743837 baseEnd_4743837 := by
    simpa [prefixWord, tailWord_4743837, baseEnd_4743837] using wordTrace_append hprefix tailTrace_4743837
  have hstable : (prefixWord ++ tailWord_4743837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743837).length < 2 ^ (prefixWord ++ tailWord_4743837).sum := by decide
  have hdescent : baseEnd_4743837 < baseStart_4743837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
