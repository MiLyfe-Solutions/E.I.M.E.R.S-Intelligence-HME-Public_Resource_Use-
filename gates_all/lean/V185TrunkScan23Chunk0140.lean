import V185TrunkScan23Chunk0139

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_828695 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_828695 : Nat := 118140960795 + 828695 * 2 ^ 59
def prefixEnd_828695 : Nat := 4983230072969 + 3 ^ 40 * 828695 * 2
def baseEnd_828695 : Nat := 425518850977740460701407

theorem tailTrace_828695 : CollatzResearch.WordTrace tailWord_828695 prefixEnd_828695 425518850977740460701407 := by
  unfold tailWord_828695
  simp only [CollatzResearch.WordTrace]
  refine ⟨30224989732787019683343539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20149993155191346455562359 30224989732787019683343539)
  ·
    refine ⟨45337484599180529525015309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30224989732787019683343539 45337484599180529525015309)
    ·
      refine ⟨17001556724692698571880741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45337484599180529525015309 17001556724692698571880741)
      ·
        refine ⟨3187791885879880982227639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17001556724692698571880741 3187791885879880982227639)
        ·
          refine ⟨4781687828819821473341459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187791885879880982227639 4781687828819821473341459)
          ·
            refine ⟨7172531743229732210012189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781687828819821473341459 7172531743229732210012189)
            ·
              refine ⟨2689699403711149578754571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7172531743229732210012189 2689699403711149578754571)
              ·
                refine ⟨4034549105566724368131857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689699403711149578754571 4034549105566724368131857)
                ·
                  refine ⟨3025911829175043276098893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4034549105566724368131857 3025911829175043276098893)
                  ·
                    refine ⟨1134716935940641228537085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025911829175043276098893 1134716935940641228537085)
                    ·
                      refine ⟨425518850977740460701407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1134716935940641228537085 425518850977740460701407)
                      ·
                        rfl

theorem cell23_828695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_828695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828695 prefixEnd_828695 := by exact prefixLift 828695
  have htrace : WordTrace (prefixWord ++ tailWord_828695) baseStart_828695 baseEnd_828695 := by
    simpa [prefixWord, tailWord_828695, baseEnd_828695] using wordTrace_append hprefix tailTrace_828695
  have hstable : (prefixWord ++ tailWord_828695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828695).length < 2 ^ (prefixWord ++ tailWord_828695).sum := by decide
  have hdescent : baseEnd_828695 < baseStart_828695 := by decide
  rcases family_descends (prefixWord ++ tailWord_828695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828705 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_828705 : Nat := 118140960795 + 828705 * 2 ^ 59
def prefixEnd_828705 : Nat := 4983230072969 + 3 ^ 40 * 828705 * 2
def baseEnd_828705 : Nat := 425523985784285421576361

theorem tailTrace_828705 : CollatzResearch.WordTrace tailWord_828705 prefixEnd_828705 425523985784285421576361 := by
  unfold tailWord_828705
  simp only [CollatzResearch.WordTrace]
  refine ⟨30225354462750791391207569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20150236308500527594138379 30225354462750791391207569)
  ·
    refine ⟨22669015847063093543405677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30225354462750791391207569 22669015847063093543405677)
    ·
      refine ⟨8500880942648660078777129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22669015847063093543405677 8500880942648660078777129)
      ·
        refine ⟨6375660706986495059082847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8500880942648660078777129 6375660706986495059082847)
        ·
          refine ⟨9563491060479742588624271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375660706986495059082847 9563491060479742588624271)
          ·
            refine ⟨14345236590719613882936407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563491060479742588624271 14345236590719613882936407)
            ·
              refine ⟨21517854886079420824404611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345236590719613882936407 21517854886079420824404611)
              ·
                refine ⟨32276782329119131236606917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21517854886079420824404611 32276782329119131236606917)
                ·
                  refine ⟨6051896686709837106863797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32276782329119131236606917 6051896686709837106863797)
                  ·
                    refine ⟨567365314379047228768481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6051896686709837106863797 567365314379047228768481)
                    ·
                      refine ⟨425523985784285421576361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567365314379047228768481 425523985784285421576361)
                      ·
                        rfl

theorem cell23_828705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_828705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828705 prefixEnd_828705 := by exact prefixLift 828705
  have htrace : WordTrace (prefixWord ++ tailWord_828705) baseStart_828705 baseEnd_828705 := by
    simpa [prefixWord, tailWord_828705, baseEnd_828705] using wordTrace_append hprefix tailTrace_828705
  have hstable : (prefixWord ++ tailWord_828705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828705).length < 2 ^ (prefixWord ++ tailWord_828705).sum := by decide
  have hdescent : baseEnd_828705 < baseStart_828705 := by decide
  rcases family_descends (prefixWord ++ tailWord_828705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828745 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 3, 4]
def baseStart_828745 : Nat := 118140960795 + 828745 * 2 ^ 59
def prefixEnd_828745 : Nat := 4983230072969 + 3 ^ 40 * 828745 * 2
def baseEnd_828745 : Nat := 141848175003488421692059

theorem tailTrace_828745 : CollatzResearch.WordTrace tailWord_828745 prefixEnd_828745 141848175003488421692059 := by
  unfold tailWord_828745
  simp only [CollatzResearch.WordTrace]
  refine ⟨30226813382605878222663689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20151208921737252148442459 30226813382605878222663689)
  ·
    refine ⟨22670110036954408666997767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30226813382605878222663689 22670110036954408666997767)
    ·
      refine ⟨34005165055431613000496651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22670110036954408666997767 34005165055431613000496651)
      ·
        refine ⟨51007747583147419500744977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34005165055431613000496651 51007747583147419500744977)
        ·
          refine ⟨38255810687360564625558733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51007747583147419500744977 38255810687360564625558733)
          ·
            refine ⟨14345929007760211734584525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38255810687360564625558733 14345929007760211734584525)
            ·
              refine ⟨5379723377910079400469197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14345929007760211734584525 5379723377910079400469197)
              ·
                refine ⟨2017396266716279775175949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5379723377910079400469197 2017396266716279775175949)
                ·
                  refine ⟨756523600018604915690981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2017396266716279775175949 756523600018604915690981)
                  ·
                    refine ⟨141848175003488421692059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756523600018604915690981 141848175003488421692059)
                    ·
                      rfl

theorem cell23_828745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_828745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828745 prefixEnd_828745 := by exact prefixLift 828745
  have htrace : WordTrace (prefixWord ++ tailWord_828745) baseStart_828745 baseEnd_828745 := by
    simpa [prefixWord, tailWord_828745, baseEnd_828745] using wordTrace_append hprefix tailTrace_828745
  have hstable : (prefixWord ++ tailWord_828745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828745).length < 2 ^ (prefixWord ++ tailWord_828745).sum := by decide
  have hdescent : baseEnd_828745 < baseStart_828745 := by decide
  rcases family_descends (prefixWord ++ tailWord_828745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828789 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_828789 : Nat := 118140960795 + 828789 * 2 ^ 59
def prefixEnd_828789 : Nat := 4983230072969 + 3 ^ 40 * 828789 * 2
def baseEnd_828789 : Nat := 425567118159263092925975

theorem tailTrace_828789 : CollatzResearch.WordTrace tailWord_828789 prefixEnd_828789 425567118159263092925975 := by
  unfold tailWord_828789
  simp only [CollatzResearch.WordTrace]
  refine ⟨30228418194446473737265421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20152278796297649158176947 30228418194446473737265421)
  ·
    refine ⟨11335656822917427651474533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30228418194446473737265421 11335656822917427651474533)
    ·
      refine ⟨2125435654297017684651475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11335656822917427651474533 2125435654297017684651475)
      ·
        refine ⟨3188153481445526526977213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125435654297017684651475 3188153481445526526977213)
        ·
          refine ⟨1195557555542072447616455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3188153481445526526977213 1195557555542072447616455)
          ·
            refine ⟨1793336333313108671424683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195557555542072447616455 1793336333313108671424683)
            ·
              refine ⟨2690004499969663007137025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793336333313108671424683 2690004499969663007137025)
              ·
                refine ⟨2017503374977247255352769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690004499969663007137025 2017503374977247255352769)
                ·
                  refine ⟨1513127531232935441514577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017503374977247255352769 1513127531232935441514577)
                  ·
                    refine ⟨1134845648424701581135933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513127531232935441514577 1134845648424701581135933)
                    ·
                      refine ⟨425567118159263092925975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1134845648424701581135933 425567118159263092925975)
                      ·
                        rfl

theorem cell23_828789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_828789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828789 prefixEnd_828789 := by exact prefixLift 828789
  have htrace : WordTrace (prefixWord ++ tailWord_828789) baseStart_828789 baseEnd_828789 := by
    simpa [prefixWord, tailWord_828789, baseEnd_828789] using wordTrace_append hprefix tailTrace_828789
  have hstable : (prefixWord ++ tailWord_828789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828789).length < 2 ^ (prefixWord ++ tailWord_828789).sum := by decide
  have hdescent : baseEnd_828789 < baseStart_828789 := by decide
  rcases family_descends (prefixWord ++ tailWord_828789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828809 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 6]
def baseStart_828809 : Nat := 118140960795 + 828809 * 2 ^ 59
def prefixEnd_828809 : Nat := 4983230072969 + 3 ^ 40 * 828809 * 2
def baseEnd_828809 : Nat := 47286376419150334963987

theorem tailTrace_828809 : CollatzResearch.WordTrace tailWord_828809 prefixEnd_828809 47286376419150334963987 := by
  unfold tailWord_828809
  simp only [CollatzResearch.WordTrace]
  refine ⟨30229147654374017152993481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20152765102916011435328987 30229147654374017152993481)
  ·
    refine ⟨22671860740780512864745111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30229147654374017152993481 22671860740780512864745111)
    ·
      refine ⟨34007791111170769297117667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22671860740780512864745111 34007791111170769297117667)
      ·
        refine ⟨51011686666756153945676501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34007791111170769297117667 51011686666756153945676501)
        ·
          refine ⟨1195586406252097358101793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51011686666756153945676501 1195586406252097358101793)
          ·
            refine ⟨896689804689073018576345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1195586406252097358101793 896689804689073018576345)
            ·
              refine ⟨672517353516804763932259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896689804689073018576345 672517353516804763932259)
              ·
                refine ⟨1008776030275207145898389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672517353516804763932259 1008776030275207145898389)
                ·
                  refine ⟨47286376419150334963987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1008776030275207145898389 47286376419150334963987)
                  ·
                    rfl

theorem cell23_828809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 6].length) (baseStart_828809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828809 prefixEnd_828809 := by exact prefixLift 828809
  have htrace : WordTrace (prefixWord ++ tailWord_828809) baseStart_828809 baseEnd_828809 := by
    simpa [prefixWord, tailWord_828809, baseEnd_828809] using wordTrace_append hprefix tailTrace_828809
  have hstable : (prefixWord ++ tailWord_828809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828809).length < 2 ^ (prefixWord ++ tailWord_828809).sum := by decide
  have hdescent : baseEnd_828809 < baseStart_828809 := by decide
  rcases family_descends (prefixWord ++ tailWord_828809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828812 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 4, 3, 2]
def baseStart_828812 : Nat := 118140960795 + 828812 * 2 ^ 59
def prefixEnd_828812 : Nat := 4983230072969 + 3 ^ 40 * 828812 * 2
def baseEnd_828812 : Nat := 425578928214316502938369

theorem tailTrace_828812 : CollatzResearch.WordTrace tailWord_828812 prefixEnd_828812 425578928214316502938369 := by
  unfold tailWord_828812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114628536681574332676345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20152838048908765776901793 15114628536681574332676345)
  ·
    refine ⟨11335971402511180749507259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15114628536681574332676345 11335971402511180749507259)
    ·
      refine ⟨17003957103766771124260889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335971402511180749507259 17003957103766771124260889)
      ·
        refine ⟨12752967827825078343195667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17003957103766771124260889 12752967827825078343195667)
        ·
          refine ⟨19129451741737617514793501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752967827825078343195667 19129451741737617514793501)
          ·
            refine ⟨7173544403151606568047563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19129451741737617514793501 7173544403151606568047563)
            ·
              refine ⟨10760316604727409852071345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173544403151606568047563 10760316604727409852071345)
              ·
                refine ⟨8070237453545557389053509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10760316604727409852071345 8070237453545557389053509)
                ·
                  refine ⟨1513169522539792010447533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8070237453545557389053509 1513169522539792010447533)
                  ·
                    refine ⟨567438570952422003917825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513169522539792010447533 567438570952422003917825)
                    ·
                      refine ⟨425578928214316502938369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567438570952422003917825 425578928214316502938369)
                      ·
                        rfl

theorem cell23_828812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_828812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828812 prefixEnd_828812 := by exact prefixLift 828812
  have htrace : WordTrace (prefixWord ++ tailWord_828812) baseStart_828812 baseEnd_828812 := by
    simpa [prefixWord, tailWord_828812, baseEnd_828812] using wordTrace_append hprefix tailTrace_828812
  have hstable : (prefixWord ++ tailWord_828812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828812).length < 2 ^ (prefixWord ++ tailWord_828812).sum := by decide
  have hdescent : baseEnd_828812 < baseStart_828812 := by decide
  rcases family_descends (prefixWord ++ tailWord_828812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828829 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_828829 : Nat := 118140960795 + 828829 * 2 ^ 59
def prefixEnd_828829 : Nat := 4983230072969 + 3 ^ 40 * 828829 * 2
def baseEnd_828829 : Nat := 425587657385442936425791

theorem tailTrace_828829 : CollatzResearch.WordTrace tailWord_828829 prefixEnd_828829 425587657385442936425791 := by
  unfold tailWord_828829
  simp only [CollatzResearch.WordTrace]
  refine ⟨30229877114301560568721541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20153251409534373712481027 30229877114301560568721541)
  ·
    refine ⟨5668101958931542606635289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30229877114301560568721541 5668101958931542606635289)
    ·
      refine ⟨4251076469198656954976467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5668101958931542606635289 4251076469198656954976467)
      ·
        refine ⟨6376614703797985432464701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251076469198656954976467 6376614703797985432464701)
        ·
          refine ⟨2391230513924244537174263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6376614703797985432464701 2391230513924244537174263)
          ·
            refine ⟨3586845770886366805761395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391230513924244537174263 3586845770886366805761395)
            ·
              refine ⟨5380268656329550208642093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586845770886366805761395 5380268656329550208642093)
              ·
                refine ⟨2017600746123581328240785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5380268656329550208642093 2017600746123581328240785)
                ·
                  refine ⟨1513200559592685996180589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017600746123581328240785 1513200559592685996180589)
                  ·
                    refine ⟨567450209847257248567721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513200559592685996180589 567450209847257248567721)
                    ·
                      refine ⟨425587657385442936425791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567450209847257248567721 425587657385442936425791)
                      ·
                        rfl

theorem cell23_828829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_828829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828829 prefixEnd_828829 := by exact prefixLift 828829
  have htrace : WordTrace (prefixWord ++ tailWord_828829) baseStart_828829 baseEnd_828829 := by
    simpa [prefixWord, tailWord_828829, baseEnd_828829] using wordTrace_append hprefix tailTrace_828829
  have hstable : (prefixWord ++ tailWord_828829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828829).length < 2 ^ (prefixWord ++ tailWord_828829).sum := by decide
  have hdescent : baseEnd_828829 < baseStart_828829 := by decide
  rcases family_descends (prefixWord ++ tailWord_828829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828835 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 1, 6]
def baseStart_828835 : Nat := 118140960795 + 828835 * 2 ^ 59
def prefixEnd_828835 : Nat := 4983230072969 + 3 ^ 40 * 828835 * 2
def baseEnd_828835 : Nat := 141863579423123304316921

theorem tailTrace_828835 : CollatzResearch.WordTrace tailWord_828835 prefixEnd_828835 141863579423123304316921 := by
  unfold tailWord_828835
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230095952279823593439959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20153397301519882395626639 30230095952279823593439959)
  ·
    refine ⟨45345143928419735390159939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30230095952279823593439959 45345143928419735390159939)
    ·
      refine ⟨68017715892629603085239909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45345143928419735390159939 68017715892629603085239909)
      ·
        refine ⟨12753321729868050578482483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68017715892629603085239909 12753321729868050578482483)
        ·
          refine ⟨19129982594802075867723725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12753321729868050578482483 19129982594802075867723725)
          ·
            refine ⟨7173743473050778450396397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19129982594802075867723725 7173743473050778450396397)
            ·
              refine ⟨2690153802394041918898649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7173743473050778450396397 2690153802394041918898649)
              ·
                refine ⟨2017615351795531439173987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690153802394041918898649 2017615351795531439173987)
                ·
                  refine ⟨3026423027693297158760981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017615351795531439173987 3026423027693297158760981)
                  ·
                    refine ⟨141863579423123304316921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3026423027693297158760981 141863579423123304316921)
                    ·
                      rfl

theorem cell23_828835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 6].length) (baseStart_828835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828835 prefixEnd_828835 := by exact prefixLift 828835
  have htrace : WordTrace (prefixWord ++ tailWord_828835) baseStart_828835 baseEnd_828835 := by
    simpa [prefixWord, tailWord_828835, baseEnd_828835] using wordTrace_append hprefix tailTrace_828835
  have hstable : (prefixWord ++ tailWord_828835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828835).length < 2 ^ (prefixWord ++ tailWord_828835).sum := by decide
  have hdescent : baseEnd_828835 < baseStart_828835 := by decide
  rcases family_descends (prefixWord ++ tailWord_828835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828839 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 1, 5]
def baseStart_828839 : Nat := 118140960795 + 828839 * 2 ^ 59
def prefixEnd_828839 : Nat := 4983230072969 + 3 ^ 40 * 828839 * 2
def baseEnd_828839 : Nat := 141864264063995965766915

theorem tailTrace_828839 : CollatzResearch.WordTrace tailWord_828839 prefixEnd_828839 141864264063995965766915 := by
  unfold tailWord_828839
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230241844265332276585571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20153494562843554851057047 30230241844265332276585571)
  ·
    refine ⟨45345362766397998414878357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30230241844265332276585571 45345362766397998414878357)
    ·
      refine ⟨2125563879674906175697423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45345362766397998414878357 2125563879674906175697423)
      ·
        refine ⟨3188345819512359263546135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125563879674906175697423 3188345819512359263546135)
        ·
          refine ⟨4782518729268538895319203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188345819512359263546135 4782518729268538895319203)
          ·
            refine ⟨7173778093902808342978805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782518729268538895319203 7173778093902808342978805)
            ·
              refine ⟨672541696303388282154263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7173778093902808342978805 672541696303388282154263)
              ·
                refine ⟨1008812544455082423231395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672541696303388282154263 1008812544455082423231395)
                ·
                  refine ⟨1513218816682623634847093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008812544455082423231395 1513218816682623634847093)
                  ·
                    refine ⟨141864264063995965766915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1513218816682623634847093 141864264063995965766915)
                    ·
                      rfl

theorem cell23_828839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_828839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828839 prefixEnd_828839 := by exact prefixLift 828839
  have htrace : WordTrace (prefixWord ++ tailWord_828839) baseStart_828839 baseEnd_828839 := by
    simpa [prefixWord, tailWord_828839, baseEnd_828839] using wordTrace_append hprefix tailTrace_828839
  have hstable : (prefixWord ++ tailWord_828839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828839).length < 2 ^ (prefixWord ++ tailWord_828839).sum := by decide
  have hdescent : baseEnd_828839 < baseStart_828839 := by decide
  rcases family_descends (prefixWord ++ tailWord_828839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828853 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_828853 : Nat := 118140960795 + 828853 * 2 ^ 59
def prefixEnd_828853 : Nat := 4983230072969 + 3 ^ 40 * 828853 * 2
def baseEnd_828853 : Nat := 425599980921150842525681

theorem tailTrace_828853 : CollatzResearch.WordTrace tailWord_828853 prefixEnd_828853 425599980921150842525681 := by
  unfold tailWord_828853
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230752466214612667595213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20153834977476408445063475 30230752466214612667595213)
  ·
    refine ⟨11336532174830479750348205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30230752466214612667595213 11336532174830479750348205)
    ·
      refine ⟨4251199565561429906380577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11336532174830479750348205 4251199565561429906380577)
      ·
        refine ⟨3188399674171072429785433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4251199565561429906380577 3188399674171072429785433)
        ·
          refine ⟨2391299755628304322339075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3188399674171072429785433 2391299755628304322339075)
          ·
            refine ⟨3586949633442456483508613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391299755628304322339075 3586949633442456483508613)
            ·
              refine ⟨672553056270460590657865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3586949633442456483508613 672553056270460590657865)
              ·
                refine ⟨504414792202845442993399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672553056270460590657865 504414792202845442993399)
                ·
                  refine ⟨756622188304268164490099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504414792202845442993399 756622188304268164490099)
                  ·
                    refine ⟨1134933282456402246735149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756622188304268164490099 1134933282456402246735149)
                    ·
                      refine ⟨425599980921150842525681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1134933282456402246735149 425599980921150842525681)
                      ·
                        rfl

theorem cell23_828853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_828853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828853 prefixEnd_828853 := by exact prefixLift 828853
  have htrace : WordTrace (prefixWord ++ tailWord_828853) baseStart_828853 baseEnd_828853 := by
    simpa [prefixWord, tailWord_828853, baseEnd_828853] using wordTrace_append hprefix tailTrace_828853
  have hstable : (prefixWord ++ tailWord_828853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828853).length < 2 ^ (prefixWord ++ tailWord_828853).sum := by decide
  have hdescent : baseEnd_828853 < baseStart_828853 := by decide
  rcases family_descends (prefixWord ++ tailWord_828853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828855 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_828855 : Nat := 118140960795 + 828855 * 2 ^ 59
def prefixEnd_828855 : Nat := 4983230072969 + 3 ^ 40 * 828855 * 2
def baseEnd_828855 : Nat := 425601007882459834700671

theorem tailTrace_828855 : CollatzResearch.WordTrace tailWord_828855 prefixEnd_828855 425601007882459834700671 := by
  unfold tailWord_828855
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230825412207367009168019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20153883608138244672778679 30230825412207367009168019)
  ·
    refine ⟨45346238118311050513752029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30230825412207367009168019 45346238118311050513752029)
    ·
      refine ⟨17004839294366643942657011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45346238118311050513752029 17004839294366643942657011)
      ·
        refine ⟨25507258941549965913985517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17004839294366643942657011 25507258941549965913985517)
        ·
          refine ⟨9565222103081237217744569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25507258941549965913985517 9565222103081237217744569)
          ·
            refine ⟨7173916577310927913308427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9565222103081237217744569 7173916577310927913308427)
            ·
              refine ⟨10760874865966391869962641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173916577310927913308427 10760874865966391869962641)
              ·
                refine ⟨8070656149474793902471981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10760874865966391869962641 8070656149474793902471981)
                ·
                  refine ⟨3026496056053047713426993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8070656149474793902471981 3026496056053047713426993)
                  ·
                    refine ⟨2269872042039785785070245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026496056053047713426993 2269872042039785785070245)
                    ·
                      refine ⟨425601007882459834700671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2269872042039785785070245 425601007882459834700671)
                      ·
                        rfl

theorem cell23_828855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_828855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828855 prefixEnd_828855 := by exact prefixLift 828855
  have htrace : WordTrace (prefixWord ++ tailWord_828855) baseStart_828855 baseEnd_828855 := by
    simpa [prefixWord, tailWord_828855, baseEnd_828855] using wordTrace_append hprefix tailTrace_828855
  have hstable : (prefixWord ++ tailWord_828855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828855).length < 2 ^ (prefixWord ++ tailWord_828855).sum := by decide
  have hdescent : baseEnd_828855 < baseStart_828855 := by decide
  rcases family_descends (prefixWord ++ tailWord_828855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828872 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_828872 : Nat := 118140960795 + 828872 * 2 ^ 59
def prefixEnd_828872 : Nat := 4983230072969 + 3 ^ 40 * 828872 * 2
def baseEnd_828872 : Nat := 425609737053586268188093

theorem tailTrace_828872 : CollatzResearch.WordTrace tailWord_828872 prefixEnd_828872 425609737053586268188093 := by
  unfold tailWord_828872
  simp only [CollatzResearch.WordTrace]
  refine ⟨15115722726572889456268435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20154296968763852608357913 15115722726572889456268435)
  ·
    refine ⟨22673584089859334184402653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15115722726572889456268435 22673584089859334184402653)
    ·
      refine ⟨8502594033697250319150995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22673584089859334184402653 8502594033697250319150995)
      ·
        refine ⟨12753891050545875478726493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502594033697250319150995 12753891050545875478726493)
        ·
          refine ⟨4782709143954703304522435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12753891050545875478726493 4782709143954703304522435)
          ·
            refine ⟨7174063715932054956783653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782709143954703304522435 7174063715932054956783653)
            ·
              refine ⟨1345136946737260304396935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7174063715932054956783653 1345136946737260304396935)
              ·
                refine ⟨2017705420105890456595403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345136946737260304396935 2017705420105890456595403)
                ·
                  refine ⟨3026558130158835684893105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017705420105890456595403 3026558130158835684893105)
                  ·
                    refine ⟨2269918597619126763669829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026558130158835684893105 2269918597619126763669829)
                    ·
                      refine ⟨425609737053586268188093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2269918597619126763669829 425609737053586268188093)
                      ·
                        rfl

theorem cell23_828872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_828872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828872 prefixEnd_828872 := by exact prefixLift 828872
  have htrace : WordTrace (prefixWord ++ tailWord_828872) baseStart_828872 baseEnd_828872 := by
    simpa [prefixWord, tailWord_828872, baseEnd_828872] using wordTrace_append hprefix tailTrace_828872
  have hstable : (prefixWord ++ tailWord_828872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828872).length < 2 ^ (prefixWord ++ tailWord_828872).sum := by decide
  have hdescent : baseEnd_828872 < baseStart_828872 := by decide
  rcases family_descends (prefixWord ++ tailWord_828872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828876 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 3, 2, 2]
def baseStart_828876 : Nat := 118140960795 + 828876 * 2 ^ 59
def prefixEnd_828876 : Nat := 4983230072969 + 3 ^ 40 * 828876 * 2
def baseEnd_828876 : Nat := 425611790976204252538075

theorem tailTrace_828876 : CollatzResearch.WordTrace tailWord_828876 prefixEnd_828876 425611790976204252538075 := by
  unfold tailWord_828876
  simp only [CollatzResearch.WordTrace]
  refine ⟨15115795672565643797841241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20154394230087525063788321 15115795672565643797841241)
  ·
    refine ⟨11336846754424232848380931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15115795672565643797841241 11336846754424232848380931)
    ·
      refine ⟨17005270131636349272571397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11336846754424232848380931 17005270131636349272571397)
      ·
        refine ⟨3188488149681815488607137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17005270131636349272571397 3188488149681815488607137)
        ·
          refine ⟨2391366112261361616455353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3188488149681815488607137 2391366112261361616455353)
          ·
            refine ⟨1793524584196021212341515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391366112261361616455353 1793524584196021212341515)
            ·
              refine ⟨2690286876294031818512273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793524584196021212341515 2690286876294031818512273)
              ·
                refine ⟨2017715157220523863884205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690286876294031818512273 2017715157220523863884205)
                ·
                  refine ⟨756643183957696448956577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2017715157220523863884205 756643183957696448956577)
                  ·
                    refine ⟨567482387968272336717433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756643183957696448956577 567482387968272336717433)
                    ·
                      refine ⟨425611790976204252538075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567482387968272336717433 425611790976204252538075)
                      ·
                        rfl

theorem cell23_828876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_828876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828876 prefixEnd_828876 := by exact prefixLift 828876
  have htrace : WordTrace (prefixWord ++ tailWord_828876) baseStart_828876 baseEnd_828876 := by
    simpa [prefixWord, tailWord_828876, baseEnd_828876] using wordTrace_append hprefix tailTrace_828876
  have hstable : (prefixWord ++ tailWord_828876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828876).length < 2 ^ (prefixWord ++ tailWord_828876).sum := by decide
  have hdescent : baseEnd_828876 < baseStart_828876 := by decide
  rcases family_descends (prefixWord ++ tailWord_828876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828893 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_828893 : Nat := 118140960795 + 828893 * 2 ^ 59
def prefixEnd_828893 : Nat := 4983230072969 + 3 ^ 40 * 828893 * 2
def baseEnd_828893 : Nat := 425620520147330686025497

theorem tailTrace_828893 : CollatzResearch.WordTrace tailWord_828893 prefixEnd_828893 425620520147330686025497 := by
  unfold tailWord_828893
  simp only [CollatzResearch.WordTrace]
  refine ⟨30232211386069699499051333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20154807590713132999367555 30232211386069699499051333)
  ·
    refine ⟨5668539634888068656072125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30232211386069699499051333 5668539634888068656072125)
    ·
      refine ⟨2125702363083025746027047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5668539634888068656072125 2125702363083025746027047)
      ·
        refine ⟨3188553544624538619040571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125702363083025746027047 3188553544624538619040571)
        ·
          refine ⟨4782830316936807928560857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188553544624538619040571 4782830316936807928560857)
          ·
            refine ⟨3587122737702605946420643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782830316936807928560857 3587122737702605946420643)
            ·
              refine ⟨5380684106553908919630965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587122737702605946420643 5380684106553908919630965)
              ·
                refine ⟨504439134989428961215403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5380684106553908919630965 504439134989428961215403)
                ·
                  refine ⟨756658702484143441823105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504439134989428961215403 756658702484143441823105)
                  ·
                    refine ⟨567494026863107581367329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756658702484143441823105 567494026863107581367329)
                    ·
                      refine ⟨425620520147330686025497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567494026863107581367329 425620520147330686025497)
                      ·
                        rfl

theorem cell23_828893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_828893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828893 prefixEnd_828893 := by exact prefixLift 828893
  have htrace : WordTrace (prefixWord ++ tailWord_828893) baseStart_828893 baseEnd_828893 := by
    simpa [prefixWord, tailWord_828893, baseEnd_828893] using wordTrace_append hprefix tailTrace_828893
  have hstable : (prefixWord ++ tailWord_828893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828893).length < 2 ^ (prefixWord ++ tailWord_828893).sum := by decide
  have hdescent : baseEnd_828893 < baseStart_828893 := by decide
  rcases family_descends (prefixWord ++ tailWord_828893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828915 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4]
def baseStart_828915 : Nat := 118140960795 + 828915 * 2 ^ 59
def prefixEnd_828915 : Nat := 4983230072969 + 3 ^ 40 * 828915 * 2
def baseEnd_828915 : Nat := 425631816721729599950395

theorem tailTrace_828915 : CollatzResearch.WordTrace tailWord_828915 prefixEnd_828915 425631816721729599950395 := by
  unfold tailWord_828915
  simp only [CollatzResearch.WordTrace]
  refine ⟨30233013791989997256352199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20155342527993331504234799 30233013791989997256352199)
  ·
    refine ⟨45349520687984995884528299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30233013791989997256352199 45349520687984995884528299)
    ·
      refine ⟨68024281031977493826792449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45349520687984995884528299 68024281031977493826792449)
      ·
        refine ⟨51018210773983120370094337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68024281031977493826792449 51018210773983120370094337)
        ·
          refine ⟨38263658080487340277570753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51018210773983120370094337 38263658080487340277570753)
          ·
            refine ⟨28697743560365505208178065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38263658080487340277570753 28697743560365505208178065)
            ·
              refine ⟨21523307670274128906133549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28697743560365505208178065 21523307670274128906133549)
              ·
                refine ⟨8071240376352798339800081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21523307670274128906133549 8071240376352798339800081)
                ·
                  refine ⟨6053430282264598754850061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8071240376352798339800081 6053430282264598754850061)
                  ·
                    refine ⟨2270036355849224533068773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6053430282264598754850061 2270036355849224533068773)
                    ·
                      refine ⟨425631816721729599950395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2270036355849224533068773 425631816721729599950395)
                      ·
                        rfl

theorem cell23_828915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_828915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828915 prefixEnd_828915 := by exact prefixLift 828915
  have htrace : WordTrace (prefixWord ++ tailWord_828915) baseStart_828915 baseEnd_828915 := by
    simpa [prefixWord, tailWord_828915, baseEnd_828915] using wordTrace_append hprefix tailTrace_828915
  have hstable : (prefixWord ++ tailWord_828915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828915).length < 2 ^ (prefixWord ++ tailWord_828915).sum := by decide
  have hdescent : baseEnd_828915 < baseStart_828915 := by decide
  rcases family_descends (prefixWord ++ tailWord_828915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828962 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_828962 : Nat := 118140960795 + 828962 * 2 ^ 59
def prefixEnd_828962 : Nat := 4983230072969 + 3 ^ 40 * 828962 * 2
def baseEnd_828962 : Nat := 425655950312490916062679

theorem tailTrace_828962 : CollatzResearch.WordTrace tailWord_828962 prefixEnd_828962 425655950312490916062679 := by
  unfold tailWord_828962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558682005704931070828285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20156485348546482855542093 7558682005704931070828285)
  ·
    refine ⟨2834505752139349151560607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7558682005704931070828285 2834505752139349151560607)
    ·
      refine ⟨4251758628209023727340911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834505752139349151560607 4251758628209023727340911)
      ·
        refine ⟨6377637942313535591011367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251758628209023727340911 6377637942313535591011367)
        ·
          refine ⟨9566456913470303386517051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6377637942313535591011367 9566456913470303386517051)
          ·
            refine ⟨14349685370205455079775577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566456913470303386517051 14349685370205455079775577)
            ·
              refine ⟨10762264027654091309831683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14349685370205455079775577 10762264027654091309831683)
              ·
                refine ⟨16143396041481136964747525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10762264027654091309831683 16143396041481136964747525)
                ·
                  refine ⟨3026886757777713180890161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16143396041481136964747525 3026886757777713180890161)
                  ·
                    refine ⟨2270165068333284885667621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026886757777713180890161 2270165068333284885667621)
                    ·
                      refine ⟨425655950312490916062679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2270165068333284885667621 425655950312490916062679)
                      ·
                        rfl

theorem cell23_828962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_828962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828962 prefixEnd_828962 := by exact prefixLift 828962
  have htrace : WordTrace (prefixWord ++ tailWord_828962) baseStart_828962 baseEnd_828962 := by
    simpa [prefixWord, tailWord_828962, baseEnd_828962] using wordTrace_append hprefix tailTrace_828962
  have hstable : (prefixWord ++ tailWord_828962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828962).length < 2 ^ (prefixWord ++ tailWord_828962).sum := by decide
  have hdescent : baseEnd_828962 < baseStart_828962 := by decide
  rcases family_descends (prefixWord ++ tailWord_828962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828965 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_828965 : Nat := 118140960795 + 828965 * 2 ^ 59
def prefixEnd_828965 : Nat := 4983230072969 + 3 ^ 40 * 828965 * 2
def baseEnd_828965 : Nat := 425657490754454404325165

theorem tailTrace_828965 : CollatzResearch.WordTrace tailWord_828965 prefixEnd_828965 425657490754454404325165 := by
  unfold tailWord_828965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30234837441808855795672349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20156558294539237197114899 30234837441808855795672349)
  ·
    refine ⟨11338064040678320923377131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30234837441808855795672349 11338064040678320923377131)
    ·
      refine ⟨17007096061017481385065697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11338064040678320923377131 17007096061017481385065697)
      ·
        refine ⟨12755322045763111038799273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17007096061017481385065697 12755322045763111038799273)
        ·
          refine ⟨9566491534322333279099455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12755322045763111038799273 9566491534322333279099455)
          ·
            refine ⟨14349737301483499918649183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566491534322333279099455 14349737301483499918649183)
            ·
              refine ⟨21524605952225249877973775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14349737301483499918649183 21524605952225249877973775)
              ·
                refine ⟨32286908928337874816960663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21524605952225249877973775 32286908928337874816960663)
                ·
                  refine ⟨48430363392506812225440995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32286908928337874816960663 48430363392506812225440995)
                  ·
                    refine ⟨72645545088760218338161493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48430363392506812225440995 72645545088760218338161493)
                    ·
                      refine ⟨425657490754454404325165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 72645545088760218338161493 425657490754454404325165)
                      ·
                        rfl

theorem cell23_828965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_828965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828965 prefixEnd_828965 := by exact prefixLift 828965
  have htrace : WordTrace (prefixWord ++ tailWord_828965) baseStart_828965 baseEnd_828965 := by
    simpa [prefixWord, tailWord_828965, baseEnd_828965] using wordTrace_append hprefix tailTrace_828965
  have hstable : (prefixWord ++ tailWord_828965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828965).length < 2 ^ (prefixWord ++ tailWord_828965).sum := by decide
  have hdescent : baseEnd_828965 < baseStart_828965 := by decide
  rcases family_descends (prefixWord ++ tailWord_828965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828983 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 2, 2, 2]
def baseStart_828983 : Nat := 118140960795 + 828983 * 2 ^ 59
def prefixEnd_828983 : Nat := 4983230072969 + 3 ^ 40 * 828983 * 2
def baseEnd_828983 : Nat := 425666733406235333900083

theorem tailTrace_828983 : CollatzResearch.WordTrace tailWord_828983 prefixEnd_828983 425666733406235333900083 := by
  unfold tailWord_828983
  simp only [CollatzResearch.WordTrace]
  refine ⟨30235493955743644869827603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20156995970495763246551735 30235493955743644869827603)
  ·
    refine ⟨45353240933615467304741405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30235493955743644869827603 45353240933615467304741405)
    ·
      refine ⟨17007465350105800239278027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45353240933615467304741405 17007465350105800239278027)
      ·
        refine ⟨25511198025158700358917041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17007465350105800239278027 25511198025158700358917041)
        ·
          refine ⟨19133398518869025269187781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25511198025158700358917041 19133398518869025269187781)
          ·
            refine ⟨3587512222287942237972709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19133398518869025269187781 3587512222287942237972709)
            ·
              refine ⟨672658541678989169619883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3587512222287942237972709 672658541678989169619883)
              ·
                refine ⟨1008987812518483754429825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672658541678989169619883 1008987812518483754429825)
                ·
                  refine ⟨756740859388862815822369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1008987812518483754429825 756740859388862815822369)
                  ·
                    refine ⟨567555644541647111866777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756740859388862815822369 567555644541647111866777)
                    ·
                      refine ⟨425666733406235333900083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567555644541647111866777 425666733406235333900083)
                      ·
                        rfl

theorem cell23_828983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_828983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828983 prefixEnd_828983 := by exact prefixLift 828983
  have htrace : WordTrace (prefixWord ++ tailWord_828983) baseStart_828983 baseEnd_828983 := by
    simpa [prefixWord, tailWord_828983, baseEnd_828983] using wordTrace_append hprefix tailTrace_828983
  have hstable : (prefixWord ++ tailWord_828983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828983).length < 2 ^ (prefixWord ++ tailWord_828983).sum := by decide
  have hdescent : baseEnd_828983 < baseStart_828983 := by decide
  rcases family_descends (prefixWord ++ tailWord_828983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829012 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_829012 : Nat := 118140960795 + 829012 * 2 ^ 59
def prefixEnd_829012 : Nat := 4983230072969 + 3 ^ 40 * 829012 * 2
def baseEnd_829012 : Nat := 425681624345215720437449

theorem tailTrace_829012 : CollatzResearch.WordTrace tailWord_829012 prefixEnd_829012 425681624345215720437449 := by
  unfold tailWord_829012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118275836319291411316645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20157701115092388548422193 15118275836319291411316645)
  ·
    refine ⟨2834676719309867139621871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15118275836319291411316645 2834676719309867139621871)
    ·
      refine ⟨4252015078964800709432807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834676719309867139621871 4252015078964800709432807)
      ·
        refine ⟨6378022618447201064149211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252015078964800709432807 6378022618447201064149211)
        ·
          refine ⟨9567033927670801596223817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378022618447201064149211 9567033927670801596223817)
          ·
            refine ⟨7175275445753101197167863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9567033927670801596223817 7175275445753101197167863)
            ·
              refine ⟨10762913168629651795751795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7175275445753101197167863 10762913168629651795751795)
              ·
                refine ⟨16144369752944477693627693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10762913168629651795751795 16144369752944477693627693)
                ·
                  refine ⟨6054138657354179135110385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16144369752944477693627693 6054138657354179135110385)
                  ·
                    refine ⟨4540603993015634351332789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6054138657354179135110385 4540603993015634351332789)
                    ·
                      refine ⟨425681624345215720437449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4540603993015634351332789 425681624345215720437449)
                      ·
                        rfl

theorem cell23_829012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_829012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829012 prefixEnd_829012 := by exact prefixLift 829012
  have htrace : WordTrace (prefixWord ++ tailWord_829012) baseStart_829012 baseEnd_829012 := by
    simpa [prefixWord, tailWord_829012, baseEnd_829012] using wordTrace_append hprefix tailTrace_829012
  have hstable : (prefixWord ++ tailWord_829012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829012).length < 2 ^ (prefixWord ++ tailWord_829012).sum := by decide
  have hdescent : baseEnd_829012 < baseStart_829012 := by decide
  rcases family_descends (prefixWord ++ tailWord_829012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829049 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 3, 4]
def baseStart_829049 : Nat := 118140960795 + 829049 * 2 ^ 59
def prefixEnd_829049 : Nat := 4983230072969 + 3 ^ 40 * 829049 * 2
def baseEnd_829049 : Nat := 141900207709810691891593

theorem tailTrace_829049 : CollatzResearch.WordTrace tailWord_829049 prefixEnd_829049 141900207709810691891593 := by
  unfold tailWord_829049
  simp only [CollatzResearch.WordTrace]
  refine ⟨30237901173504538141730201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20158600782336358761153467 30237901173504538141730201)
  ·
    refine ⟨22678425880128403606297651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30237901173504538141730201 22678425880128403606297651)
    ·
      refine ⟨34017638820192605409446477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22678425880128403606297651 34017638820192605409446477)
      ·
        refine ⟨12756614557572227028542429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34017638820192605409446477 12756614557572227028542429)
        ·
          refine ⟨4783730459089585135703411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12756614557572227028542429 4783730459089585135703411)
          ·
            refine ⟨7175595688634377703555117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4783730459089585135703411 7175595688634377703555117)
            ·
              refine ⟨2690848383237891638833169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7175595688634377703555117 2690848383237891638833169)
              ·
                refine ⟨2018136287428418729124877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690848383237891638833169 2018136287428418729124877)
                ·
                  refine ⟨756801107785657023421829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2018136287428418729124877 756801107785657023421829)
                  ·
                    refine ⟨141900207709810691891593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756801107785657023421829 141900207709810691891593)
                    ·
                      rfl

theorem cell23_829049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_829049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829049 prefixEnd_829049 := by exact prefixLift 829049
  have htrace : WordTrace (prefixWord ++ tailWord_829049) baseStart_829049 baseEnd_829049 := by
    simpa [prefixWord, tailWord_829049, baseEnd_829049] using wordTrace_append hprefix tailTrace_829049
  have hstable : (prefixWord ++ tailWord_829049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829049).length < 2 ^ (prefixWord ++ tailWord_829049).sum := by decide
  have hdescent : baseEnd_829049 < baseStart_829049 := by decide
  rcases family_descends (prefixWord ++ tailWord_829049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829072 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_829072 : Nat := 118140960795 + 829072 * 2 ^ 59
def prefixEnd_829072 : Nat := 4983230072969 + 3 ^ 40 * 829072 * 2
def baseEnd_829072 : Nat := 425712433184485485687173

theorem tailTrace_829072 : CollatzResearch.WordTrace tailWord_829072 prefixEnd_829072 425712433184485485687173 := by
  unfold tailWord_829072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15119370026210606534908735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20159160034947475379878313 15119370026210606534908735)
  ·
    refine ⟨22679055039315909802363103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15119370026210606534908735 22679055039315909802363103)
    ·
      refine ⟨34018582558973864703544655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22679055039315909802363103 34018582558973864703544655)
      ·
        refine ⟨51027873838460797055316983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34018582558973864703544655 51027873838460797055316983)
        ·
          refine ⟨76541810757691195582975475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51027873838460797055316983 76541810757691195582975475)
          ·
            refine ⟨114812716136536793374463213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76541810757691195582975475 114812716136536793374463213)
            ·
              refine ⟨43054768551201297515423705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114812716136536793374463213 43054768551201297515423705)
              ·
                refine ⟨32291076413400973136567779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43054768551201297515423705 32291076413400973136567779)
                ·
                  refine ⟨48436614620101459704851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32291076413400973136567779 48436614620101459704851669)
                  ·
                    refine ⟨1135233155158627961832461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48436614620101459704851669 1135233155158627961832461)
                    ·
                      refine ⟨425712433184485485687173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135233155158627961832461 425712433184485485687173)
                      ·
                        rfl

theorem cell23_829072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_829072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829072 prefixEnd_829072 := by exact prefixLift 829072
  have htrace : WordTrace (prefixWord ++ tailWord_829072) baseStart_829072 baseEnd_829072 := by
    simpa [prefixWord, tailWord_829072, baseEnd_829072] using wordTrace_append hprefix tailTrace_829072
  have hstable : (prefixWord ++ tailWord_829072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829072).length < 2 ^ (prefixWord ++ tailWord_829072).sum := by decide
  have hdescent : baseEnd_829072 < baseStart_829072 := by decide
  rcases family_descends (prefixWord ++ tailWord_829072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829079 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 6]
def baseStart_829079 : Nat := 118140960795 + 829079 * 2 ^ 59
def prefixEnd_829079 : Nat := 4983230072969 + 3 ^ 40 * 829079 * 2
def baseEnd_829079 : Nat := 47301780838785217588849

theorem tailTrace_829079 : CollatzResearch.WordTrace tailWord_829079 prefixEnd_829079 47301780838785217588849 := by
  unfold tailWord_829079
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238995363395853265322291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20159330242263902176881527 30238995363395853265322291)
  ·
    refine ⟨45358493045093779897983437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30238995363395853265322291 45358493045093779897983437)
    ·
      refine ⟨17009434891910167461743789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45358493045093779897983437 17009434891910167461743789)
      ·
        refine ⟨6378538084466312798153921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17009434891910167461743789 6378538084466312798153921)
        ·
          refine ⟨4783903563349734598615441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6378538084466312798153921 4783903563349734598615441)
          ·
            refine ⟨3587927672512300948961581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783903563349734598615441 3587927672512300948961581)
            ·
              refine ⟨1345472877192112855860593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3587927672512300948961581 1345472877192112855860593)
              ·
                refine ⟨1009104657894084641895445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345472877192112855860593 1009104657894084641895445)
                ·
                  refine ⟨47301780838785217588849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1009104657894084641895445 47301780838785217588849)
                  ·
                    rfl

theorem cell23_829079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 6].length) (baseStart_829079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829079 prefixEnd_829079 := by exact prefixLift 829079
  have htrace : WordTrace (prefixWord ++ tailWord_829079) baseStart_829079 baseEnd_829079 := by
    simpa [prefixWord, tailWord_829079, baseEnd_829079] using wordTrace_append hprefix tailTrace_829079
  have hstable : (prefixWord ++ tailWord_829079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829079).length < 2 ^ (prefixWord ++ tailWord_829079).sum := by decide
  have hdescent : baseEnd_829079 < baseStart_829079 := by decide
  rcases family_descends (prefixWord ++ tailWord_829079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829106 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_829106 : Nat := 118140960795 + 829106 * 2 ^ 59
def prefixEnd_829106 : Nat := 4983230072969 + 3 ^ 40 * 829106 * 2
def baseEnd_829106 : Nat := 425729891526738352662017

theorem tailTrace_829106 : CollatzResearch.WordTrace tailWord_829106 prefixEnd_829106 425729891526738352662017 := by
  unfold tailWord_829106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559995033574509219138793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20159986756198691251036781 7559995033574509219138793)
  ·
    refine ⟨5669996275180881914354095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7559995033574509219138793 5669996275180881914354095)
    ·
      refine ⟨8504994412771322871531143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5669996275180881914354095 8504994412771322871531143)
      ·
        refine ⟨12757491619156984307296715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8504994412771322871531143 12757491619156984307296715)
        ·
          refine ⟨19136237428735476460945073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757491619156984307296715 19136237428735476460945073)
          ·
            refine ⟨14352178071551607345708805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19136237428735476460945073 14352178071551607345708805)
            ·
              refine ⟨2691033388415926377320401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14352178071551607345708805 2691033388415926377320401)
              ·
                refine ⟨2018275041311944782990301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2691033388415926377320401 2018275041311944782990301)
                ·
                  refine ⟨756853140491979293621363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2018275041311944782990301 756853140491979293621363)
                  ·
                    refine ⟨1135279710737968940432045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756853140491979293621363 1135279710737968940432045)
                    ·
                      refine ⟨425729891526738352662017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135279710737968940432045 425729891526738352662017)
                      ·
                        rfl

theorem cell23_829106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_829106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829106 prefixEnd_829106 := by exact prefixLift 829106
  have htrace : WordTrace (prefixWord ++ tailWord_829106) baseStart_829106 baseEnd_829106 := by
    simpa [prefixWord, tailWord_829106, baseEnd_829106] using wordTrace_append hprefix tailTrace_829106
  have hstable : (prefixWord ++ tailWord_829106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829106).length < 2 ^ (prefixWord ++ tailWord_829106).sum := by decide
  have hdescent : baseEnd_829106 < baseStart_829106 := by decide
  rcases family_descends (prefixWord ++ tailWord_829106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829112 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_829112 : Nat := 118140960795 + 829112 * 2 ^ 59
def prefixEnd_829112 : Nat := 4983230072969 + 3 ^ 40 * 829112 * 2
def baseEnd_829112 : Nat := 425732972410665329186989

theorem tailTrace_829112 : CollatzResearch.WordTrace tailWord_829112 prefixEnd_829112 425732972410665329186989 := by
  unfold tailWord_829112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120099486138149950636795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20160132648184199934182393 15120099486138149950636795)
  ·
    refine ⟨22680149229207224925955193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15120099486138149950636795 22680149229207224925955193)
    ·
      refine ⟨17010111921905418694466395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22680149229207224925955193 17010111921905418694466395)
      ·
        refine ⟨25515167882858128041699593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17010111921905418694466395 25515167882858128041699593)
        ·
          refine ⟨19136375912143596031274695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25515167882858128041699593 19136375912143596031274695)
          ·
            refine ⟨28704563868215394046912043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19136375912143596031274695 28704563868215394046912043)
            ·
              refine ⟨43056845802323091070368065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28704563868215394046912043 43056845802323091070368065)
              ·
                refine ⟨32292634351742318302776049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43056845802323091070368065 32292634351742318302776049)
                ·
                  refine ⟨24219475763806738727082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32292634351742318302776049 24219475763806738727082037)
                  ·
                    refine ⟨2270575852856881755663941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24219475763806738727082037 2270575852856881755663941)
                    ·
                      refine ⟨425732972410665329186989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2270575852856881755663941 425732972410665329186989)
                      ·
                        rfl

theorem cell23_829112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_829112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829112 prefixEnd_829112 := by exact prefixLift 829112
  have htrace : WordTrace (prefixWord ++ tailWord_829112) baseStart_829112 baseEnd_829112 := by
    simpa [prefixWord, tailWord_829112, baseEnd_829112] using wordTrace_append hprefix tailTrace_829112
  have hstable : (prefixWord ++ tailWord_829112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829112).length < 2 ^ (prefixWord ++ tailWord_829112).sum := by decide
  have hdescent : baseEnd_829112 < baseStart_829112 := by decide
  rcases family_descends (prefixWord ++ tailWord_829112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829116 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_829116 : Nat := 118140960795 + 829116 * 2 ^ 59
def prefixEnd_829116 : Nat := 4983230072969 + 3 ^ 40 * 829116 * 2
def baseEnd_829116 : Nat := 425735026333283313536971

theorem tailTrace_829116 : CollatzResearch.WordTrace tailWord_829116 prefixEnd_829116 425735026333283313536971 := by
  unfold tailWord_829116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120172432130904292209601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20160229909507872389612801 15120172432130904292209601)
  ·
    refine ⟨11340129324098178219157201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15120172432130904292209601 11340129324098178219157201)
    ·
      refine ⟨8505096993073633664367901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11340129324098178219157201 8505096993073633664367901)
      ·
        refine ⟨3189411372402612624137963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8505096993073633664367901 3189411372402612624137963)
        ·
          refine ⟨4784117058603918936206945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189411372402612624137963 4784117058603918936206945)
          ·
            refine ⟨3588087793952939202155209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4784117058603918936206945 3588087793952939202155209)
            ·
              refine ⟨2691065845464704401616407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588087793952939202155209 2691065845464704401616407)
              ·
                refine ⟨4036598768197056602424611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691065845464704401616407 4036598768197056602424611)
                ·
                  refine ⟨6054898152295584903636917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4036598768197056602424611 6054898152295584903636917)
                  ·
                    refine ⟨567646701777711084715961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6054898152295584903636917 567646701777711084715961)
                    ·
                      refine ⟨425735026333283313536971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567646701777711084715961 425735026333283313536971)
                      ·
                        rfl

theorem cell23_829116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_829116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829116 prefixEnd_829116 := by exact prefixLift 829116
  have htrace : WordTrace (prefixWord ++ tailWord_829116) baseStart_829116 baseEnd_829116 := by
    simpa [prefixWord, tailWord_829116, baseEnd_829116] using wordTrace_append hprefix tailTrace_829116
  have hstable : (prefixWord ++ tailWord_829116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829116).length < 2 ^ (prefixWord ++ tailWord_829116).sum := by decide
  have hdescent : baseEnd_829116 < baseStart_829116 := by decide
  rcases family_descends (prefixWord ++ tailWord_829116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829140 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_829140 : Nat := 118140960795 + 829140 * 2 ^ 59
def prefixEnd_829140 : Nat := 4983230072969 + 3 ^ 40 * 829140 * 2
def baseEnd_829140 : Nat := 425747349868991219636861

theorem tailTrace_829140 : CollatzResearch.WordTrace tailWord_829140 prefixEnd_829140 425747349868991219636861 := by
  unfold tailWord_829140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120610108087430341646437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20160813477449907122195249 15120610108087430341646437)
  ·
    refine ⟨2835114395266393189058707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15120610108087430341646437 2835114395266393189058707)
    ·
      refine ⟨4252671592899589783588061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2835114395266393189058707 4252671592899589783588061)
      ·
        refine ⟨1594751847337346168845523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4252671592899589783588061 1594751847337346168845523)
        ·
          refine ⟨2392127771006019253268285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594751847337346168845523 2392127771006019253268285)
          ·
            refine ⟨897047914127257219975607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2392127771006019253268285 897047914127257219975607)
            ·
              refine ⟨1345571871190885829963411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897047914127257219975607 1345571871190885829963411)
              ·
                refine ⟨2018357806786328744945117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345571871190885829963411 2018357806786328744945117)
                ·
                  refine ⟨756884177544873279354419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2018357806786328744945117 756884177544873279354419)
                  ·
                    refine ⟨1135326266317309919031629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756884177544873279354419 1135326266317309919031629)
                    ·
                      refine ⟨425747349868991219636861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135326266317309919031629 425747349868991219636861)
                      ·
                        rfl

theorem cell23_829140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_829140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829140 prefixEnd_829140 := by exact prefixLift 829140
  have htrace : WordTrace (prefixWord ++ tailWord_829140) baseStart_829140 baseEnd_829140 := by
    simpa [prefixWord, tailWord_829140, baseEnd_829140] using wordTrace_append hprefix tailTrace_829140
  have hstable : (prefixWord ++ tailWord_829140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829140).length < 2 ^ (prefixWord ++ tailWord_829140).sum := by decide
  have hdescent : baseEnd_829140 < baseStart_829140 := by decide
  rcases family_descends (prefixWord ++ tailWord_829140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829152 : List Nat := [2, 1, 1, 3, 1, 2, 3, 10]
def baseStart_829152 : Nat := 118140960795 + 829152 * 2 ^ 59
def prefixEnd_829152 : Nat := 4983230072969 + 3 ^ 40 * 829152 * 2
def baseEnd_829152 : Nat := 15768648579142413803215

theorem tailTrace_829152 : CollatzResearch.WordTrace tailWord_829152 prefixEnd_829152 15768648579142413803215 := by
  unfold tailWord_829152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120828946065693366364855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20161105261420924488486473 15120828946065693366364855)
  ·
    refine ⟨22681243419098540049547283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15120828946065693366364855 22681243419098540049547283)
    ·
      refine ⟨34021865128647810074320925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22681243419098540049547283 34021865128647810074320925)
      ·
        refine ⟨12758199423242928777870347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34021865128647810074320925 12758199423242928777870347)
        ·
          refine ⟨19137299134864393166805521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12758199423242928777870347 19137299134864393166805521)
          ·
            refine ⟨14352974351148294875104141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19137299134864393166805521 14352974351148294875104141)
            ·
              refine ⟨5382365381680610578164053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14352974351148294875104141 5382365381680610578164053)
              ·
                refine ⟨15768648579142413803215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5382365381680610578164053 15768648579142413803215)
                ·
                  rfl

theorem cell23_829152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 10].length) (baseStart_829152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829152 prefixEnd_829152 := by exact prefixLift 829152
  have htrace : WordTrace (prefixWord ++ tailWord_829152) baseStart_829152 baseEnd_829152 := by
    simpa [prefixWord, tailWord_829152, baseEnd_829152] using wordTrace_append hprefix tailTrace_829152
  have hstable : (prefixWord ++ tailWord_829152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829152).length < 2 ^ (prefixWord ++ tailWord_829152).sum := by decide
  have hdescent : baseEnd_829152 < baseStart_829152 := by decide
  rcases family_descends (prefixWord ++ tailWord_829152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829156 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_829156 : Nat := 118140960795 + 829156 * 2 ^ 59
def prefixEnd_829156 : Nat := 4983230072969 + 3 ^ 40 * 829156 * 2
def baseEnd_829156 : Nat := 141918521853154385678929

theorem tailTrace_829156 : CollatzResearch.WordTrace tailWord_829156 prefixEnd_829156 141918521853154385678929 := by
  unfold tailWord_829156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120901892058447707937661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20161202522744596943916881 15120901892058447707937661)
  ·
    refine ⟨5670338209521917890476623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15120901892058447707937661 5670338209521917890476623)
    ·
      refine ⟨8505507314282876835714935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670338209521917890476623 8505507314282876835714935)
      ·
        refine ⟨12758260971424315253572403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505507314282876835714935 12758260971424315253572403)
        ·
          refine ⟨19137391457136472880358605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12758260971424315253572403 19137391457136472880358605)
          ·
            refine ⟨7176521796426177330134477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19137391457136472880358605 7176521796426177330134477)
            ·
              refine ⟨2691195673659816498800429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7176521796426177330134477 2691195673659816498800429)
              ·
                refine ⟨1009198377622431187050161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2691195673659816498800429 1009198377622431187050161)
                ·
                  refine ⟨756898783216823390287621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009198377622431187050161 756898783216823390287621)
                  ·
                    refine ⟨141918521853154385678929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756898783216823390287621 141918521853154385678929)
                    ·
                      rfl

theorem cell23_829156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_829156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829156 prefixEnd_829156 := by exact prefixLift 829156
  have htrace : WordTrace (prefixWord ++ tailWord_829156) baseStart_829156 baseEnd_829156 := by
    simpa [prefixWord, tailWord_829156, baseEnd_829156] using wordTrace_append hprefix tailTrace_829156
  have hstable : (prefixWord ++ tailWord_829156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829156).length < 2 ^ (prefixWord ++ tailWord_829156).sum := by decide
  have hdescent : baseEnd_829156 < baseStart_829156 := by decide
  rcases family_descends (prefixWord ++ tailWord_829156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829166 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_829166 : Nat := 118140960795 + 829166 * 2 ^ 59
def prefixEnd_829166 : Nat := 4983230072969 + 3 ^ 40 * 829166 * 2
def baseEnd_829166 : Nat := 425760700366008117911741

theorem tailTrace_829166 : CollatzResearch.WordTrace tailWord_829166 prefixEnd_829166 425760700366008117911741 := by
  unfold tailWord_829166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780271064260083390467419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20161445676053778082492901 3780271064260083390467419)
  ·
    refine ⟨5670406596390125085701129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3780271064260083390467419 5670406596390125085701129)
    ·
      refine ⟨4252804947292593814275847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5670406596390125085701129 4252804947292593814275847)
      ·
        refine ⟨6379207420938890721413771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252804947292593814275847 6379207420938890721413771)
        ·
          refine ⟨9568811131408336082120657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379207420938890721413771 9568811131408336082120657)
          ·
            refine ⟨7176608348556252061590493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9568811131408336082120657 7176608348556252061590493)
            ·
              refine ⟨2691228130708594523096435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7176608348556252061590493 2691228130708594523096435)
              ·
                refine ⟨4036842196062891784644653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691228130708594523096435 4036842196062891784644653)
                ·
                  refine ⟨1513815823523584419241745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4036842196062891784644653 1513815823523584419241745)
                  ·
                    refine ⟨1135361867642688314431309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1513815823523584419241745 1135361867642688314431309)
                    ·
                      refine ⟨425760700366008117911741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135361867642688314431309 425760700366008117911741)
                      ·
                        rfl

theorem cell23_829166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_829166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829166 prefixEnd_829166 := by exact prefixLift 829166
  have htrace : WordTrace (prefixWord ++ tailWord_829166) baseStart_829166 baseEnd_829166 := by
    simpa [prefixWord, tailWord_829166, baseEnd_829166] using wordTrace_append hprefix tailTrace_829166
  have hstable : (prefixWord ++ tailWord_829166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829166).length < 2 ^ (prefixWord ++ tailWord_829166).sum := by decide
  have hdescent : baseEnd_829166 < baseStart_829166 := by decide
  rcases family_descends (prefixWord ++ tailWord_829166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829180 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_829180 : Nat := 118140960795 + 829180 * 2 ^ 59
def prefixEnd_829180 : Nat := 4983230072969 + 3 ^ 40 * 829180 * 2
def baseEnd_829180 : Nat := 425767889095171063136677

theorem tailTrace_829180 : CollatzResearch.WordTrace tailWord_829180 prefixEnd_829180 425767889095171063136677 := by
  unfold tailWord_829180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15121339568014973757374497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20161786090686631676499329 15121339568014973757374497)
  ·
    refine ⟨11341004676011230318030873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15121339568014973757374497 11341004676011230318030873)
    ·
      refine ⟨8505753507008422738523155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11341004676011230318030873 8505753507008422738523155)
      ·
        refine ⟨12758630260512634107784733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505753507008422738523155 12758630260512634107784733)
        ·
          refine ⟨4784486347692237790419275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12758630260512634107784733 4784486347692237790419275)
          ·
            refine ⟨7176729521538356685628913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784486347692237790419275 7176729521538356685628913)
            ·
              refine ⟨5382547141153767514221685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7176729521538356685628913 5382547141153767514221685)
              ·
                refine ⟨504613794483165704458283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5382547141153767514221685 504613794483165704458283)
                ·
                  refine ⟨756920691724748556687425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504613794483165704458283 756920691724748556687425)
                  ·
                    refine ⟨567690518793561417515569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756920691724748556687425 567690518793561417515569)
                    ·
                      refine ⟨425767889095171063136677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567690518793561417515569 425767889095171063136677)
                      ·
                        rfl

theorem cell23_829180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_829180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829180 prefixEnd_829180 := by exact prefixLift 829180
  have htrace : WordTrace (prefixWord ++ tailWord_829180) baseStart_829180 baseEnd_829180 := by
    simpa [prefixWord, tailWord_829180, baseEnd_829180] using wordTrace_append hprefix tailTrace_829180
  have hstable : (prefixWord ++ tailWord_829180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829180).length < 2 ^ (prefixWord ++ tailWord_829180).sum := by decide
  have hdescent : baseEnd_829180 < baseStart_829180 := by decide
  rcases family_descends (prefixWord ++ tailWord_829180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829196 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_829196 : Nat := 118140960795 + 829196 * 2 ^ 59
def prefixEnd_829196 : Nat := 4983230072969 + 3 ^ 40 * 829196 * 2
def baseEnd_829196 : Nat := 425776104785643000536603

theorem tailTrace_829196 : CollatzResearch.WordTrace tailWord_829196 prefixEnd_829196 425776104785643000536603 := by
  unfold tailWord_829196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15121631351985991123665721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20162175135981321498220961 15121631351985991123665721)
  ·
    refine ⟨11341223513989493342749291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15121631351985991123665721 11341223513989493342749291)
    ·
      refine ⟨17011835270984240014123937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11341223513989493342749291 17011835270984240014123937)
      ·
        refine ⟨12758876453238180010592953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17011835270984240014123937 12758876453238180010592953)
        ·
          refine ⟨9569157339928635007944715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12758876453238180010592953 9569157339928635007944715)
          ·
            refine ⟨14353736009892952511917073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9569157339928635007944715 14353736009892952511917073)
            ·
              refine ⟨10765302007419714383937805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14353736009892952511917073 10765302007419714383937805)
              ·
                refine ⟨4036988252782392893976677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10765302007419714383937805 4036988252782392893976677)
                ·
                  refine ⟨756935297396698667620627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4036988252782392893976677 756935297396698667620627)
                  ·
                    refine ⟨1135402946095048001430941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756935297396698667620627 1135402946095048001430941)
                    ·
                      refine ⟨425776104785643000536603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135402946095048001430941 425776104785643000536603)
                      ·
                        rfl

theorem cell23_829196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_829196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829196 prefixEnd_829196 := by exact prefixLift 829196
  have htrace : WordTrace (prefixWord ++ tailWord_829196) baseStart_829196 baseEnd_829196 := by
    simpa [prefixWord, tailWord_829196, baseEnd_829196] using wordTrace_append hprefix tailTrace_829196
  have hstable : (prefixWord ++ tailWord_829196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829196).length < 2 ^ (prefixWord ++ tailWord_829196).sum := by decide
  have hdescent : baseEnd_829196 < baseStart_829196 := by decide
  rcases family_descends (prefixWord ++ tailWord_829196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829214 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_829214 : Nat := 118140960795 + 829214 * 2 ^ 59
def prefixEnd_829214 : Nat := 4983230072969 + 3 ^ 40 * 829214 * 2
def baseEnd_829214 : Nat := 425785347437423930111521

theorem tailTrace_829214 : CollatzResearch.WordTrace tailWord_829214 prefixEnd_829214 425785347437423930111521 := by
  unfold tailWord_829214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780489902238346415185837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20162612811937847547657797 3780489902238346415185837)
  ·
    refine ⟨1417683713339379905694689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3780489902238346415185837 1417683713339379905694689)
    ·
      refine ⟨1063262785004534929271017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1417683713339379905694689 1063262785004534929271017)
      ·
        refine ⟨797447088753401196953263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1063262785004534929271017 797447088753401196953263)
        ·
          refine ⟨1196170633130101795429895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797447088753401196953263 1196170633130101795429895)
          ·
            refine ⟨1794255949695152693144843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196170633130101795429895 1794255949695152693144843)
            ·
              refine ⟨2691383924542729039717265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794255949695152693144843 2691383924542729039717265)
              ·
                refine ⟨2018537943407046779787949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2691383924542729039717265 2018537943407046779787949)
                ·
                  refine ⟨756951728777642542420481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2018537943407046779787949 756951728777642542420481)
                  ·
                    refine ⟨567713796583231906815361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756951728777642542420481 567713796583231906815361)
                    ·
                      refine ⟨425785347437423930111521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567713796583231906815361 425785347437423930111521)
                      ·
                        rfl

theorem cell23_829214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_829214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829214 prefixEnd_829214 := by exact prefixLift 829214
  have htrace : WordTrace (prefixWord ++ tailWord_829214) baseStart_829214 baseEnd_829214 := by
    simpa [prefixWord, tailWord_829214, baseEnd_829214] using wordTrace_append hprefix tailTrace_829214
  have hstable : (prefixWord ++ tailWord_829214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829214).length < 2 ^ (prefixWord ++ tailWord_829214).sum := by decide
  have hdescent : baseEnd_829214 < baseStart_829214 := by decide
  rcases family_descends (prefixWord ++ tailWord_829214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829239 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_829239 : Nat := 118140960795 + 829239 * 2 ^ 59
def prefixEnd_829239 : Nat := 4983230072969 + 3 ^ 40 * 829239 * 2
def baseEnd_829239 : Nat := 425798184453786332298905

theorem tailTrace_829239 : CollatzResearch.WordTrace tailWord_829239 prefixEnd_829239 425798184453786332298905 := by
  unfold tailWord_829239
  simp only [CollatzResearch.WordTrace]
  refine ⟨30244831042816200591146771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20163220695210800394097847 30244831042816200591146771)
  ·
    refine ⟨45367246564224300886720157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30244831042816200591146771 45367246564224300886720157)
    ·
      refine ⟨17012717461584112832520059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45367246564224300886720157 17012717461584112832520059)
      ·
        refine ⟨25519076192376169248780089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17012717461584112832520059 25519076192376169248780089)
        ·
          refine ⟨19139307144282126936585067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25519076192376169248780089 19139307144282126936585067)
          ·
            refine ⟨28708960716423190404877601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19139307144282126936585067 28708960716423190404877601)
            ·
              refine ⟨21531720537317392803658201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28708960716423190404877601 21531720537317392803658201)
              ·
                refine ⟨16148790402988044602743651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21531720537317392803658201 16148790402988044602743651)
                ·
                  refine ⟨24223185604482066904115477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16148790402988044602743651 24223185604482066904115477)
                  ·
                    refine ⟨1135461825210096886130413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24223185604482066904115477 1135461825210096886130413)
                    ·
                      refine ⟨425798184453786332298905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135461825210096886130413 425798184453786332298905)
                      ·
                        rfl

theorem cell23_829239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_829239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829239 prefixEnd_829239 := by exact prefixLift 829239
  have htrace : WordTrace (prefixWord ++ tailWord_829239) baseStart_829239 baseEnd_829239 := by
    simpa [prefixWord, tailWord_829239, baseEnd_829239] using wordTrace_append hprefix tailTrace_829239
  have hstable : (prefixWord ++ tailWord_829239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829239).length < 2 ^ (prefixWord ++ tailWord_829239).sum := by decide
  have hdescent : baseEnd_829239 < baseStart_829239 := by decide
  rcases family_descends (prefixWord ++ tailWord_829239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829240 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 1, 3, 2]
def baseStart_829240 : Nat := 118140960795 + 829240 * 2 ^ 59
def prefixEnd_829240 : Nat := 4983230072969 + 3 ^ 40 * 829240 * 2
def baseEnd_829240 : Nat := 425798697934440828386401

theorem tailTrace_829240 : CollatzResearch.WordTrace tailWord_829240 prefixEnd_829240 425798697934440828386401 := by
  unfold tailWord_829240
  simp only [CollatzResearch.WordTrace]
  refine ⟨15122433757906288880966587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20163245010541718507955449 15122433757906288880966587)
  ·
    refine ⟨22683650636859433321449881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15122433757906288880966587 22683650636859433321449881)
    ·
      refine ⟨17012737977644574991087411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22683650636859433321449881 17012737977644574991087411)
      ·
        refine ⟨25519106966466862486631117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17012737977644574991087411 25519106966466862486631117)
        ·
          refine ⟨9569665112425073432486669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25519106966466862486631117 9569665112425073432486669)
          ·
            refine ⟨3588624417159402537182501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9569665112425073432486669 3588624417159402537182501)
            ·
              refine ⟨672867078217387975721719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3588624417159402537182501 672867078217387975721719)
              ·
                refine ⟨1009300617326081963582579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672867078217387975721719 1009300617326081963582579)
                ·
                  refine ⟨1513950925989122945373869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009300617326081963582579 1513950925989122945373869)
                  ·
                    refine ⟨567731597245921104515201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513950925989122945373869 567731597245921104515201)
                    ·
                      refine ⟨425798697934440828386401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567731597245921104515201 425798697934440828386401)
                      ·
                        rfl

theorem cell23_829240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_829240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829240 prefixEnd_829240 := by exact prefixLift 829240
  have htrace : WordTrace (prefixWord ++ tailWord_829240) baseStart_829240 baseEnd_829240 := by
    simpa [prefixWord, tailWord_829240, baseEnd_829240] using wordTrace_append hprefix tailTrace_829240
  have hstable : (prefixWord ++ tailWord_829240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829240).length < 2 ^ (prefixWord ++ tailWord_829240).sum := by decide
  have hdescent : baseEnd_829240 < baseStart_829240 := by decide
  rcases family_descends (prefixWord ++ tailWord_829240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829246 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_829246 : Nat := 118140960795 + 829246 * 2 ^ 59
def prefixEnd_829246 : Nat := 4983230072969 + 3 ^ 40 * 829246 * 2
def baseEnd_829246 : Nat := 141933926272789268303791

theorem tailTrace_829246 : CollatzResearch.WordTrace tailWord_829246 prefixEnd_829246 141933926272789268303791 := by
  unfold tailWord_829246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780635794223855098331449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20163390902527227191101061 3780635794223855098331449)
  ·
    refine ⟨2835476845667891323748587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3780635794223855098331449 2835476845667891323748587)
    ·
      refine ⟨4253215268501836985622881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2835476845667891323748587 4253215268501836985622881)
      ·
        refine ⟨3189911451376377739217161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4253215268501836985622881 3189911451376377739217161)
        ·
          refine ⟨2392433588532283304412871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189911451376377739217161 2392433588532283304412871)
          ·
            refine ⟨3588650382798424956619307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392433588532283304412871 3588650382798424956619307)
            ·
              refine ⟨5382975574197637434928961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588650382798424956619307 5382975574197637434928961)
              ·
                refine ⟨4037231680648228076196721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5382975574197637434928961 4037231680648228076196721)
                ·
                  refine ⟨3027923760486171057147541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037231680648228076196721 3027923760486171057147541)
                  ·
                    refine ⟨141933926272789268303791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3027923760486171057147541 141933926272789268303791)
                    ·
                      rfl

theorem cell23_829246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_829246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829246 prefixEnd_829246 := by exact prefixLift 829246
  have htrace : WordTrace (prefixWord ++ tailWord_829246) baseStart_829246 baseEnd_829246 := by
    simpa [prefixWord, tailWord_829246, baseEnd_829246] using wordTrace_append hprefix tailTrace_829246
  have hstable : (prefixWord ++ tailWord_829246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829246).length < 2 ^ (prefixWord ++ tailWord_829246).sum := by decide
  have hdescent : baseEnd_829246 < baseStart_829246 := by decide
  rcases family_descends (prefixWord ++ tailWord_829246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829247 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 2, 1, 3]
def baseStart_829247 : Nat := 118140960795 + 829247 * 2 ^ 59
def prefixEnd_829247 : Nat := 4983230072969 + 3 ^ 40 * 829247 * 2
def baseEnd_829247 : Nat := 425802292299022300998869

theorem tailTrace_829247 : CollatzResearch.WordTrace tailWord_829247 prefixEnd_829247 425802292299022300998869 := by
  unfold tailWord_829247
  simp only [CollatzResearch.WordTrace]
  refine ⟨30245122826787217957437995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20163415217858145304958663 30245122826787217957437995)
  ·
    refine ⟨45367684240180826936156993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30245122826787217957437995 45367684240180826936156993)
    ·
      refine ⟨34025763180135620202117745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45367684240180826936156993 34025763180135620202117745)
      ·
        refine ⟨25519322385101715151588309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34025763180135620202117745 25519322385101715151588309)
        ·
          refine ⟨598109118400821448865351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25519322385101715151588309 598109118400821448865351)
          ·
            refine ⟨897163677601232173298027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598109118400821448865351 897163677601232173298027)
            ·
              refine ⟨1345745516401848259947041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897163677601232173298027 1345745516401848259947041)
              ·
                refine ⟨1009309137301386194960281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345745516401848259947041 1009309137301386194960281)
                ·
                  refine ⟨756981852976039646220211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009309137301386194960281 756981852976039646220211)
                  ·
                    refine ⟨1135472779464059469330317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756981852976039646220211 1135472779464059469330317)
                    ·
                      refine ⟨425802292299022300998869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135472779464059469330317 425802292299022300998869)
                      ·
                        rfl

theorem cell23_829247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_829247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829247 prefixEnd_829247 := by exact prefixLift 829247
  have htrace : WordTrace (prefixWord ++ tailWord_829247) baseStart_829247 baseEnd_829247 := by
    simpa [prefixWord, tailWord_829247, baseEnd_829247] using wordTrace_append hprefix tailTrace_829247
  have hstable : (prefixWord ++ tailWord_829247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829247).length < 2 ^ (prefixWord ++ tailWord_829247).sum := by decide
  have hdescent : baseEnd_829247 < baseStart_829247 := by decide
  rcases family_descends (prefixWord ++ tailWord_829247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829253 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 4, 2, 2]
def baseStart_829253 : Nat := 118140960795 + 829253 * 2 ^ 59
def prefixEnd_829253 : Nat := 4983230072969 + 3 ^ 40 * 829253 * 2
def baseEnd_829253 : Nat := 425805373182949277523841

theorem tailTrace_829253 : CollatzResearch.WordTrace tailWord_829253 prefixEnd_829253 425805373182949277523841 := by
  unfold tailWord_829253
  simp only [CollatzResearch.WordTrace]
  refine ⟨30245341664765480982156413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20163561109843653988104275 30245341664765480982156413)
  ·
    refine ⟨11342003124287055368308655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30245341664765480982156413 11342003124287055368308655)
    ·
      refine ⟨17013004686430583052462983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11342003124287055368308655 17013004686430583052462983)
      ·
        refine ⟨25519507029645874578694475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17013004686430583052462983 25519507029645874578694475)
        ·
          refine ⟨38279260544468811868041713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25519507029645874578694475 38279260544468811868041713)
          ·
            refine ⟨28709445408351608901031285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38279260544468811868041713 28709445408351608901031285)
            ·
              refine ⟨2691510507032963334471683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28709445408351608901031285 2691510507032963334471683)
              ·
                refine ⟨4037265760549445001707525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691510507032963334471683 4037265760549445001707525)
                ·
                  refine ⟨756987330103020937820161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4037265760549445001707525 756987330103020937820161)
                  ·
                    refine ⟨567740497577265703365121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756987330103020937820161 567740497577265703365121)
                    ·
                      refine ⟨425805373182949277523841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567740497577265703365121 425805373182949277523841)
                      ·
                        rfl

theorem cell23_829253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_829253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829253 prefixEnd_829253 := by exact prefixLift 829253
  have htrace : WordTrace (prefixWord ++ tailWord_829253) baseStart_829253 baseEnd_829253 := by
    simpa [prefixWord, tailWord_829253, baseEnd_829253] using wordTrace_append hprefix tailTrace_829253
  have hstable : (prefixWord ++ tailWord_829253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829253).length < 2 ^ (prefixWord ++ tailWord_829253).sum := by decide
  have hdescent : baseEnd_829253 < baseStart_829253 := by decide
  rcases family_descends (prefixWord ++ tailWord_829253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829266 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_829266 : Nat := 118140960795 + 829266 * 2 ^ 59
def prefixEnd_829266 : Nat := 4983230072969 + 3 ^ 40 * 829266 * 2
def baseEnd_829266 : Nat := 425812048431457726661281

theorem tailTrace_829266 : CollatzResearch.WordTrace tailWord_829266 prefixEnd_829266 425812048431457726661281 := by
  unfold tailWord_829266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7561453953429596050594913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20163877209145589468253101 7561453953429596050594913)
  ·
    refine ⟨5671090465072197037946185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7561453953429596050594913 5671090465072197037946185)
    ·
      refine ⟨4253317848804147778459639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5671090465072197037946185 4253317848804147778459639)
      ·
        refine ⟨6379976773206221667689459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4253317848804147778459639 6379976773206221667689459)
        ·
          refine ⟨9569965159809332501534189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379976773206221667689459 9569965159809332501534189)
          ·
            refine ⟨3588736934928499688075321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9569965159809332501534189 3588736934928499688075321)
            ·
              refine ⟨2691552701196374766056491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588736934928499688075321 2691552701196374766056491)
              ·
                refine ⟨4037329051794562149084737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691552701196374766056491 4037329051794562149084737)
                ·
                  refine ⟨3027996788845921611813553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037329051794562149084737 3027996788845921611813553)
                  ·
                    refine ⟨2270997591634441208860165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3027996788845921611813553 2270997591634441208860165)
                    ·
                      refine ⟨425812048431457726661281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2270997591634441208860165 425812048431457726661281)
                      ·
                        rfl

theorem cell23_829266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_829266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829266 prefixEnd_829266 := by exact prefixLift 829266
  have htrace : WordTrace (prefixWord ++ tailWord_829266) baseStart_829266 baseEnd_829266 := by
    simpa [prefixWord, tailWord_829266, baseEnd_829266] using wordTrace_append hprefix tailTrace_829266
  have hstable : (prefixWord ++ tailWord_829266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829266).length < 2 ^ (prefixWord ++ tailWord_829266).sum := by decide
  have hdescent : baseEnd_829266 < baseStart_829266 := by decide
  rcases family_descends (prefixWord ++ tailWord_829266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829289 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_829289 : Nat := 118140960795 + 829289 * 2 ^ 59
def prefixEnd_829289 : Nat := 4983230072969 + 3 ^ 40 * 829289 * 2
def baseEnd_829289 : Nat := 141941286162170378891225

theorem tailTrace_829289 : CollatzResearch.WordTrace tailWord_829289 prefixEnd_829289 141941286162170378891225 := by
  unfold tailWord_829289
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246654692635059130466921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20164436461756706086977947 30246654692635059130466921)
  ·
    refine ⟨22684991019476294347850191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30246654692635059130466921 22684991019476294347850191)
    ·
      refine ⟨34027486529214441521775287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22684991019476294347850191 34027486529214441521775287)
      ·
        refine ⟨51041229793821662282662931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34027486529214441521775287 51041229793821662282662931)
        ·
          refine ⟨76561844690732493423994397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51041229793821662282662931 76561844690732493423994397)
          ·
            refine ⟨28710691759024685033997899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76561844690732493423994397 28710691759024685033997899)
            ·
              refine ⟨43066037638537027550996849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28710691759024685033997899 43066037638537027550996849)
              ·
                refine ⟨32299528228902770663247637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43066037638537027550996849 32299528228902770663247637)
                ·
                  refine ⟨1514040385729817374839733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32299528228902770663247637 1514040385729817374839733)
                  ·
                    refine ⟨141941286162170378891225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1514040385729817374839733 141941286162170378891225)
                    ·
                      rfl

theorem cell23_829289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_829289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829289 prefixEnd_829289 := by exact prefixLift 829289
  have htrace : WordTrace (prefixWord ++ tailWord_829289) baseStart_829289 baseEnd_829289 := by
    simpa [prefixWord, tailWord_829289, baseEnd_829289] using wordTrace_append hprefix tailTrace_829289
  have hstable : (prefixWord ++ tailWord_829289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829289).length < 2 ^ (prefixWord ++ tailWord_829289).sum := by decide
  have hdescent : baseEnd_829289 < baseStart_829289 := by decide
  rcases family_descends (prefixWord ++ tailWord_829289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829293 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 5]
def baseStart_829293 : Nat := 118140960795 + 829293 * 2 ^ 59
def prefixEnd_829293 : Nat := 4983230072969 + 3 ^ 40 * 829293 * 2
def baseEnd_829293 : Nat := 47313990267681013447073

theorem tailTrace_829293 : CollatzResearch.WordTrace tailWord_829293 prefixEnd_829293 47313990267681013447073 := by
  unfold tailWord_829293
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246800584620567813612533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20164533723080378542408355 30246800584620567813612533)
  ·
    refine ⟨2835637554808178232526175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30246800584620567813612533 2835637554808178232526175)
    ·
      refine ⟨4253456332212267348789263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2835637554808178232526175 4253456332212267348789263)
      ·
        refine ⟨6380184498318401023183895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4253456332212267348789263 6380184498318401023183895)
        ·
          refine ⟨9570276747477601534775843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6380184498318401023183895 9570276747477601534775843)
          ·
            refine ⟨14355415121216402302163765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570276747477601534775843 14355415121216402302163765)
            ·
              refine ⟨1345820167614037715827853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14355415121216402302163765 1345820167614037715827853)
              ·
                refine ⟨504682562855264143435445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1345820167614037715827853 504682562855264143435445)
                ·
                  refine ⟨47313990267681013447073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 504682562855264143435445 47313990267681013447073)
                  ·
                    rfl

theorem cell23_829293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_829293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829293 prefixEnd_829293 := by exact prefixLift 829293
  have htrace : WordTrace (prefixWord ++ tailWord_829293) baseStart_829293 baseEnd_829293 := by
    simpa [prefixWord, tailWord_829293, baseEnd_829293] using wordTrace_append hprefix tailTrace_829293
  have hstable : (prefixWord ++ tailWord_829293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829293).length < 2 ^ (prefixWord ++ tailWord_829293).sum := by decide
  have hdescent : baseEnd_829293 < baseStart_829293 := by decide
  rcases family_descends (prefixWord ++ tailWord_829293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829296 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 7, 2]
def baseStart_829296 : Nat := 118140960795 + 829296 * 2 ^ 59
def prefixEnd_829296 : Nat := 4983230072969 + 3 ^ 40 * 829296 * 2
def baseEnd_829296 : Nat := 425827452851092609286143

theorem tailTrace_829296 : CollatzResearch.WordTrace tailWord_829296 prefixEnd_829296 425827452851092609286143 := by
  unfold tailWord_829296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15123455001804849662985871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20164606669073132883981161 15123455001804849662985871)
  ·
    refine ⟨22685182502707274494478807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15123455001804849662985871 22685182502707274494478807)
    ·
      refine ⟨34027773754060911741718211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22685182502707274494478807 34027773754060911741718211)
      ·
        refine ⟨51041660631091367612577317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34027773754060911741718211 51041660631091367612577317)
        ·
          refine ⟨9570311368329631427358247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51041660631091367612577317 9570311368329631427358247)
          ·
            refine ⟨14355467052494447141037371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570311368329631427358247 14355467052494447141037371)
            ·
              refine ⟨21533200578741670711556057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14355467052494447141037371 21533200578741670711556057)
              ·
                refine ⟨16149900434056253033667043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21533200578741670711556057 16149900434056253033667043)
                ·
                  refine ⟨24224850651084379550500565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16149900434056253033667043 24224850651084379550500565)
                  ·
                    refine ⟨567769937134790145714857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24224850651084379550500565 567769937134790145714857)
                    ·
                      refine ⟨425827452851092609286143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567769937134790145714857 425827452851092609286143)
                      ·
                        rfl

theorem cell23_829296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 7, 2].length) (baseStart_829296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829296 prefixEnd_829296 := by exact prefixLift 829296
  have htrace : WordTrace (prefixWord ++ tailWord_829296) baseStart_829296 baseEnd_829296 := by
    simpa [prefixWord, tailWord_829296, baseEnd_829296] using wordTrace_append hprefix tailTrace_829296
  have hstable : (prefixWord ++ tailWord_829296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829296).length < 2 ^ (prefixWord ++ tailWord_829296).sum := by decide
  have hdescent : baseEnd_829296 < baseStart_829296 := by decide
  rcases family_descends (prefixWord ++ tailWord_829296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829299 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5]
def baseStart_829299 : Nat := 118140960795 + 829299 * 2 ^ 59
def prefixEnd_829299 : Nat := 4983230072969 + 3 ^ 40 * 829299 * 2
def baseEnd_829299 : Nat := 425828993293056097548629

theorem tailTrace_829299 : CollatzResearch.WordTrace tailWord_829299 prefixEnd_829299 425828993293056097548629 := by
  unfold tailWord_829299
  simp only [CollatzResearch.WordTrace]
  refine ⟨30247019422598830838330951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20164679615065887225553967 30247019422598830838330951)
  ·
    refine ⟨45370529133898246257496427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30247019422598830838330951 45370529133898246257496427)
    ·
      refine ⟨68055793700847369386244641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45370529133898246257496427 68055793700847369386244641)
      ·
        refine ⟨51041845275635527039683481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68055793700847369386244641 51041845275635527039683481)
        ·
          refine ⟨38281383956726645279762611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51041845275635527039683481 38281383956726645279762611)
          ·
            refine ⟨57422075935089967919643917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38281383956726645279762611 57422075935089967919643917)
            ·
              refine ⟨21533278475658737969866469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57422075935089967919643917 21533278475658737969866469)
              ·
                refine ⟨4037489714186013369349963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21533278475658737969866469 4037489714186013369349963)
                ·
                  refine ⟨6056234571279020054024945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037489714186013369349963 6056234571279020054024945)
                  ·
                    refine ⟨4542175928459265040518709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056234571279020054024945 4542175928459265040518709)
                    ·
                      refine ⟨425828993293056097548629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4542175928459265040518709 425828993293056097548629)
                      ·
                        rfl

theorem cell23_829299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_829299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829299 prefixEnd_829299 := by exact prefixLift 829299
  have htrace : WordTrace (prefixWord ++ tailWord_829299) baseStart_829299 baseEnd_829299 := by
    simpa [prefixWord, tailWord_829299, baseEnd_829299] using wordTrace_append hprefix tailTrace_829299
  have hstable : (prefixWord ++ tailWord_829299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829299).length < 2 ^ (prefixWord ++ tailWord_829299).sum := by decide
  have hdescent : baseEnd_829299 < baseStart_829299 := by decide
  rcases family_descends (prefixWord ++ tailWord_829299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829310 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_829310 : Nat := 118140960795 + 829310 * 2 ^ 59
def prefixEnd_829310 : Nat := 4983230072969 + 3 ^ 40 * 829310 * 2
def baseEnd_829310 : Nat := 47314960175583950501231

theorem tailTrace_829310 : CollatzResearch.WordTrace tailWord_829310 prefixEnd_829310 47314960175583950501231 := by
  unfold tailWord_829310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780927578194872464622673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20164947083705986477987589 3780927578194872464622673)
  ·
    refine ⟨2835695683646154348467005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3780927578194872464622673 2835695683646154348467005)
    ·
      refine ⟨1063385881367307880675127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2835695683646154348467005 1063385881367307880675127)
      ·
        refine ⟨1595078822050961821012691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063385881367307880675127 1595078822050961821012691)
        ·
          refine ⟨2392618233076442731519037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595078822050961821012691 2392618233076442731519037)
          ·
            refine ⟨897231837403666024319639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2392618233076442731519037 897231837403666024319639)
            ·
              refine ⟨1345847756105499036479459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897231837403666024319639 1345847756105499036479459)
              ·
                refine ⟨2018771634158248554719189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345847756105499036479459 2018771634158248554719189)
                ·
                  refine ⟨47314960175583950501231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2018771634158248554719189 47314960175583950501231)
                  ·
                    rfl

theorem cell23_829310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_829310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829310 prefixEnd_829310 := by exact prefixLift 829310
  have htrace : WordTrace (prefixWord ++ tailWord_829310) baseStart_829310 baseEnd_829310 := by
    simpa [prefixWord, tailWord_829310, baseEnd_829310] using wordTrace_append hprefix tailTrace_829310
  have hstable : (prefixWord ++ tailWord_829310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829310).length < 2 ^ (prefixWord ++ tailWord_829310).sum := by decide
  have hdescent : baseEnd_829310 < baseStart_829310 := by decide
  rcases family_descends (prefixWord ++ tailWord_829310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829349 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 10]
def baseStart_829349 : Nat := 118140960795 + 829349 * 2 ^ 59
def prefixEnd_829349 : Nat := 4983230072969 + 3 ^ 40 * 829349 * 2
def baseEnd_829349 : Nat := 47317185258420100213711

theorem tailTrace_829349 : CollatzResearch.WordTrace tailWord_829349 prefixEnd_829349 47317185258420100213711 := by
  unfold tailWord_829349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30248843072417689377651101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20165895381611792918434067 30248843072417689377651101)
  ·
    refine ⟨11343316152156633516619163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30248843072417689377651101 11343316152156633516619163)
    ·
      refine ⟨17014974228234950274928745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11343316152156633516619163 17014974228234950274928745)
      ·
        refine ⟨12761230671176212706196559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17014974228234950274928745 12761230671176212706196559)
        ·
          refine ⟨19141846006764319059294839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12761230671176212706196559 19141846006764319059294839)
          ·
            refine ⟨28712769010146478588942259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19141846006764319059294839 28712769010146478588942259)
            ·
              refine ⟨43069153515219717883413389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28712769010146478588942259 43069153515219717883413389)
              ·
                refine ⟨16150932568207394206280021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43069153515219717883413389 16150932568207394206280021)
                ·
                  refine ⟨47317185258420100213711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 16150932568207394206280021 47317185258420100213711)
                  ·
                    rfl

theorem cell23_829349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_829349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829349 prefixEnd_829349 := by exact prefixLift 829349
  have htrace : WordTrace (prefixWord ++ tailWord_829349) baseStart_829349 baseEnd_829349 := by
    simpa [prefixWord, tailWord_829349, baseEnd_829349] using wordTrace_append hprefix tailTrace_829349
  have hstable : (prefixWord ++ tailWord_829349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829349).length < 2 ^ (prefixWord ++ tailWord_829349).sum := by decide
  have hdescent : baseEnd_829349 < baseStart_829349 := by decide
  rcases family_descends (prefixWord ++ tailWord_829349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829379 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 11]
def baseStart_829379 : Nat := 118140960795 + 829379 * 2 ^ 59
def prefixEnd_829379 : Nat := 4983230072969 + 3 ^ 40 * 829379 * 2
def baseEnd_829379 : Nat := 141956690581805261516087

theorem tailTrace_829379 : CollatzResearch.WordTrace tailWord_829379 prefixEnd_829379 141956690581805261516087 := by
  unfold tailWord_829379
  simp only [CollatzResearch.WordTrace]
  refine ⟨30249937262309004501243191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20166624841539336334162127 30249937262309004501243191)
  ·
    refine ⟨45374905893463506751864787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30249937262309004501243191 45374905893463506751864787)
    ·
      refine ⟨68062358840195260127797181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45374905893463506751864787 68062358840195260127797181)
      ·
        refine ⟨25523384565073222547923943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68062358840195260127797181 25523384565073222547923943)
        ·
          refine ⟨38285076847609833821885915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25523384565073222547923943 38285076847609833821885915)
          ·
            refine ⟨57427615271414750732828873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38285076847609833821885915 57427615271414750732828873)
            ·
              refine ⟨43070711453561063049621655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57427615271414750732828873 43070711453561063049621655)
              ·
                refine ⟨64606067180341594574432483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43070711453561063049621655 64606067180341594574432483)
                ·
                  refine ⟨96909100770512391861648725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64606067180341594574432483 96909100770512391861648725)
                  ·
                    refine ⟨141956690581805261516087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 96909100770512391861648725 141956690581805261516087)
                    ·
                      rfl

theorem cell23_829379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_829379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829379 prefixEnd_829379 := by exact prefixLift 829379
  have htrace : WordTrace (prefixWord ++ tailWord_829379) baseStart_829379 baseEnd_829379 := by
    simpa [prefixWord, tailWord_829379, baseEnd_829379] using wordTrace_append hprefix tailTrace_829379
  have hstable : (prefixWord ++ tailWord_829379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829379).length < 2 ^ (prefixWord ++ tailWord_829379).sum := by decide
  have hdescent : baseEnd_829379 < baseStart_829379 := by decide
  rcases family_descends (prefixWord ++ tailWord_829379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829443 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 2, 4]
def baseStart_829443 : Nat := 118140960795 + 829443 * 2 ^ 59
def prefixEnd_829443 : Nat := 4983230072969 + 3 ^ 40 * 829443 * 2
def baseEnd_829443 : Nat := 141967644835767844715989

theorem tailTrace_829443 : CollatzResearch.WordTrace tailWord_829443 prefixEnd_829443 141967644835767844715989 := by
  unfold tailWord_829443
  simp only [CollatzResearch.WordTrace]
  refine ⟨30252271534077143431572983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20168181022718095621048655 30252271534077143431572983)
  ·
    refine ⟨45378407301115715147359475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30252271534077143431572983 45378407301115715147359475)
    ·
      refine ⟨68067610951673572721039213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45378407301115715147359475 68067610951673572721039213)
      ·
        refine ⟨25525354106877589770389705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68067610951673572721039213 25525354106877589770389705)
        ·
          refine ⟨19144015580158192327792279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25525354106877589770389705 19144015580158192327792279)
          ·
            refine ⟨28716023370237288491688419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19144015580158192327792279 28716023370237288491688419)
            ·
              refine ⟨43074035055355932737532629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28716023370237288491688419 43074035055355932737532629)
              ·
                refine ⟨1009547696609904673535921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43074035055355932737532629 1009547696609904673535921)
                ·
                  refine ⟨757160772457428505151941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009547696609904673535921 757160772457428505151941)
                  ·
                    refine ⟨141967644835767844715989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757160772457428505151941 141967644835767844715989)
                    ·
                      rfl

theorem cell23_829443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 4].length) (baseStart_829443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829443 prefixEnd_829443 := by exact prefixLift 829443
  have htrace : WordTrace (prefixWord ++ tailWord_829443) baseStart_829443 baseEnd_829443 := by
    simpa [prefixWord, tailWord_829443, baseEnd_829443] using wordTrace_append hprefix tailTrace_829443
  have hstable : (prefixWord ++ tailWord_829443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829443).length < 2 ^ (prefixWord ++ tailWord_829443).sum := by decide
  have hdescent : baseEnd_829443 < baseStart_829443 := by decide
  rcases family_descends (prefixWord ++ tailWord_829443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829461 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_829461 : Nat := 118140960795 + 829461 * 2 ^ 59
def prefixEnd_829461 : Nat := 4983230072969 + 3 ^ 40 * 829461 * 2
def baseEnd_829461 : Nat := 425912177159084463722885

theorem tailTrace_829461 : CollatzResearch.WordTrace tailWord_829461 prefixEnd_829461 425912177159084463722885 := by
  unfold tailWord_829461
  simp only [CollatzResearch.WordTrace]
  refine ⟨30252928048011932505728237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20168618698674621670485491 30252928048011932505728237)
  ·
    refine ⟨11344848018004474689648089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30252928048011932505728237 11344848018004474689648089)
    ·
      refine ⟨8508636013503356017236067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11344848018004474689648089 8508636013503356017236067)
      ·
        refine ⟨12762954020255034025854101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508636013503356017236067 12762954020255034025854101)
        ·
          refine ⟨598263469699454719961911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12762954020255034025854101 598263469699454719961911)
          ·
            refine ⟨897395204549182079942867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598263469699454719961911 897395204549182079942867)
            ·
              refine ⟨1346092806823773119914301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897395204549182079942867 1346092806823773119914301)
              ·
                refine ⟨504784802558914919967863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346092806823773119914301 504784802558914919967863)
                ·
                  refine ⟨757177203838372379951795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504784802558914919967863 757177203838372379951795)
                  ·
                    refine ⟨1135765805757558569927693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757177203838372379951795 1135765805757558569927693)
                    ·
                      refine ⟨425912177159084463722885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135765805757558569927693 425912177159084463722885)
                      ·
                        rfl

theorem cell23_829461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_829461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829461 prefixEnd_829461 := by exact prefixLift 829461
  have htrace : WordTrace (prefixWord ++ tailWord_829461) baseStart_829461 baseEnd_829461 := by
    simpa [prefixWord, tailWord_829461, baseEnd_829461] using wordTrace_append hprefix tailTrace_829461
  have hstable : (prefixWord ++ tailWord_829461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829461).length < 2 ^ (prefixWord ++ tailWord_829461).sum := by decide
  have hdescent : baseEnd_829461 < baseStart_829461 := by decide
  rcases family_descends (prefixWord ++ tailWord_829461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829467 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 1, 2, 2]
def baseStart_829467 : Nat := 118140960795 + 829467 * 2 ^ 59
def prefixEnd_829467 : Nat := 4983230072969 + 3 ^ 40 * 829467 * 2
def baseEnd_829467 : Nat := 425915258043011440247857

theorem tailTrace_829467 : CollatzResearch.WordTrace tailWord_829467 prefixEnd_829467 425915258043011440247857 := by
  unfold tailWord_829467
  simp only [CollatzResearch.WordTrace]
  refine ⟨30253146885990195530446655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20168764590660130353631103 30253146885990195530446655)
  ·
    refine ⟨45379720328985293295669983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30253146885990195530446655 45379720328985293295669983)
    ·
      refine ⟨68069580493477939943504975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45379720328985293295669983 68069580493477939943504975)
      ·
        refine ⟨102104370740216909915257463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68069580493477939943504975 102104370740216909915257463)
        ·
          refine ⟨153156556110325364872886195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102104370740216909915257463 153156556110325364872886195)
          ·
            refine ⟨229734834165488047309329293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153156556110325364872886195 229734834165488047309329293)
            ·
              refine ⟨86150562812058017740998485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229734834165488047309329293 86150562812058017740998485)
              ·
                refine ⟨504788453976902447701163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 86150562812058017740998485 504788453976902447701163)
                ·
                  refine ⟨757182680965353671551745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504788453976902447701163 757182680965353671551745)
                  ·
                    refine ⟨567887010724015253663809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 757182680965353671551745 567887010724015253663809)
                    ·
                      refine ⟨425915258043011440247857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567887010724015253663809 425915258043011440247857)
                      ·
                        rfl

theorem cell23_829467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 2, 2].length) (baseStart_829467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829467 prefixEnd_829467 := by exact prefixLift 829467
  have htrace : WordTrace (prefixWord ++ tailWord_829467) baseStart_829467 baseEnd_829467 := by
    simpa [prefixWord, tailWord_829467, baseEnd_829467] using wordTrace_append hprefix tailTrace_829467
  have hstable : (prefixWord ++ tailWord_829467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829467).length < 2 ^ (prefixWord ++ tailWord_829467).sum := by decide
  have hdescent : baseEnd_829467 < baseStart_829467 := by decide
  rcases family_descends (prefixWord ++ tailWord_829467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829473 : List Nat := [1, 2, 3, 2, 4, 2, 9]
def baseStart_829473 : Nat := 118140960795 + 829473 * 2 ^ 59
def prefixEnd_829473 : Nat := 4983230072969 + 3 ^ 40 * 829473 * 2
def baseEnd_829473 : Nat := 5258251097863437244109

theorem tailTrace_829473 : CollatzResearch.WordTrace tailWord_829473 prefixEnd_829473 5258251097863437244109 := by
  unfold tailWord_829473
  simp only [CollatzResearch.WordTrace]
  refine ⟨30253365723968458555165073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20168910482645639036776715 30253365723968458555165073)
  ·
    refine ⟨22690024292976343916373805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30253365723968458555165073 22690024292976343916373805)
    ·
      refine ⟨8508759109866128968640177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22690024292976343916373805 8508759109866128968640177)
      ·
        refine ⟨6381569332399596726480133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8508759109866128968640177 6381569332399596726480133)
        ·
          refine ⟨1196544249824924386215025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6381569332399596726480133 1196544249824924386215025)
          ·
            refine ⟨897408187368693289661269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196544249824924386215025 897408187368693289661269)
            ·
              refine ⟨5258251097863437244109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 897408187368693289661269 5258251097863437244109)
              ·
                rfl

theorem cell23_829473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 9].length) (baseStart_829473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829473 prefixEnd_829473 := by exact prefixLift 829473
  have htrace : WordTrace (prefixWord ++ tailWord_829473) baseStart_829473 baseEnd_829473 := by
    simpa [prefixWord, tailWord_829473, baseEnd_829473] using wordTrace_append hprefix tailTrace_829473
  have hstable : (prefixWord ++ tailWord_829473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829473).length < 2 ^ (prefixWord ++ tailWord_829473).sum := by decide
  have hdescent : baseEnd_829473 < baseStart_829473 := by decide
  rcases family_descends (prefixWord ++ tailWord_829473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829523 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 8, 2]
def baseStart_829523 : Nat := 118140960795 + 829523 * 2 ^ 59
def prefixEnd_829523 : Nat := 4983230072969 + 3 ^ 40 * 829523 * 2
def baseEnd_829523 : Nat := 425944012959663221147599

theorem tailTrace_829523 : CollatzResearch.WordTrace tailWord_829523 prefixEnd_829523 425944012959663221147599 := by
  unfold tailWord_829523
  simp only [CollatzResearch.WordTrace]
  refine ⟨30255189373787317094485223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20170126249191544729656815 30255189373787317094485223)
  ·
    refine ⟨45382784060680975641727835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30255189373787317094485223 45382784060680975641727835)
    ·
      refine ⟨68074176091021463462591753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45382784060680975641727835 68074176091021463462591753)
      ·
        refine ⟨51055632068266097596943815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68074176091021463462591753 51055632068266097596943815)
        ·
          refine ⟨76583448102399146395415723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51055632068266097596943815 76583448102399146395415723)
          ·
            refine ⟨114875172153598719593123585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76583448102399146395415723 114875172153598719593123585)
            ·
              refine ⟨86156379115199039694842689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114875172153598719593123585 86156379115199039694842689)
              ·
                refine ⟨64617284336399279771132017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86156379115199039694842689 64617284336399279771132017)
                ·
                  refine ⟨48462963252299459828349013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64617284336399279771132017 48462963252299459828349013)
                  ·
                    refine ⟨567925350612884294863465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48462963252299459828349013 567925350612884294863465)
                    ·
                      refine ⟨425944012959663221147599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567925350612884294863465 425944012959663221147599)
                      ·
                        rfl

theorem cell23_829523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8, 2].length) (baseStart_829523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829523 prefixEnd_829523 := by exact prefixLift 829523
  have htrace : WordTrace (prefixWord ++ tailWord_829523) baseStart_829523 baseEnd_829523 := by
    simpa [prefixWord, tailWord_829523, baseEnd_829523] using wordTrace_append hprefix tailTrace_829523
  have hstable : (prefixWord ++ tailWord_829523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829523).length < 2 ^ (prefixWord ++ tailWord_829523).sum := by decide
  have hdescent : baseEnd_829523 < baseStart_829523 := by decide
  rcases family_descends (prefixWord ++ tailWord_829523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829543 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_829543 : Nat := 118140960795 + 829543 * 2 ^ 59
def prefixEnd_829543 : Nat := 4983230072969 + 3 ^ 40 * 829543 * 2
def baseEnd_829543 : Nat := 425954282572753142897507

theorem tailTrace_829543 : CollatzResearch.WordTrace tailWord_829543 prefixEnd_829543 425954282572753142897507 := by
  unfold tailWord_829543
  simp only [CollatzResearch.WordTrace]
  refine ⟨30255918833714860510213283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20170612555809907006808855 30255918833714860510213283)
  ·
    refine ⟨45383878250572290765319925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30255918833714860510213283 45383878250572290765319925)
    ·
      refine ⟨4254738585991152259248743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45383878250572290765319925 4254738585991152259248743)
      ·
        refine ⟨6382107878986728388873115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254738585991152259248743 6382107878986728388873115)
        ·
          refine ⟨9573161818480092583309673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382107878986728388873115 9573161818480092583309673)
          ·
            refine ⟨7179871363860069437482255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9573161818480092583309673 7179871363860069437482255)
            ·
              refine ⟨10769807045790104156223383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179871363860069437482255 10769807045790104156223383)
              ·
                refine ⟨16154710568685156234335075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769807045790104156223383 16154710568685156234335075)
                ·
                  refine ⟨24232065853027734351502613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16154710568685156234335075 24232065853027734351502613)
                  ·
                    refine ⟨1135878086860675047726685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24232065853027734351502613 1135878086860675047726685)
                    ·
                      refine ⟨425954282572753142897507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1135878086860675047726685 425954282572753142897507)
                      ·
                        rfl

theorem cell23_829543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_829543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829543 prefixEnd_829543 := by exact prefixLift 829543
  have htrace : WordTrace (prefixWord ++ tailWord_829543) baseStart_829543 baseEnd_829543 := by
    simpa [prefixWord, tailWord_829543, baseEnd_829543] using wordTrace_append hprefix tailTrace_829543
  have hstable : (prefixWord ++ tailWord_829543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829543).length < 2 ^ (prefixWord ++ tailWord_829543).sum := by decide
  have hdescent : baseEnd_829543 < baseStart_829543 := by decide
  rcases family_descends (prefixWord ++ tailWord_829543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829553 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_829553 : Nat := 118140960795 + 829553 * 2 ^ 59
def prefixEnd_829553 : Nat := 4983230072969 + 3 ^ 40 * 829553 * 2
def baseEnd_829553 : Nat := 425959417379298103772461

theorem tailTrace_829553 : CollatzResearch.WordTrace tailWord_829553 prefixEnd_829553 425959417379298103772461 := by
  unfold tailWord_829553
  simp only [CollatzResearch.WordTrace]
  refine ⟨30256283563678632218077313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20170855709119088145384875 30256283563678632218077313)
  ·
    refine ⟨22692212672758974163557985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30256283563678632218077313 22692212672758974163557985)
    ·
      refine ⟨17019159504569230622668489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22692212672758974163557985 17019159504569230622668489)
      ·
        refine ⟨12764369628426922967001367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17019159504569230622668489 12764369628426922967001367)
        ·
          refine ⟨19146554442640384450502051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12764369628426922967001367 19146554442640384450502051)
          ·
            refine ⟨28719831663960576675753077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19146554442640384450502051 28719831663960576675753077)
            ·
              refine ⟨2692484218496304063351851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28719831663960576675753077 2692484218496304063351851)
              ·
                refine ⟨4038726327744456095027777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692484218496304063351851 4038726327744456095027777)
                ·
                  refine ⟨3029044745808342071270833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038726327744456095027777 3029044745808342071270833)
                  ·
                    refine ⟨2271783559356256553453125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3029044745808342071270833 2271783559356256553453125)
                    ·
                      refine ⟨425959417379298103772461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2271783559356256553453125 425959417379298103772461)
                      ·
                        rfl

theorem cell23_829553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_829553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829553 prefixEnd_829553 := by exact prefixLift 829553
  have htrace : WordTrace (prefixWord ++ tailWord_829553) baseStart_829553 baseEnd_829553 := by
    simpa [prefixWord, tailWord_829553, baseEnd_829553] using wordTrace_append hprefix tailTrace_829553
  have hstable : (prefixWord ++ tailWord_829553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829553).length < 2 ^ (prefixWord ++ tailWord_829553).sum := by decide
  have hdescent : baseEnd_829553 < baseStart_829553 := by decide
  rcases family_descends (prefixWord ++ tailWord_829553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829591 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 2, 2, 2]
def baseStart_829591 : Nat := 118140960795 + 829591 * 2 ^ 59
def prefixEnd_829591 : Nat := 4983230072969 + 3 ^ 40 * 829591 * 2
def baseEnd_829591 : Nat := 425978929644168955097287

theorem tailTrace_829591 : CollatzResearch.WordTrace tailWord_829591 prefixEnd_829591 425978929644168955097287 := by
  unfold tailWord_829591
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257669537540964707960627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20171779691693976471973751 30257669537540964707960627)
  ·
    refine ⟨45386504306311447061940941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30257669537540964707960627 45386504306311447061940941)
    ·
      refine ⟨17019939114866792648227853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45386504306311447061940941 17019939114866792648227853)
      ·
        refine ⟨6382477168075047243085445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17019939114866792648227853 6382477168075047243085445)
        ·
          refine ⟨1196714469014071358078521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6382477168075047243085445 1196714469014071358078521)
          ·
            refine ⟨897535851760553518558891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196714469014071358078521 897535851760553518558891)
            ·
              refine ⟨1346303777640830277838337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897535851760553518558891 1346303777640830277838337)
              ·
                refine ⟨1009727833230622708378753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346303777640830277838337 1009727833230622708378753)
                ·
                  refine ⟨757295874922967031284065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009727833230622708378753 757295874922967031284065)
                  ·
                    refine ⟨567971906192225273463049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 757295874922967031284065 567971906192225273463049)
                    ·
                      refine ⟨425978929644168955097287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567971906192225273463049 425978929644168955097287)
                      ·
                        rfl

theorem cell23_829591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_829591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829591 prefixEnd_829591 := by exact prefixLift 829591
  have htrace : WordTrace (prefixWord ++ tailWord_829591) baseStart_829591 baseEnd_829591 := by
    simpa [prefixWord, tailWord_829591, baseEnd_829591] using wordTrace_append hprefix tailTrace_829591
  have hstable : (prefixWord ++ tailWord_829591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829591).length < 2 ^ (prefixWord ++ tailWord_829591).sum := by decide
  have hdescent : baseEnd_829591 < baseStart_829591 := by decide
  rcases family_descends (prefixWord ++ tailWord_829591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829593 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_829593 : Nat := 118140960795 + 829593 * 2 ^ 59
def prefixEnd_829593 : Nat := 4983230072969 + 3 ^ 40 * 829593 * 2
def baseEnd_829593 : Nat := 141993318868492649090759

theorem tailTrace_829593 : CollatzResearch.WordTrace tailWord_829593 prefixEnd_829593 141993318868492649090759 := by
  unfold tailWord_829593
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257742483533719049533433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20171828322355812699688955 30257742483533719049533433)
  ·
    refine ⟨22693306862650289287150075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30257742483533719049533433 22693306862650289287150075)
    ·
      refine ⟨34039960293975433930725113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22693306862650289287150075 34039960293975433930725113)
      ·
        refine ⟨25529970220481575448043835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34039960293975433930725113 25529970220481575448043835)
        ·
          refine ⟨38294955330722363172065753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25529970220481575448043835 38294955330722363172065753)
          ·
            refine ⟨28721216498041772379049315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38294955330722363172065753 28721216498041772379049315)
            ·
              refine ⟨43081824747062658568573973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28721216498041772379049315 43081824747062658568573973)
              ·
                refine ⟨2019460535018562120401905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43081824747062658568573973 2019460535018562120401905)
                ·
                  refine ⟨1514595401263921590301429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2019460535018562120401905 1514595401263921590301429)
                  ·
                    refine ⟨141993318868492649090759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1514595401263921590301429 141993318868492649090759)
                    ·
                      rfl

theorem cell23_829593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_829593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829593 prefixEnd_829593 := by exact prefixLift 829593
  have htrace : WordTrace (prefixWord ++ tailWord_829593) baseStart_829593 baseEnd_829593 := by
    simpa [prefixWord, tailWord_829593, baseEnd_829593] using wordTrace_append hprefix tailTrace_829593
  have hstable : (prefixWord ++ tailWord_829593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829593).length < 2 ^ (prefixWord ++ tailWord_829593).sum := by decide
  have hdescent : baseEnd_829593 < baseStart_829593 := by decide
  rcases family_descends (prefixWord ++ tailWord_829593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829657 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 1, 4]
def baseStart_829657 : Nat := 118140960795 + 829657 * 2 ^ 59
def prefixEnd_829657 : Nat := 4983230072969 + 3 ^ 40 * 829657 * 2
def baseEnd_829657 : Nat := 142004273122455232290661

theorem tailTrace_829657 : CollatzResearch.WordTrace tailWord_829657 prefixEnd_829657 142004273122455232290661 := by
  unfold tailWord_829657
  simp only [CollatzResearch.WordTrace]
  refine ⟨30260076755301857979863225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20173384503534571986575483 30260076755301857979863225)
  ·
    refine ⟨22695057566476393484897419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30260076755301857979863225 22695057566476393484897419)
    ·
      refine ⟨34042586349714590227346129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22695057566476393484897419 34042586349714590227346129)
      ·
        refine ⟨25531939762285942670509597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34042586349714590227346129 25531939762285942670509597)
        ·
          refine ⟨9574477410857228501441099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25531939762285942670509597 9574477410857228501441099)
          ·
            refine ⟨14361716116285842752161649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574477410857228501441099 14361716116285842752161649)
            ·
              refine ⟨10771287087214382064121237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361716116285842752161649 10771287087214382064121237)
              ·
                refine ⟨504904082213174159255683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10771287087214382064121237 504904082213174159255683)
                ·
                  refine ⟨757356123319761238883525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504904082213174159255683 757356123319761238883525)
                  ·
                    refine ⟨142004273122455232290661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757356123319761238883525 142004273122455232290661)
                    ·
                      rfl

theorem cell23_829657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 4].length) (baseStart_829657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829657 prefixEnd_829657 := by exact prefixLift 829657
  have htrace : WordTrace (prefixWord ++ tailWord_829657) baseStart_829657 baseEnd_829657 := by
    simpa [prefixWord, tailWord_829657, baseEnd_829657] using wordTrace_append hprefix tailTrace_829657
  have hstable : (prefixWord ++ tailWord_829657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829657).length < 2 ^ (prefixWord ++ tailWord_829657).sum := by decide
  have hdescent : baseEnd_829657 < baseStart_829657 := by decide
  rcases family_descends (prefixWord ++ tailWord_829657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829693 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_829693 : Nat := 118140960795 + 829693 * 2 ^ 59
def prefixEnd_829693 : Nat := 4983230072969 + 3 ^ 40 * 829693 * 2
def baseEnd_829693 : Nat := 426031304670927556021817

theorem tailTrace_829693 : CollatzResearch.WordTrace tailWord_829693 prefixEnd_829693 426031304670927556021817 := by
  unfold tailWord_829693
  simp only [CollatzResearch.WordTrace]
  refine ⟨30261389783171436128173733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20174259855447624085449155 30261389783171436128173733)
  ·
    refine ⟨5674010584344644274032575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30261389783171436128173733 5674010584344644274032575)
    ·
      refine ⟨8511015876516966411048863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5674010584344644274032575 8511015876516966411048863)
      ·
        refine ⟨12766523814775449616573295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511015876516966411048863 12766523814775449616573295)
        ·
          refine ⟨19149785722163174424859943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12766523814775449616573295 19149785722163174424859943)
          ·
            refine ⟨28724678583244761637289915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19149785722163174424859943 28724678583244761637289915)
            ·
              refine ⟨43087017874867142455934873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28724678583244761637289915 43087017874867142455934873)
              ·
                refine ⟨32315263406150356841951155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43087017874867142455934873 32315263406150356841951155)
                ·
                  refine ⟨48472895109225535262926733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32315263406150356841951155 48472895109225535262926733)
                  ·
                    refine ⟨18177335665959575723597525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48472895109225535262926733 18177335665959575723597525)
                    ·
                      refine ⟨426031304670927556021817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18177335665959575723597525 426031304670927556021817)
                      ·
                        rfl

theorem cell23_829693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_829693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829693 prefixEnd_829693 := by exact prefixLift 829693
  have htrace : WordTrace (prefixWord ++ tailWord_829693) baseStart_829693 baseEnd_829693 := by
    simpa [prefixWord, tailWord_829693, baseEnd_829693] using wordTrace_append hprefix tailTrace_829693
  have hstable : (prefixWord ++ tailWord_829693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829693).length < 2 ^ (prefixWord ++ tailWord_829693).sum := by decide
  have hdescent : baseEnd_829693 < baseStart_829693 := by decide
  rcases family_descends (prefixWord ++ tailWord_829693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829707 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 2, 3, 2]
def baseStart_829707 : Nat := 118140960795 + 829707 * 2 ^ 59
def prefixEnd_829707 : Nat := 4983230072969 + 3 ^ 40 * 829707 * 2
def baseEnd_829707 : Nat := 426038493400090501246753

theorem tailTrace_829707 : CollatzResearch.WordTrace tailWord_829707 prefixEnd_829707 426038493400090501246753 := by
  unfold tailWord_829707
  simp only [CollatzResearch.WordTrace]
  refine ⟨30261900405120716519183375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20174600270080477679455583 30261900405120716519183375)
  ·
    refine ⟨45392850607681074778775063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30261900405120716519183375 45392850607681074778775063)
    ·
      refine ⟨68089275911521612168162595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45392850607681074778775063 68089275911521612168162595)
      ·
        refine ⟨102133913867282418252243893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68089275911521612168162595 102133913867282418252243893)
        ·
          refine ⟨9575054425057726711147865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102133913867282418252243893 9575054425057726711147865)
          ·
            refine ⟨7181290818793295033360899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9575054425057726711147865 7181290818793295033360899)
            ·
              refine ⟨10771936228189942550041349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181290818793295033360899 10771936228189942550041349)
              ·
                refine ⟨2019738042785614228132753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10771936228189942550041349 2019738042785614228132753)
                ·
                  refine ⟨1514803532089210671099565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2019738042785614228132753 1514803532089210671099565)
                  ·
                    refine ⟨568051324533454001662337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1514803532089210671099565 568051324533454001662337)
                    ·
                      refine ⟨426038493400090501246753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568051324533454001662337 426038493400090501246753)
                      ·
                        rfl

theorem cell23_829707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3, 2].length) (baseStart_829707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829707 prefixEnd_829707 := by exact prefixLift 829707
  have htrace : WordTrace (prefixWord ++ tailWord_829707) baseStart_829707 baseEnd_829707 := by
    simpa [prefixWord, tailWord_829707, baseEnd_829707] using wordTrace_append hprefix tailTrace_829707
  have hstable : (prefixWord ++ tailWord_829707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829707).length < 2 ^ (prefixWord ++ tailWord_829707).sum := by decide
  have hdescent : baseEnd_829707 < baseStart_829707 := by decide
  rcases family_descends (prefixWord ++ tailWord_829707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829720 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_829720 : Nat := 118140960795 + 829720 * 2 ^ 59
def prefixEnd_829720 : Nat := 4983230072969 + 3 ^ 40 * 829720 * 2
def baseEnd_829720 : Nat := 426045168648598950384193

theorem tailTrace_829720 : CollatzResearch.WordTrace tailWord_829720 prefixEnd_829720 426045168648598950384193 := by
  unfold tailWord_829720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15131187277036809869703307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20174916369382413159604409 15131187277036809869703307)
  ·
    refine ⟨22696780915555214804554961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15131187277036809869703307 22696780915555214804554961)
    ·
      refine ⟨17022585686666411103416221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22696780915555214804554961 17022585686666411103416221)
      ·
        refine ⟨6383469632499904163781083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17022585686666411103416221 6383469632499904163781083)
        ·
          refine ⟨9575204448749856245671625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383469632499904163781083 9575204448749856245671625)
          ·
            refine ⟨7181403336562392184253719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9575204448749856245671625 7181403336562392184253719)
            ·
              refine ⟨10772105004843588276380579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181403336562392184253719 10772105004843588276380579)
              ·
                refine ⟨16158157507265382414570869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10772105004843588276380579 16158157507265382414570869)
                ·
                  refine ⟨1514827266306129601366019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16158157507265382414570869 1514827266306129601366019)
                  ·
                    refine ⟨2272240899459194402049029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514827266306129601366019 2272240899459194402049029)
                    ·
                      refine ⟨426045168648598950384193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2272240899459194402049029 426045168648598950384193)
                      ·
                        rfl

theorem cell23_829720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_829720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829720 prefixEnd_829720 := by exact prefixLift 829720
  have htrace : WordTrace (prefixWord ++ tailWord_829720) baseStart_829720 baseEnd_829720 := by
    simpa [prefixWord, tailWord_829720, baseEnd_829720] using wordTrace_append hprefix tailTrace_829720
  have hstable : (prefixWord ++ tailWord_829720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829720).length < 2 ^ (prefixWord ++ tailWord_829720).sum := by decide
  have hdescent : baseEnd_829720 < baseStart_829720 := by decide
  rcases family_descends (prefixWord ++ tailWord_829720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829735 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_829735 : Nat := 118140960795 + 829735 * 2 ^ 59
def prefixEnd_829735 : Nat := 4983230072969 + 3 ^ 40 * 829735 * 2
def baseEnd_829735 : Nat := 426052870858416391696625

theorem tailTrace_829735 : CollatzResearch.WordTrace tailWord_829735 prefixEnd_829735 426052870858416391696625 := by
  unfold tailWord_829735
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262921649019277301202659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20175281099346184867468439 30262921649019277301202659)
  ·
    refine ⟨45394382473528915951803989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30262921649019277301202659 45394382473528915951803989)
    ·
      refine ⟨531965419611666983810203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 45394382473528915951803989 531965419611666983810203)
      ·
        refine ⟨797948129417500475715305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531965419611666983810203 797948129417500475715305)
        ·
          refine ⟨598461097063125356786479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797948129417500475715305 598461097063125356786479)
          ·
            refine ⟨897691645594688035179719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598461097063125356786479 897691645594688035179719)
            ·
              refine ⟨1346537468392032052769579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897691645594688035179719 1346537468392032052769579)
              ·
                refine ⟨2019806202588048079154369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346537468392032052769579 2019806202588048079154369)
                ·
                  refine ⟨1514854651941036059365777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2019806202588048079154369 1514854651941036059365777)
                  ·
                    refine ⟨1136140988955777044524333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1514854651941036059365777 1136140988955777044524333)
                    ·
                      refine ⟨426052870858416391696625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136140988955777044524333 426052870858416391696625)
                      ·
                        rfl

theorem cell23_829735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_829735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829735 prefixEnd_829735 := by exact prefixLift 829735
  have htrace : WordTrace (prefixWord ++ tailWord_829735) baseStart_829735 baseEnd_829735 := by
    simpa [prefixWord, tailWord_829735, baseEnd_829735] using wordTrace_append hprefix tailTrace_829735
  have hstable : (prefixWord ++ tailWord_829735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829735).length < 2 ^ (prefixWord ++ tailWord_829735).sum := by decide
  have hdescent : baseEnd_829735 < baseStart_829735 := by decide
  rcases family_descends (prefixWord ++ tailWord_829735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829741 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_829741 : Nat := 118140960795 + 829741 * 2 ^ 59
def prefixEnd_829741 : Nat := 4983230072969 + 3 ^ 40 * 829741 * 2
def baseEnd_829741 : Nat := 426055951742343368221597

theorem tailTrace_829741 : CollatzResearch.WordTrace tailWord_829741 prefixEnd_829741 426055951742343368221597 := by
  unfold tailWord_829741
  simp only [CollatzResearch.WordTrace]
  refine ⟨30263140486997540325921077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20175426991331693550614051 30263140486997540325921077)
  ·
    refine ⟨2837169420656019405555101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30263140486997540325921077 2837169420656019405555101)
    ·
      refine ⟨1063938532746007277083163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2837169420656019405555101 1063938532746007277083163)
      ·
        refine ⟨1595907799119010915624745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063938532746007277083163 1595907799119010915624745)
        ·
          refine ⟨1196930849339258186718559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595907799119010915624745 1196930849339258186718559)
          ·
            refine ⟨1795396274008887280077839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196930849339258186718559 1795396274008887280077839)
            ·
              refine ⟨2693094411013330920116759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795396274008887280077839 2693094411013330920116759)
              ·
                refine ⟨4039641616519996380175139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693094411013330920116759 4039641616519996380175139)
                ·
                  refine ⟨6059462424779994570262709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039641616519996380175139 6059462424779994570262709)
                  ·
                    refine ⟨568074602323124490962129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6059462424779994570262709 568074602323124490962129)
                    ·
                      refine ⟨426055951742343368221597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568074602323124490962129 426055951742343368221597)
                      ·
                        rfl

theorem cell23_829741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_829741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829741 prefixEnd_829741 := by exact prefixLift 829741
  have htrace : WordTrace (prefixWord ++ tailWord_829741) baseStart_829741 baseEnd_829741 := by
    simpa [prefixWord, tailWord_829741, baseEnd_829741] using wordTrace_append hprefix tailTrace_829741
  have hstable : (prefixWord ++ tailWord_829741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829741).length < 2 ^ (prefixWord ++ tailWord_829741).sum := by decide
  have hdescent : baseEnd_829741 < baseStart_829741 := by decide
  rcases family_descends (prefixWord ++ tailWord_829741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829743 : List Nat := [1, 1, 2, 1, 2, 1, 4, 11]
def baseStart_829743 : Nat := 118140960795 + 829743 * 2 ^ 59
def prefixEnd_829743 : Nat := 4983230072969 + 3 ^ 40 * 829743 * 2
def baseEnd_829743 : Nat := 15779888100135272607281

theorem tailTrace_829743 : CollatzResearch.WordTrace tailWord_829743 prefixEnd_829743 15779888100135272607281 := by
  unfold tailWord_829743
  simp only [CollatzResearch.WordTrace]
  refine ⟨30263213432990294667493883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20175475621993529778329255 30263213432990294667493883)
  ·
    refine ⟨45394820149485442001240825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30263213432990294667493883 45394820149485442001240825)
    ·
      refine ⟨34046115112114081500930619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45394820149485442001240825 34046115112114081500930619)
      ·
        refine ⟨51069172668171122251395929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34046115112114081500930619 51069172668171122251395929)
        ·
          refine ⟨38301879501128341688546947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51069172668171122251395929 38301879501128341688546947)
          ·
            refine ⟨57452819251692512532820421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38301879501128341688546947 57452819251692512532820421)
            ·
              refine ⟨10772403609692346099903829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57452819251692512532820421 10772403609692346099903829)
              ·
                refine ⟨15779888100135272607281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 10772403609692346099903829 15779888100135272607281)
                ·
                  rfl

theorem cell23_829743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 11].length) (baseStart_829743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829743 prefixEnd_829743 := by exact prefixLift 829743
  have htrace : WordTrace (prefixWord ++ tailWord_829743) baseStart_829743 baseEnd_829743 := by
    simpa [prefixWord, tailWord_829743, baseEnd_829743] using wordTrace_append hprefix tailTrace_829743
  have hstable : (prefixWord ++ tailWord_829743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829743).length < 2 ^ (prefixWord ++ tailWord_829743).sum := by decide
  have hdescent : baseEnd_829743 < baseStart_829743 := by decide
  rcases family_descends (prefixWord ++ tailWord_829743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829748 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_829748 : Nat := 118140960795 + 829748 * 2 ^ 59
def prefixEnd_829748 : Nat := 4983230072969 + 3 ^ 40 * 829748 * 2
def baseEnd_829748 : Nat := 426059546106924840834065

theorem tailTrace_829748 : CollatzResearch.WordTrace tailWord_829748 prefixEnd_829748 426059546106924840834065 := by
  unfold tailWord_829748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15131697898986090260712949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20175597198648120347617265 15131697898986090260712949)
  ·
    refine ⟨1418596678029945961941839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15131697898986090260712949 1418596678029945961941839)
    ·
      refine ⟨2127895017044918942912759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418596678029945961941839 2127895017044918942912759)
      ·
        refine ⟨3191842525567378414369139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127895017044918942912759 3191842525567378414369139)
        ·
          refine ⟨4787763788351067621553709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191842525567378414369139 4787763788351067621553709)
          ·
            refine ⟨1795411420631650358082641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4787763788351067621553709 1795411420631650358082641)
            ·
              refine ⟨1346558565473737768561981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795411420631650358082641 1346558565473737768561981)
              ·
                refine ⟨504959462052651663210743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346558565473737768561981 504959462052651663210743)
                ·
                  refine ⟨757439193078977494816115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504959462052651663210743 757439193078977494816115)
                  ·
                    refine ⟨1136158789618466242224173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757439193078977494816115 1136158789618466242224173)
                    ·
                      refine ⟨426059546106924840834065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136158789618466242224173 426059546106924840834065)
                      ·
                        rfl

theorem cell23_829748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_829748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829748 prefixEnd_829748 := by exact prefixLift 829748
  have htrace : WordTrace (prefixWord ++ tailWord_829748) baseStart_829748 baseEnd_829748 := by
    simpa [prefixWord, tailWord_829748, baseEnd_829748] using wordTrace_append hprefix tailTrace_829748
  have hstable : (prefixWord ++ tailWord_829748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829748).length < 2 ^ (prefixWord ++ tailWord_829748).sum := by decide
  have hdescent : baseEnd_829748 < baseStart_829748 := by decide
  rcases family_descends (prefixWord ++ tailWord_829748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829754 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4]
def baseStart_829754 : Nat := 118140960795 + 829754 * 2 ^ 59
def prefixEnd_829754 : Nat := 4983230072969 + 3 ^ 40 * 829754 * 2
def baseEnd_829754 : Nat := 426062626990851817359037

theorem tailTrace_829754 : CollatzResearch.WordTrace tailWord_829754 prefixEnd_829754 426062626990851817359037 := by
  unfold tailWord_829754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565903658987610886536079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20175743090633629030762877 7565903658987610886536079)
  ·
    refine ⟨11348855488481416329804119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7565903658987610886536079 11348855488481416329804119)
    ·
      refine ⟨17023283232722124494706179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11348855488481416329804119 17023283232722124494706179)
      ·
        refine ⟨25534924849083186742059269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17023283232722124494706179 25534924849083186742059269)
        ·
          refine ⟨4787798409203097514136113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25534924849083186742059269 4787798409203097514136113)
          ·
            refine ⟨3590848806902323135602085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4787798409203097514136113 3590848806902323135602085)
            ·
              refine ⟨673284151294185587925391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3590848806902323135602085 673284151294185587925391)
              ·
                refine ⟨1009926226941278381888087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673284151294185587925391 1009926226941278381888087)
                ·
                  refine ⟨1514889340411917572832131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009926226941278381888087 1514889340411917572832131)
                  ·
                    refine ⟨2272334010617876359248197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1514889340411917572832131 2272334010617876359248197)
                    ·
                      refine ⟨426062626990851817359037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2272334010617876359248197 426062626990851817359037)
                      ·
                        rfl

theorem cell23_829754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_829754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829754 prefixEnd_829754 := by exact prefixLift 829754
  have htrace : WordTrace (prefixWord ++ tailWord_829754) baseStart_829754 baseEnd_829754 := by
    simpa [prefixWord, tailWord_829754, baseEnd_829754] using wordTrace_append hprefix tailTrace_829754
  have hstable : (prefixWord ++ tailWord_829754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829754).length < 2 ^ (prefixWord ++ tailWord_829754).sum := by decide
  have hdescent : baseEnd_829754 < baseStart_829754 := by decide
  rcases family_descends (prefixWord ++ tailWord_829754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829770 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_829770 : Nat := 118140960795 + 829770 * 2 ^ 59
def prefixEnd_829770 : Nat := 4983230072969 + 3 ^ 40 * 829770 * 2
def baseEnd_829770 : Nat := 426070842681323754758963

theorem tailTrace_829770 : CollatzResearch.WordTrace tailWord_829770 prefixEnd_829770 426070842681323754758963 := by
  unfold tailWord_829770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566049550973119569681691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20176132135928318852484509 7566049550973119569681691)
  ·
    refine ⟨11349074326459679354522537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7566049550973119569681691 11349074326459679354522537)
    ·
      refine ⟨8511805744844759515891903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11349074326459679354522537 8511805744844759515891903)
      ·
        refine ⟨12767708617267139273837855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511805744844759515891903 12767708617267139273837855)
        ·
          refine ⟨19151562925900708910756783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12767708617267139273837855 19151562925900708910756783)
          ·
            refine ⟨28727344388851063366135175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19151562925900708910756783 28727344388851063366135175)
            ·
              refine ⟨43091016583276595049202763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28727344388851063366135175 43091016583276595049202763)
              ·
                refine ⟨64636524874914892573804145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43091016583276595049202763 64636524874914892573804145)
                ·
                  refine ⟨48477393656186169430353109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64636524874914892573804145 48477393656186169430353109)
                  ·
                    refine ⟨1136188913816863346023901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48477393656186169430353109 1136188913816863346023901)
                    ·
                      refine ⟨426070842681323754758963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136188913816863346023901 426070842681323754758963)
                      ·
                        rfl

theorem cell23_829770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_829770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829770 prefixEnd_829770 := by exact prefixLift 829770
  have htrace : WordTrace (prefixWord ++ tailWord_829770) baseStart_829770 baseEnd_829770 := by
    simpa [prefixWord, tailWord_829770, baseEnd_829770] using wordTrace_append hprefix tailTrace_829770
  have hstable : (prefixWord ++ tailWord_829770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829770).length < 2 ^ (prefixWord ++ tailWord_829770).sum := by decide
  have hdescent : baseEnd_829770 < baseStart_829770 := by decide
  rcases family_descends (prefixWord ++ tailWord_829770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829781 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_829781 : Nat := 118140960795 + 829781 * 2 ^ 59
def prefixEnd_829781 : Nat := 4983230072969 + 3 ^ 40 * 829781 * 2
def baseEnd_829781 : Nat := 142025496989507737240471

theorem tailTrace_829781 : CollatzResearch.WordTrace tailWord_829781 prefixEnd_829781 142025496989507737240471 := by
  unfold tailWord_829781
  simp only [CollatzResearch.WordTrace]
  refine ⟨30264599406852627157377197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20176399604568418104918131 30264599406852627157377197)
  ·
    refine ⟨11349224777569735184016449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30264599406852627157377197 11349224777569735184016449)
    ·
      refine ⟨8511918583177301388012337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11349224777569735184016449 8511918583177301388012337)
      ·
        refine ⟨6383938937382976041009253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8511918583177301388012337 6383938937382976041009253)
        ·
          refine ⟨1196988550759308007689235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6383938937382976041009253 1196988550759308007689235)
          ·
            refine ⟨1795482826138962011533853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196988550759308007689235 1795482826138962011533853)
            ·
              refine ⟨673306059802110754325195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1795482826138962011533853 673306059802110754325195)
              ·
                refine ⟨1009959089703166131487793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673306059802110754325195 1009959089703166131487793)
                ·
                  refine ⟨757469317277374598615845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009959089703166131487793 757469317277374598615845)
                  ·
                    refine ⟨142025496989507737240471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757469317277374598615845 142025496989507737240471)
                    ·
                      rfl

theorem cell23_829781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_829781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829781 prefixEnd_829781 := by exact prefixLift 829781
  have htrace : WordTrace (prefixWord ++ tailWord_829781) baseStart_829781 baseEnd_829781 := by
    simpa [prefixWord, tailWord_829781, baseEnd_829781] using wordTrace_append hprefix tailTrace_829781
  have hstable : (prefixWord ++ tailWord_829781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829781).length < 2 ^ (prefixWord ++ tailWord_829781).sum := by decide
  have hdescent : baseEnd_829781 < baseStart_829781 := by decide
  rcases family_descends (prefixWord ++ tailWord_829781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829794 : List Nat := [3, 3, 2, 1, 1, 4, 2, 7]
def baseStart_829794 : Nat := 118140960795 + 829794 * 2 ^ 59
def prefixEnd_829794 : Nat := 4983230072969 + 3 ^ 40 * 829794 * 2
def baseEnd_829794 : Nat := 15780858008038209661439

theorem tailTrace_829794 : CollatzResearch.WordTrace tailWord_829794 prefixEnd_829794 15780858008038209661439 := by
  unfold tailWord_829794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566268388951382594400109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20176715703870353585066957 7566268388951382594400109)
  ·
    refine ⟨2837350645856768472900041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7566268388951382594400109 2837350645856768472900041)
    ·
      refine ⟨2128012984392576354675031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2837350645856768472900041 2128012984392576354675031)
      ·
        refine ⟨3192019476588864532012547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128012984392576354675031 3192019476588864532012547)
        ·
          refine ⟨4788029214883296798018821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192019476588864532012547 4788029214883296798018821)
          ·
            refine ⟨897755477790618149628529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4788029214883296798018821 897755477790618149628529)
            ·
              refine ⟨673316608342963612221397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897755477790618149628529 673316608342963612221397)
              ·
                refine ⟨15780858008038209661439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 673316608342963612221397 15780858008038209661439)
                ·
                  rfl

theorem cell23_829794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_829794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829794 prefixEnd_829794 := by exact prefixLift 829794
  have htrace : WordTrace (prefixWord ++ tailWord_829794) baseStart_829794 baseEnd_829794 := by
    simpa [prefixWord, tailWord_829794, baseEnd_829794] using wordTrace_append hprefix tailTrace_829794
  have hstable : (prefixWord ++ tailWord_829794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829794).length < 2 ^ (prefixWord ++ tailWord_829794).sum := by decide
  have hdescent : baseEnd_829794 < baseStart_829794 := by decide
  rcases family_descends (prefixWord ++ tailWord_829794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829820 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_829820 : Nat := 118140960795 + 829820 * 2 ^ 59
def prefixEnd_829820 : Nat := 4983230072969 + 3 ^ 40 * 829820 * 2
def baseEnd_829820 : Nat := 142032172238016186377911

theorem tailTrace_829820 : CollatzResearch.WordTrace tailWord_829820 prefixEnd_829820 142032172238016186377911 := by
  unfold tailWord_829820
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133010926855668409023457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20177347902474224545364609 15133010926855668409023457)
  ·
    refine ⟨11349758195141751306767593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15133010926855668409023457 11349758195141751306767593)
    ·
      refine ⟨8512318646356313480075695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11349758195141751306767593 8512318646356313480075695)
      ·
        refine ⟨12768477969534470220113543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8512318646356313480075695 12768477969534470220113543)
        ·
          refine ⟨19152716954301705330170315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12768477969534470220113543 19152716954301705330170315)
          ·
            refine ⟨28729075431452557995255473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19152716954301705330170315 28729075431452557995255473)
            ·
              refine ⟨21546806573589418496441605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28729075431452557995255473 21546806573589418496441605)
              ·
                refine ⟨4040026232548015968082801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21546806573589418496441605 4040026232548015968082801)
                ·
                  refine ⟨3030019674411011976062101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040026232548015968082801 3030019674411011976062101)
                  ·
                    refine ⟨142032172238016186377911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3030019674411011976062101 142032172238016186377911)
                    ·
                      rfl

theorem cell23_829820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_829820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829820 prefixEnd_829820 := by exact prefixLift 829820
  have htrace : WordTrace (prefixWord ++ tailWord_829820) baseStart_829820 baseEnd_829820 := by
    simpa [prefixWord, tailWord_829820, baseEnd_829820] using wordTrace_append hprefix tailTrace_829820
  have hstable : (prefixWord ++ tailWord_829820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829820).length < 2 ^ (prefixWord ++ tailWord_829820).sum := by decide
  have hdescent : baseEnd_829820 < baseStart_829820 := by decide
  rcases family_descends (prefixWord ++ tailWord_829820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829838 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_829838 : Nat := 118140960795 + 829838 * 2 ^ 59
def prefixEnd_829838 : Nat := 4983230072969 + 3 ^ 40 * 829838 * 2
def baseEnd_829838 : Nat := 426105759365829488708651

theorem tailTrace_829838 : CollatzResearch.WordTrace tailWord_829838 prefixEnd_829838 426105759365829488708651 := by
  unfold tailWord_829838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3783334795955765736525271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20177785578430750594801445 3783334795955765736525271)
  ·
    refine ⟨5675002193933648604787907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3783334795955765736525271 5675002193933648604787907)
    ·
      refine ⟨8512503290900472907181861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5675002193933648604787907 8512503290900472907181861)
      ·
        refine ⟨1596094367043838670096599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8512503290900472907181861 1596094367043838670096599)
        ·
          refine ⟨2394141550565758005144899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596094367043838670096599 2394141550565758005144899)
          ·
            refine ⟨3591212325848637007717349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394141550565758005144899 3591212325848637007717349)
            ·
              refine ⟨673352311096619438947003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3591212325848637007717349 673352311096619438947003)
              ·
                refine ⟨1010028466644929158420505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673352311096619438947003 1010028466644929158420505)
                ·
                  refine ⟨757521349983696868815379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010028466644929158420505 757521349983696868815379)
                  ·
                    refine ⟨1136282024975545303223069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757521349983696868815379 1136282024975545303223069)
                    ·
                      refine ⟨426105759365829488708651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136282024975545303223069 426105759365829488708651)
                      ·
                        rfl

theorem cell23_829838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_829838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829838 prefixEnd_829838 := by exact prefixLift 829838
  have htrace : WordTrace (prefixWord ++ tailWord_829838) baseStart_829838 baseEnd_829838 := by
    simpa [prefixWord, tailWord_829838, baseEnd_829838] using wordTrace_append hprefix tailTrace_829838
  have hstable : (prefixWord ++ tailWord_829838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829838).length < 2 ^ (prefixWord ++ tailWord_829838).sum := by decide
  have hdescent : baseEnd_829838 < baseStart_829838 := by decide
  rcases family_descends (prefixWord ++ tailWord_829838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829848 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 1, 3, 2]
def baseStart_829848 : Nat := 118140960795 + 829848 * 2 ^ 59
def prefixEnd_829848 : Nat := 4983230072969 + 3 ^ 40 * 829848 * 2
def baseEnd_829848 : Nat := 426110894172374449583605

theorem tailTrace_829848 : CollatzResearch.WordTrace tailWord_829848 prefixEnd_829848 426110894172374449583605 := by
  unfold tailWord_829848
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133521548804948800033099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20178028731739931733377465 15133521548804948800033099)
  ·
    refine ⟨22700282323207423200049649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15133521548804948800033099 22700282323207423200049649)
    ·
      refine ⟨17025211742405567400037237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22700282323207423200049649 17025211742405567400037237)
      ·
        refine ⟨1596113600850521943753491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17025211742405567400037237 1596113600850521943753491)
        ·
          refine ⟨2394170401275782915630237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596113600850521943753491 2394170401275782915630237)
          ·
            refine ⟨897813900478418593361339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2394170401275782915630237 897813900478418593361339)
            ·
              refine ⟨1346720850717627890042009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897813900478418593361339 1346720850717627890042009)
              ·
                refine ⟨1010040638038220917531507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346720850717627890042009 1010040638038220917531507)
                ·
                  refine ⟨1515060957057331376297261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010040638038220917531507 1515060957057331376297261)
                  ·
                    refine ⟨568147858896499266111473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515060957057331376297261 568147858896499266111473)
                    ·
                      refine ⟨426110894172374449583605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568147858896499266111473 426110894172374449583605)
                      ·
                        rfl

theorem cell23_829848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_829848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829848 prefixEnd_829848 := by exact prefixLift 829848
  have htrace : WordTrace (prefixWord ++ tailWord_829848) baseStart_829848 baseEnd_829848 := by
    simpa [prefixWord, tailWord_829848, baseEnd_829848] using wordTrace_append hprefix tailTrace_829848
  have hstable : (prefixWord ++ tailWord_829848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829848).length < 2 ^ (prefixWord ++ tailWord_829848).sum := by decide
  have hdescent : baseEnd_829848 < baseStart_829848 := by decide
  rcases family_descends (prefixWord ++ tailWord_829848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829864 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_829864 : Nat := 118140960795 + 829864 * 2 ^ 59
def prefixEnd_829864 : Nat := 4983230072969 + 3 ^ 40 * 829864 * 2
def baseEnd_829864 : Nat := 426119109862846386983531

theorem tailTrace_829864 : CollatzResearch.WordTrace tailWord_829864 prefixEnd_829864 426119109862846386983531 := by
  unfold tailWord_829864
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133813332775966166324323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20178417777034621555099097 15133813332775966166324323)
  ·
    refine ⟨22700719999163949249486485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15133813332775966166324323 22700719999163949249486485)
    ·
      refine ⟨1064096249960810121069679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22700719999163949249486485 1064096249960810121069679)
      ·
        refine ⟨1596144374941215181604519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064096249960810121069679 1596144374941215181604519)
        ·
          refine ⟨2394216562411822772406779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596144374941215181604519 2394216562411822772406779)
          ·
            refine ⟨3591324843617734158610169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394216562411822772406779 3591324843617734158610169)
            ·
              refine ⟨2693493632713300618957627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3591324843617734158610169 2693493632713300618957627)
              ·
                refine ⟨4040240449069950928436441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693493632713300618957627 4040240449069950928436441)
                ·
                  refine ⟨3030180336802463196327331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040240449069950928436441 3030180336802463196327331)
                  ·
                    refine ⟨4545270505203694794490997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030180336802463196327331 4545270505203694794490997)
                    ·
                      refine ⟨426119109862846386983531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4545270505203694794490997 426119109862846386983531)
                      ·
                        rfl

theorem cell23_829864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_829864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829864 prefixEnd_829864 := by exact prefixLift 829864
  have htrace : WordTrace (prefixWord ++ tailWord_829864) baseStart_829864 baseEnd_829864 := by
    simpa [prefixWord, tailWord_829864, baseEnd_829864] using wordTrace_append hprefix tailTrace_829864
  have hstable : (prefixWord ++ tailWord_829864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829864).length < 2 ^ (prefixWord ++ tailWord_829864).sum := by decide
  have hdescent : baseEnd_829864 < baseStart_829864 := by decide
  rcases family_descends (prefixWord ++ tailWord_829864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829880 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_829880 : Nat := 118140960795 + 829880 * 2 ^ 59
def prefixEnd_829880 : Nat := 4983230072969 + 3 ^ 40 * 829880 * 2
def baseEnd_829880 : Nat := 142042441851106108127819

theorem tailTrace_829880 : CollatzResearch.WordTrace tailWord_829880 prefixEnd_829880 142042441851106108127819 := by
  unfold tailWord_829880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134105116746983532615547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20178806822329311376820729 15134105116746983532615547)
  ·
    refine ⟨22701157675120475298923321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134105116746983532615547 22701157675120475298923321)
    ·
      refine ⟨17025868256340356474192491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22701157675120475298923321 17025868256340356474192491)
      ·
        refine ⟨25538802384510534711288737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025868256340356474192491 25538802384510534711288737)
        ·
          refine ⟨19154101788382901033466553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25538802384510534711288737 19154101788382901033466553)
          ·
            refine ⟨14365576341287175775099915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19154101788382901033466553 14365576341287175775099915)
            ·
              refine ⟨21548364511930763662649873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14365576341287175775099915 21548364511930763662649873)
              ·
                refine ⟨16161273383948072746987405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21548364511930763662649873 16161273383948072746987405)
                ·
                  refine ⟨6060477518980527280120277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16161273383948072746987405 6060477518980527280120277)
                  ·
                    refine ⟨142042441851106108127819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6060477518980527280120277 142042441851106108127819)
                    ·
                      rfl

theorem cell23_829880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_829880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829880 prefixEnd_829880 := by exact prefixLift 829880
  have htrace : WordTrace (prefixWord ++ tailWord_829880) baseStart_829880 baseEnd_829880 := by
    simpa [prefixWord, tailWord_829880, baseEnd_829880] using wordTrace_append hprefix tailTrace_829880
  have hstable : (prefixWord ++ tailWord_829880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829880).length < 2 ^ (prefixWord ++ tailWord_829880).sum := by decide
  have hdescent : baseEnd_829880 < baseStart_829880 := by decide
  rcases family_descends (prefixWord ++ tailWord_829880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829944 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 3, 4]
def baseStart_829944 : Nat := 118140960795 + 829944 * 2 ^ 59
def prefixEnd_829944 : Nat := 4983230072969 + 3 ^ 40 * 829944 * 2
def baseEnd_829944 : Nat := 142053396105068691327721

theorem tailTrace_829944 : CollatzResearch.WordTrace tailWord_829944 prefixEnd_829944 142053396105068691327721 := by
  unfold tailWord_829944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15135272252631052997780443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20180363003508070663707257 15135272252631052997780443)
  ·
    refine ⟨22702908378946579496670665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15135272252631052997780443 22702908378946579496670665)
    ·
      refine ⟨17027181284209934622502999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22702908378946579496670665 17027181284209934622502999)
      ·
        refine ⟨25540771926314901933754499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17027181284209934622502999 25540771926314901933754499)
        ·
          refine ⟨38311157889472352900631749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25540771926314901933754499 38311157889472352900631749)
          ·
            refine ⟨7183342104276066168868453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38311157889472352900631749 7183342104276066168868453)
            ·
              refine ⟨1346876644551762406662835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7183342104276066168868453 1346876644551762406662835)
              ·
                refine ⟨2020314966827643609994253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346876644551762406662835 2020314966827643609994253)
                ·
                  refine ⟨757618112560366353747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2020314966827643609994253 757618112560366353747845)
                  ·
                    refine ⟨142053396105068691327721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757618112560366353747845 142053396105068691327721)
                    ·
                      rfl

theorem cell23_829944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_829944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829944 prefixEnd_829944 := by exact prefixLift 829944
  have htrace : WordTrace (prefixWord ++ tailWord_829944) baseStart_829944 baseEnd_829944 := by
    simpa [prefixWord, tailWord_829944, baseEnd_829944] using wordTrace_append hprefix tailTrace_829944
  have hstable : (prefixWord ++ tailWord_829944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829944).length < 2 ^ (prefixWord ++ tailWord_829944).sum := by decide
  have hdescent : baseEnd_829944 < baseStart_829944 := by decide
  rcases family_descends (prefixWord ++ tailWord_829944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829957 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 6]
def baseStart_829957 : Nat := 118140960795 + 829957 * 2 ^ 59
def prefixEnd_829957 : Nat := 4983230072969 + 3 ^ 40 * 829957 * 2
def baseEnd_829957 : Nat := 47351873729301613680067

theorem tailTrace_829957 : CollatzResearch.WordTrace tailWord_829957 prefixEnd_829957 47351873729301613680067 := by
  unfold tailWord_829957
  simp only [CollatzResearch.WordTrace]
  refine ⟨30271018654215009215784125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20180679102810006143856083 30271018654215009215784125)
  ·
    refine ⟨11351631995330628455919047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30271018654215009215784125 11351631995330628455919047)
    ·
      refine ⟨17027447992995942683878571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11351631995330628455919047 17027447992995942683878571)
      ·
        refine ⟨25541171989493914025817857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17027447992995942683878571 25541171989493914025817857)
        ·
          refine ⟨19155878992120435519363393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25541171989493914025817857 19155878992120435519363393)
          ·
            refine ⟨14366909244090326639522545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19155878992120435519363393 14366909244090326639522545)
            ·
              refine ⟨10775181933067744979641909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14366909244090326639522545 10775181933067744979641909)
              ·
                refine ⟨1010173306225101091841429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10775181933067744979641909 1010173306225101091841429)
                ·
                  refine ⟨47351873729301613680067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1010173306225101091841429 47351873729301613680067)
                  ·
                    rfl

theorem cell23_829957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_829957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829957 prefixEnd_829957 := by exact prefixLift 829957
  have htrace : WordTrace (prefixWord ++ tailWord_829957) baseStart_829957 baseEnd_829957 := by
    simpa [prefixWord, tailWord_829957, baseEnd_829957] using wordTrace_append hprefix tailTrace_829957
  have hstable : (prefixWord ++ tailWord_829957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829957).length < 2 ^ (prefixWord ++ tailWord_829957).sum := by decide
  have hdescent : baseEnd_829957 < baseStart_829957 := by decide
  rcases family_descends (prefixWord ++ tailWord_829957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829988 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_829988 : Nat := 118140960795 + 829988 * 2 ^ 59
def prefixEnd_829988 : Nat := 4983230072969 + 3 ^ 40 * 829988 * 2
def baseEnd_829988 : Nat := 426182781464003901832961

theorem tailTrace_829988 : CollatzResearch.WordTrace tailWord_829988 prefixEnd_829988 426182781464003901832961 := by
  unfold tailWord_829988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136074658551350755081309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20181432878068467673441745 15136074658551350755081309)
  ·
    refine ⟨5676027996956756533155491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15136074658551350755081309 5676027996956756533155491)
    ·
      refine ⟨8514041995435134799733237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676027996956756533155491 8514041995435134799733237)
      ·
        refine ⟨798191437072043887474991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8514041995435134799733237 798191437072043887474991)
        ·
          refine ⟨1197287155608065831212487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798191437072043887474991 1197287155608065831212487)
          ·
            refine ⟨1795930733412098746818731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197287155608065831212487 1795930733412098746818731)
            ·
              refine ⟨2693896100118148120228097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795930733412098746818731 2693896100118148120228097)
              ·
                refine ⟨2020422075088611090171073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693896100118148120228097 2020422075088611090171073)
                ·
                  refine ⟨1515316556316458317628305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2020422075088611090171073 1515316556316458317628305)
                  ·
                    refine ⟨1136487417237343738221229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1515316556316458317628305 1136487417237343738221229)
                    ·
                      refine ⟨426182781464003901832961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136487417237343738221229 426182781464003901832961)
                      ·
                        rfl

theorem cell23_829988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_829988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_829988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_829988 prefixEnd_829988 := by exact prefixLift 829988
  have htrace : WordTrace (prefixWord ++ tailWord_829988) baseStart_829988 baseEnd_829988 := by
    simpa [prefixWord, tailWord_829988, baseEnd_829988] using wordTrace_append hprefix tailTrace_829988
  have hstable : (prefixWord ++ tailWord_829988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829988).length < 2 ^ (prefixWord ++ tailWord_829988).sum := by decide
  have hdescent : baseEnd_829988 < baseStart_829988 := by decide
  rcases family_descends (prefixWord ++ tailWord_829988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830001 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_830001 : Nat := 118140960795 + 830001 * 2 ^ 59
def prefixEnd_830001 : Nat := 4983230072969 + 3 ^ 40 * 830001 * 2
def baseEnd_830001 : Nat := 426189456712512350970401

theorem tailTrace_830001 : CollatzResearch.WordTrace tailWord_830001 prefixEnd_830001 426189456712512350970401 := by
  unfold tailWord_830001
  simp only [CollatzResearch.WordTrace]
  refine ⟨30272623466055604730385857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20181748977370403153590571 30272623466055604730385857)
  ·
    refine ⟨22704467599541703547789393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30272623466055604730385857 22704467599541703547789393)
    ·
      refine ⟨17028350699656277660842045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22704467599541703547789393 17028350699656277660842045)
      ·
        refine ⟨6385631512371104122815767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17028350699656277660842045 6385631512371104122815767)
        ·
          refine ⟨9578447268556656184223651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385631512371104122815767 9578447268556656184223651)
          ·
            refine ⟨14367670902834984276335477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578447268556656184223651 14367670902834984276335477)
            ·
              refine ⟨1346969147140779775906451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14367670902834984276335477 1346969147140779775906451)
              ·
                refine ⟨2020453720711169663859677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346969147140779775906451 2020453720711169663859677)
                ·
                  refine ⟨757670145266688623947379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2020453720711169663859677 757670145266688623947379)
                  ·
                    refine ⟨1136505217900032935921069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757670145266688623947379 1136505217900032935921069)
                    ·
                      refine ⟨426189456712512350970401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136505217900032935921069 426189456712512350970401)
                      ·
                        rfl

theorem cell23_830001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_830001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830001 prefixEnd_830001 := by exact prefixLift 830001
  have htrace : WordTrace (prefixWord ++ tailWord_830001) baseStart_830001 baseEnd_830001 := by
    simpa [prefixWord, tailWord_830001, baseEnd_830001] using wordTrace_append hprefix tailTrace_830001
  have hstable : (prefixWord ++ tailWord_830001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830001).length < 2 ^ (prefixWord ++ tailWord_830001).sum := by decide
  have hdescent : baseEnd_830001 < baseStart_830001 := by decide
  rcases family_descends (prefixWord ++ tailWord_830001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830021 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_830021 : Nat := 118140960795 + 830021 * 2 ^ 59
def prefixEnd_830021 : Nat := 4983230072969 + 3 ^ 40 * 830021 * 2
def baseEnd_830021 : Nat := 142066575441867424240103

theorem tailTrace_830021 : CollatzResearch.WordTrace tailWord_830021 prefixEnd_830021 142066575441867424240103 := by
  unfold tailWord_830021
  simp only [CollatzResearch.WordTrace]
  refine ⟨30273352925983148146113917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20182235283988765430742611 30273352925983148146113917)
  ·
    refine ⟨11352507347243680554792719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30273352925983148146113917 11352507347243680554792719)
    ·
      refine ⟨17028761020865520832189079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11352507347243680554792719 17028761020865520832189079)
      ·
        refine ⟨25543141531298281248283619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17028761020865520832189079 25543141531298281248283619)
        ·
          refine ⟨38314712296947421872425429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25543141531298281248283619 38314712296947421872425429)
          ·
            refine ⟨898001069459705200134971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 38314712296947421872425429 898001069459705200134971)
            ·
              refine ⟨1347001604189557800202457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898001069459705200134971 1347001604189557800202457)
              ·
                refine ⟨1010251203142168350151843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347001604189557800202457 1010251203142168350151843)
                ·
                  refine ⟨1515376804713252525227765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010251203142168350151843 1515376804713252525227765)
                  ·
                    refine ⟨142066575441867424240103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1515376804713252525227765 142066575441867424240103)
                    ·
                      rfl

theorem cell23_830021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_830021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830021 prefixEnd_830021 := by exact prefixLift 830021
  have htrace : WordTrace (prefixWord ++ tailWord_830021) baseStart_830021 baseEnd_830021 := by
    simpa [prefixWord, tailWord_830021, baseEnd_830021] using wordTrace_append hprefix tailTrace_830021
  have hstable : (prefixWord ++ tailWord_830021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830021).length < 2 ^ (prefixWord ++ tailWord_830021).sum := by decide
  have hdescent : baseEnd_830021 < baseStart_830021 := by decide
  rcases family_descends (prefixWord ++ tailWord_830021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830024 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_830024 : Nat := 118140960795 + 830024 * 2 ^ 59
def prefixEnd_830024 : Nat := 4983230072969 + 3 ^ 40 * 830024 * 2
def baseEnd_830024 : Nat := 426201266767565760982795

theorem tailTrace_830024 : CollatzResearch.WordTrace tailWord_830024 prefixEnd_830024 426201266767565760982795 := by
  unfold tailWord_830024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136731172486139829236563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20182308229981519772315417 15136731172486139829236563)
  ·
    refine ⟨22705096758729209743854845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15136731172486139829236563 22705096758729209743854845)
    ·
      refine ⟨8514411284523453653945567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22705096758729209743854845 8514411284523453653945567)
      ·
        refine ⟨12771616926785180480918351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514411284523453653945567 12771616926785180480918351)
        ·
          refine ⟨19157425390177770721377527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12771616926785180480918351 19157425390177770721377527)
          ·
            refine ⟨28736138085266656082066291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19157425390177770721377527 28736138085266656082066291)
            ·
              refine ⟨43104207127899984123099437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28736138085266656082066291 43104207127899984123099437)
              ·
                refine ⟨16164077672962494046162289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43104207127899984123099437 16164077672962494046162289)
                ·
                  refine ⟨12123058254721870534621717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16164077672962494046162289 12123058254721870534621717)
                  ·
                    refine ⟨568268355690087681310393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12123058254721870534621717 568268355690087681310393)
                    ·
                      refine ⟨426201266767565760982795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568268355690087681310393 426201266767565760982795)
                      ·
                        rfl

theorem cell23_830024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_830024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830024 prefixEnd_830024 := by exact prefixLift 830024
  have htrace : WordTrace (prefixWord ++ tailWord_830024) baseStart_830024 baseEnd_830024 := by
    simpa [prefixWord, tailWord_830024, baseEnd_830024] using wordTrace_append hprefix tailTrace_830024
  have hstable : (prefixWord ++ tailWord_830024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830024).length < 2 ^ (prefixWord ++ tailWord_830024).sum := by decide
  have hdescent : baseEnd_830024 < baseStart_830024 := by decide
  rcases family_descends (prefixWord ++ tailWord_830024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830027 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5]
def baseStart_830027 : Nat := 118140960795 + 830027 * 2 ^ 59
def prefixEnd_830027 : Nat := 4983230072969 + 3 ^ 40 * 830027 * 2
def baseEnd_830027 : Nat := 426202807209529249245281

theorem tailTrace_830027 : CollatzResearch.WordTrace tailWord_830027 prefixEnd_830027 426202807209529249245281 := by
  unfold tailWord_830027
  simp only [CollatzResearch.WordTrace]
  refine ⟨30273571763961411170832335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20182381175974274113888223 30273571763961411170832335)
  ·
    refine ⟨45410357645942116756248503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30273571763961411170832335 45410357645942116756248503)
    ·
      refine ⟨68115536468913175134372755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45410357645942116756248503 68115536468913175134372755)
      ·
        refine ⟨102173304703369762701559133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68115536468913175134372755 102173304703369762701559133)
        ·
          refine ⟨38314989263763661013084675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102173304703369762701559133 38314989263763661013084675)
          ·
            refine ⟨57472483895645491519627013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38314989263763661013084675 57472483895645491519627013)
            ·
              refine ⟨10776090730433529659930065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57472483895645491519627013 10776090730433529659930065)
              ·
                refine ⟨8082068047825147244947549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10776090730433529659930065 8082068047825147244947549)
                ·
                  refine ⟨3030775517934430216855331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8082068047825147244947549 3030775517934430216855331)
                  ·
                    refine ⟨4546163276901645325282997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030775517934430216855331 4546163276901645325282997)
                    ·
                      refine ⟨426202807209529249245281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4546163276901645325282997 426202807209529249245281)
                      ·
                        rfl

theorem cell23_830027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_830027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830027 prefixEnd_830027 := by exact prefixLift 830027
  have htrace : WordTrace (prefixWord ++ tailWord_830027) baseStart_830027 baseEnd_830027 := by
    simpa [prefixWord, tailWord_830027, baseEnd_830027] using wordTrace_append hprefix tailTrace_830027
  have hstable : (prefixWord ++ tailWord_830027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830027).length < 2 ^ (prefixWord ++ tailWord_830027).sum := by decide
  have hdescent : baseEnd_830027 < baseStart_830027 := by decide
  rcases family_descends (prefixWord ++ tailWord_830027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830034 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_830034 : Nat := 118140960795 + 830034 * 2 ^ 59
def prefixEnd_830034 : Nat := 4983230072969 + 3 ^ 40 * 830034 * 2
def baseEnd_830034 : Nat := 142068800524703573952583

theorem tailTrace_830034 : CollatzResearch.WordTrace tailWord_830034 prefixEnd_830034 142068800524703573952583 := by
  unfold tailWord_830034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568456768734012841584289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20182551383290700910891437 7568456768734012841584289)
  ·
    refine ⟨5676342576550509631188217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7568456768734012841584289 5676342576550509631188217)
    ·
      refine ⟨4257256932412882223391163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5676342576550509631188217 4257256932412882223391163)
      ·
        refine ⟨6385885398619323335086745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257256932412882223391163 6385885398619323335086745)
        ·
          refine ⟨4789414048964492501315059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6385885398619323335086745 4789414048964492501315059)
          ·
            refine ⟨7184121073446738751972589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789414048964492501315059 7184121073446738751972589)
            ·
              refine ⟨2694045402542527031989721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7184121073446738751972589 2694045402542527031989721)
              ·
                refine ⟨2020534051906895273992291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694045402542527031989721 2020534051906895273992291)
                ·
                  refine ⟨3030801077860342910988437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020534051906895273992291 3030801077860342910988437)
                  ·
                    refine ⟨142068800524703573952583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3030801077860342910988437 142068800524703573952583)
                    ·
                      rfl

theorem cell23_830034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_830034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830034 prefixEnd_830034 := by exact prefixLift 830034
  have htrace : WordTrace (prefixWord ++ tailWord_830034) baseStart_830034 baseEnd_830034 := by
    simpa [prefixWord, tailWord_830034, baseEnd_830034] using wordTrace_append hprefix tailTrace_830034
  have hstable : (prefixWord ++ tailWord_830034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830034).length < 2 ^ (prefixWord ++ tailWord_830034).sum := by decide
  have hdescent : baseEnd_830034 < baseStart_830034 := by decide
  rcases family_descends (prefixWord ++ tailWord_830034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830046 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_830046 : Nat := 118140960795 + 830046 * 2 ^ 59
def prefixEnd_830046 : Nat := 4983230072969 + 3 ^ 40 * 830046 * 2
def baseEnd_830046 : Nat := 142070854447321558302565

theorem tailTrace_830046 : CollatzResearch.WordTrace tailWord_830046 prefixEnd_830046 142070854447321558302565 := by
  unfold tailWord_830046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784283093861572176971749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20182843167261718277182661 3784283093861572176971749)
  ·
    refine ⟨709553080099044783182203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3784283093861572176971749 709553080099044783182203)
    ·
      refine ⟨1064329620148567174773305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709553080099044783182203 1064329620148567174773305)
      ·
        refine ⟨798247215111425381079979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064329620148567174773305 798247215111425381079979)
        ·
          refine ⟨1197370822667138071619969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798247215111425381079979 1197370822667138071619969)
          ·
            refine ⟨898028117000353553714977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197370822667138071619969 898028117000353553714977)
            ·
              refine ⟨673521087750265165286233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898028117000353553714977 673521087750265165286233)
              ·
                refine ⟨505140815812698873964675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673521087750265165286233 505140815812698873964675)
                ·
                  refine ⟨757711223719048310947013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505140815812698873964675 757711223719048310947013)
                  ·
                    refine ⟨142070854447321558302565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757711223719048310947013 142070854447321558302565)
                    ·
                      rfl

theorem cell23_830046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_830046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830046 prefixEnd_830046 := by exact prefixLift 830046
  have htrace : WordTrace (prefixWord ++ tailWord_830046) baseStart_830046 baseEnd_830046 := by
    simpa [prefixWord, tailWord_830046, baseEnd_830046] using wordTrace_append hprefix tailTrace_830046
  have hstable : (prefixWord ++ tailWord_830046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830046).length < 2 ^ (prefixWord ++ tailWord_830046).sum := by decide
  have hdescent : baseEnd_830046 < baseStart_830046 := by decide
  rcases family_descends (prefixWord ++ tailWord_830046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830051 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 2, 4]
def baseStart_830051 : Nat := 118140960795 + 830051 * 2 ^ 59
def prefixEnd_830051 : Nat := 4983230072969 + 3 ^ 40 * 830051 * 2
def baseEnd_830051 : Nat := 142071710248412385115057

theorem tailTrace_830051 : CollatzResearch.WordTrace tailWord_830051 prefixEnd_830051 142071710248412385115057 := by
  unfold tailWord_830051
  simp only [CollatzResearch.WordTrace]
  refine ⟨30274447115874463269706007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20182964743916308846470671 30274447115874463269706007)
  ·
    refine ⟨45411670673811694904559011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30274447115874463269706007 45411670673811694904559011)
    ·
      refine ⟨68117506010717542356838517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45411670673811694904559011 68117506010717542356838517)
      ·
        refine ⟨6386016188504769595953611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68117506010717542356838517 6386016188504769595953611)
        ·
          refine ⟨9579024282757154393930417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386016188504769595953611 9579024282757154393930417)
          ·
            refine ⟨7184268212067865795447813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9579024282757154393930417 7184268212067865795447813)
            ·
              refine ⟨1347050289762724836646465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7184268212067865795447813 1347050289762724836646465)
              ·
                refine ⟨1010287717322043627484849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347050289762724836646465 1010287717322043627484849)
                ·
                  refine ⟨757715787991532720613637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010287717322043627484849 757715787991532720613637)
                  ·
                    refine ⟨142071710248412385115057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757715787991532720613637 142071710248412385115057)
                    ·
                      rfl

theorem cell23_830051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 4].length) (baseStart_830051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830051 prefixEnd_830051 := by exact prefixLift 830051
  have htrace : WordTrace (prefixWord ++ tailWord_830051) baseStart_830051 baseEnd_830051 := by
    simpa [prefixWord, tailWord_830051, baseEnd_830051] using wordTrace_append hprefix tailTrace_830051
  have hstable : (prefixWord ++ tailWord_830051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830051).length < 2 ^ (prefixWord ++ tailWord_830051).sum := by decide
  have hdescent : baseEnd_830051 < baseStart_830051 := by decide
  rcases family_descends (prefixWord ++ tailWord_830051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830058 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_830058 : Nat := 118140960795 + 830058 * 2 ^ 59
def prefixEnd_830058 : Nat := 4983230072969 + 3 ^ 40 * 830058 * 2
def baseEnd_830058 : Nat := 426218725109818627957639

theorem tailTrace_830058 : CollatzResearch.WordTrace tailWord_830058 prefixEnd_830058 426218725109818627957639 := by
  unfold tailWord_830058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568675606712275866302707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20183134951232735643473885 7568675606712275866302707)
  ·
    refine ⟨11353013410068413799454061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7568675606712275866302707 11353013410068413799454061)
    ·
      refine ⟨4257380028775655174795273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11353013410068413799454061 4257380028775655174795273)
      ·
        refine ⟨3193035021581741381096455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257380028775655174795273 3193035021581741381096455)
        ·
          refine ⟨4789552532372612071644683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193035021581741381096455 4789552532372612071644683)
          ·
            refine ⟨7184328798558918107467025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789552532372612071644683 7184328798558918107467025)
            ·
              refine ⟨5388246598919188580600269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7184328798558918107467025 5388246598919188580600269)
              ·
                refine ⟨2020592474594695717725101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5388246598919188580600269 2020592474594695717725101)
                ·
                  refine ⟨757722177973010894146913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2020592474594695717725101 757722177973010894146913)
                  ·
                    refine ⟨568291633479758170610185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 757722177973010894146913 568291633479758170610185)
                    ·
                      refine ⟨426218725109818627957639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568291633479758170610185 426218725109818627957639)
                      ·
                        rfl

theorem cell23_830058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_830058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830058 prefixEnd_830058 := by exact prefixLift 830058
  have htrace : WordTrace (prefixWord ++ tailWord_830058) baseStart_830058 baseEnd_830058 := by
    simpa [prefixWord, tailWord_830058, baseEnd_830058] using wordTrace_append hprefix tailTrace_830058
  have hstable : (prefixWord ++ tailWord_830058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830058).length < 2 ^ (prefixWord ++ tailWord_830058).sum := by decide
  have hdescent : baseEnd_830058 < baseStart_830058 := by decide
  rcases family_descends (prefixWord ++ tailWord_830058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830061 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_830061 : Nat := 118140960795 + 830061 * 2 ^ 59
def prefixEnd_830061 : Nat := 4983230072969 + 3 ^ 40 * 830061 * 2
def baseEnd_830061 : Nat := 426220265551782116220125

theorem tailTrace_830061 : CollatzResearch.WordTrace tailWord_830061 prefixEnd_830061 426220265551782116220125 := by
  unfold tailWord_830061
  simp only [CollatzResearch.WordTrace]
  refine ⟨30274811845838234977570037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20183207897225489985046691 30274811845838234977570037)
  ·
    refine ⟨2838263610547334529147191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30274811845838234977570037 2838263610547334529147191)
    ·
      refine ⟨4257395415821001793720787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838263610547334529147191 4257395415821001793720787)
      ·
        refine ⟨6386093123731502690581181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257395415821001793720787 6386093123731502690581181)
        ·
          refine ⟨2394784921399313508967943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6386093123731502690581181 2394784921399313508967943)
          ·
            refine ⟨3592177382098970263451915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394784921399313508967943 3592177382098970263451915)
            ·
              refine ⟨5388266073148455395177873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592177382098970263451915 5388266073148455395177873)
              ·
                refine ⟨4041199554861341546383405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388266073148455395177873 4041199554861341546383405)
                ·
                  refine ⟨1515449833073003079893777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4041199554861341546383405 1515449833073003079893777)
                  ·
                    refine ⟨1136587374804752309920333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1515449833073003079893777 1136587374804752309920333)
                    ·
                      refine ⟨426220265551782116220125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136587374804752309920333 426220265551782116220125)
                      ·
                        rfl

theorem cell23_830061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_830061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830061 prefixEnd_830061 := by exact prefixLift 830061
  have htrace : WordTrace (prefixWord ++ tailWord_830061) baseStart_830061 baseEnd_830061 := by
    simpa [prefixWord, tailWord_830061, baseEnd_830061] using wordTrace_append hprefix tailTrace_830061
  have hstable : (prefixWord ++ tailWord_830061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830061).length < 2 ^ (prefixWord ++ tailWord_830061).sum := by decide
  have hdescent : baseEnd_830061 < baseStart_830061 := by decide
  rcases family_descends (prefixWord ++ tailWord_830061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830108 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_830108 : Nat := 118140960795 + 830108 * 2 ^ 59
def prefixEnd_830108 : Nat := 4983230072969 + 3 ^ 40 * 830108 * 2
def baseEnd_830108 : Nat := 426244399142543432332409

theorem tailTrace_830108 : CollatzResearch.WordTrace tailWord_830108 prefixEnd_830108 426244399142543432332409 := by
  unfold tailWord_830108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138263038333981002265489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20184350717778641336353985 15138263038333981002265489)
  ·
    refine ⟨11353697278750485751699117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15138263038333981002265489 11353697278750485751699117)
    ·
      refine ⟨4257636479531432156887169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11353697278750485751699117 4257636479531432156887169)
      ·
        refine ⟨3193227359648574117665377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257636479531432156887169 3193227359648574117665377)
        ·
          refine ⟨2394920519736430588249033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193227359648574117665377 2394920519736430588249033)
          ·
            refine ⟨1796190389802322941186775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394920519736430588249033 1796190389802322941186775)
            ·
              refine ⟨2694285584703484411780163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796190389802322941186775 2694285584703484411780163)
              ·
                refine ⟨4041428377055226617670245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694285584703484411780163 4041428377055226617670245)
                ·
                  refine ⟨757767820697854990813171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4041428377055226617670245 757767820697854990813171)
                  ·
                    refine ⟨1136651731046782486219757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757767820697854990813171 1136651731046782486219757)
                    ·
                      refine ⟨426244399142543432332409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136651731046782486219757 426244399142543432332409)
                      ·
                        rfl

theorem cell23_830108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_830108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830108 prefixEnd_830108 := by exact prefixLift 830108
  have htrace : WordTrace (prefixWord ++ tailWord_830108) baseStart_830108 baseEnd_830108 := by
    simpa [prefixWord, tailWord_830108, baseEnd_830108] using wordTrace_append hprefix tailTrace_830108
  have hstable : (prefixWord ++ tailWord_830108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830108).length < 2 ^ (prefixWord ++ tailWord_830108).sum := by decide
  have hdescent : baseEnd_830108 < baseStart_830108 := by decide
  rcases family_descends (prefixWord ++ tailWord_830108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830122 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_830122 : Nat := 118140960795 + 830122 * 2 ^ 59
def prefixEnd_830122 : Nat := 4983230072969 + 3 ^ 40 * 830122 * 2
def baseEnd_830122 : Nat := 426251587871706377557345

theorem tailTrace_830122 : CollatzResearch.WordTrace tailWord_830122 prefixEnd_830122 426251587871706377557345 := by
  unfold tailWord_830122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569259174654310598885155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20184691132411494930360413 7569259174654310598885155)
  ·
    refine ⟨11353888761981465898327733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569259174654310598885155 11353888761981465898327733)
    ·
      refine ⟨1064427071435762427968225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11353888761981465898327733 1064427071435762427968225)
      ·
        refine ⟨798320303576821820976169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064427071435762427968225 798320303576821820976169)
        ·
          refine ⟨598740227682616365732127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798320303576821820976169 598740227682616365732127)
          ·
            refine ⟨898110341523924548598191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598740227682616365732127 898110341523924548598191)
            ·
              refine ⟨1347165512285886822897287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898110341523924548598191 1347165512285886822897287)
              ·
                refine ⟨2020748268428830234345931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347165512285886822897287 2020748268428830234345931)
                ·
                  refine ⟨3031122402643245351518897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020748268428830234345931 3031122402643245351518897)
                  ·
                    refine ⟨2273341801982434013639173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031122402643245351518897 2273341801982434013639173)
                    ·
                      refine ⟨426251587871706377557345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2273341801982434013639173 426251587871706377557345)
                      ·
                        rfl

theorem cell23_830122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_830122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830122 prefixEnd_830122 := by exact prefixLift 830122
  have htrace : WordTrace (prefixWord ++ tailWord_830122) baseStart_830122 baseEnd_830122 := by
    simpa [prefixWord, tailWord_830122, baseEnd_830122] using wordTrace_append hprefix tailTrace_830122
  have hstable : (prefixWord ++ tailWord_830122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830122).length < 2 ^ (prefixWord ++ tailWord_830122).sum := by decide
  have hdescent : baseEnd_830122 < baseStart_830122 := by decide
  rcases family_descends (prefixWord ++ tailWord_830122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830135 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 1, 3, 2]
def baseStart_830135 : Nat := 118140960795 + 830135 * 2 ^ 59
def prefixEnd_830135 : Nat := 4983230072969 + 3 ^ 40 * 830135 * 2
def baseEnd_830135 : Nat := 426258263120214826694785

theorem tailTrace_830135 : CollatzResearch.WordTrace tailWord_830135 prefixEnd_830135 426258263120214826694785 := by
  unfold tailWord_830135
  simp only [CollatzResearch.WordTrace]
  refine ⟨30277510847570145615763859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20185007231713430410509239 30277510847570145615763859)
  ·
    refine ⟨45416266271355218423645789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30277510847570145615763859 45416266271355218423645789)
    ·
      refine ⟨17031099851758206908867171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45416266271355218423645789 17031099851758206908867171)
      ·
        refine ⟨25546649777637310363300757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17031099851758206908867171 25546649777637310363300757)
        ·
          refine ⟨1197499208326748923279723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25546649777637310363300757 1197499208326748923279723)
          ·
            refine ⟨1796248812490123384919585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197499208326748923279723 1796248812490123384919585)
            ·
              refine ⟨1347186609367592538689689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1796248812490123384919585 1347186609367592538689689)
              ·
                refine ⟨1010389957025694404017267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347186609367592538689689 1010389957025694404017267)
                ·
                  refine ⟨1515584935538541606025901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010389957025694404017267 1515584935538541606025901)
                  ·
                    refine ⟨568344350826953102259713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515584935538541606025901 568344350826953102259713)
                    ·
                      refine ⟨426258263120214826694785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568344350826953102259713 426258263120214826694785)
                      ·
                        rfl

theorem cell23_830135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_830135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830135 prefixEnd_830135 := by exact prefixLift 830135
  have htrace : WordTrace (prefixWord ++ tailWord_830135) baseStart_830135 baseEnd_830135 := by
    simpa [prefixWord, tailWord_830135, baseEnd_830135] using wordTrace_append hprefix tailTrace_830135
  have hstable : (prefixWord ++ tailWord_830135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830135).length < 2 ^ (prefixWord ++ tailWord_830135).sum := by decide
  have hdescent : baseEnd_830135 < baseStart_830135 := by decide
  rcases family_descends (prefixWord ++ tailWord_830135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830241 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_830241 : Nat := 118140960795 + 830241 * 2 ^ 59
def prefixEnd_830241 : Nat := 4983230072969 + 3 ^ 40 * 830241 * 2
def baseEnd_830241 : Nat := 426312692069591411969297

theorem tailTrace_830241 : CollatzResearch.WordTrace tailWord_830241 prefixEnd_830241 426312692069591411969297 := by
  unfold tailWord_830241
  simp only [CollatzResearch.WordTrace]
  refine ⟨30281376985186125719122577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20187584656790750479415051 30281376985186125719122577)
  ·
    refine ⟨22711032738889594289341933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30281376985186125719122577 22711032738889594289341933)
    ·
      refine ⟨8516637277083597858503225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22711032738889594289341933 8516637277083597858503225)
      ·
        refine ⟨6387477957812698393877419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8516637277083597858503225 6387477957812698393877419)
        ·
          refine ⟨9581216936719047590816129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387477957812698393877419 9581216936719047590816129)
          ·
            refine ⟨7185912702539285693112097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9581216936719047590816129 7185912702539285693112097)
            ·
              refine ⟨5389434526904464269834073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7185912702539285693112097 5389434526904464269834073)
              ·
                refine ⟨4042075895178348202375555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389434526904464269834073 4042075895178348202375555)
                ·
                  refine ⟨6063113842767522303563333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042075895178348202375555 6063113842767522303563333)
                  ·
                    refine ⟨1136833845518910431918125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6063113842767522303563333 1136833845518910431918125)
                    ·
                      refine ⟨426312692069591411969297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136833845518910431918125 426312692069591411969297)
                      ·
                        rfl

theorem cell23_830241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_830241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830241 prefixEnd_830241 := by exact prefixLift 830241
  have htrace : WordTrace (prefixWord ++ tailWord_830241) baseStart_830241 baseEnd_830241 := by
    simpa [prefixWord, tailWord_830241, baseEnd_830241] using wordTrace_append hprefix tailTrace_830241
  have hstable : (prefixWord ++ tailWord_830241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830241).length < 2 ^ (prefixWord ++ tailWord_830241).sum := by decide
  have hdescent : baseEnd_830241 < baseStart_830241 := by decide
  rcases family_descends (prefixWord ++ tailWord_830241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830248 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 3, 4]
def baseStart_830248 : Nat := 118140960795 + 830248 * 2 ^ 59
def prefixEnd_830248 : Nat := 4983230072969 + 3 ^ 40 * 830248 * 2
def baseEnd_830248 : Nat := 142105428811390961527255

theorem tailTrace_830248 : CollatzResearch.WordTrace tailWord_830248 prefixEnd_830248 142105428811390961527255 := by
  unfold tailWord_830248
  simp only [CollatzResearch.WordTrace]
  refine ⟨15140816148080382957313699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20187754864107177276418265 15140816148080382957313699)
  ·
    refine ⟨22711224222120574435970549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15140816148080382957313699 22711224222120574435970549)
    ·
      refine ⟨2129177270823803853372239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22711224222120574435970549 2129177270823803853372239)
      ·
        refine ⟨3193765906235705780058359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129177270823803853372239 3193765906235705780058359)
        ·
          refine ⟨4790648859353558670087539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193765906235705780058359 4790648859353558670087539)
          ·
            refine ⟨7185973289030338005131309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790648859353558670087539 7185973289030338005131309)
            ·
              refine ⟨2694739983386376751924241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7185973289030338005131309 2694739983386376751924241)
              ·
                refine ⟨2021054987539782563943181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694739983386376751924241 2021054987539782563943181)
                ·
                  refine ⟨757895620327418461478693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2021054987539782563943181 757895620327418461478693)
                  ·
                    refine ⟨142105428811390961527255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757895620327418461478693 142105428811390961527255)
                    ·
                      rfl

theorem cell23_830248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_830248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830248 prefixEnd_830248 := by exact prefixLift 830248
  have htrace : WordTrace (prefixWord ++ tailWord_830248) baseStart_830248 baseEnd_830248 := by
    simpa [prefixWord, tailWord_830248, baseEnd_830248] using wordTrace_append hprefix tailTrace_830248
  have hstable : (prefixWord ++ tailWord_830248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830248).length < 2 ^ (prefixWord ++ tailWord_830248).sum := by decide
  have hdescent : baseEnd_830248 < baseStart_830248 := by decide
  rcases family_descends (prefixWord ++ tailWord_830248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830288 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 3, 1, 3]
def baseStart_830288 : Nat := 118140960795 + 830288 * 2 ^ 59
def prefixEnd_830288 : Nat := 4983230072969 + 3 ^ 40 * 830288 * 2
def baseEnd_830288 : Nat := 426336825660352728081581

theorem tailTrace_830288 : CollatzResearch.WordTrace tailWord_830288 prefixEnd_830288 426336825660352728081581 := by
  unfold tailWord_830288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15141545608007926373041759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20188727477343901830722345 15141545608007926373041759)
  ·
    refine ⟨22712318412011889559562639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15141545608007926373041759 22712318412011889559562639)
    ·
      refine ⟨34068477618017834339343959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22712318412011889559562639 34068477618017834339343959)
      ·
        refine ⟨51102716427026751509015939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34068477618017834339343959 51102716427026751509015939)
        ·
          refine ⟨76654074640540127263523909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51102716427026751509015939 76654074640540127263523909)
          ·
            refine ⟨14372638995101273861910733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76654074640540127263523909 14372638995101273861910733)
            ·
              refine ⟨5389739623162977698216525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14372638995101273861910733 5389739623162977698216525)
              ·
                refine ⟨2021152358686116636831197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5389739623162977698216525 2021152358686116636831197)
                ·
                  refine ⟨757932134507293738811699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2021152358686116636831197 757932134507293738811699)
                  ·
                    refine ⟨1136898201760940608217549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757932134507293738811699 1136898201760940608217549)
                    ·
                      refine ⟨426336825660352728081581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136898201760940608217549 426336825660352728081581)
                      ·
                        rfl

theorem cell23_830288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_830288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830288 prefixEnd_830288 := by exact prefixLift 830288
  have htrace : WordTrace (prefixWord ++ tailWord_830288) baseStart_830288 baseEnd_830288 := by
    simpa [prefixWord, tailWord_830288, baseEnd_830288] using wordTrace_append hprefix tailTrace_830288
  have hstable : (prefixWord ++ tailWord_830288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830288).length < 2 ^ (prefixWord ++ tailWord_830288).sum := by decide
  have hdescent : baseEnd_830288 < baseStart_830288 := by decide
  rcases family_descends (prefixWord ++ tailWord_830288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830298 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2]
def baseStart_830298 : Nat := 118140960795 + 830298 * 2 ^ 59
def prefixEnd_830298 : Nat := 4983230072969 + 3 ^ 40 * 830298 * 2
def baseEnd_830298 : Nat := 426341960466897688956535

theorem tailTrace_830298 : CollatzResearch.WordTrace tailWord_830298 prefixEnd_830298 426341960466897688956535 := by
  unfold tailWord_830298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570863986494906113486887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20188970630653082969298365 7570863986494906113486887)
  ·
    refine ⟨11356295979742359170230331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7570863986494906113486887 11356295979742359170230331)
    ·
      refine ⟨17034443969613538755345497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11356295979742359170230331 17034443969613538755345497)
      ·
        refine ⟨12775832977210154066509123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17034443969613538755345497 12775832977210154066509123)
        ·
          refine ⟨19163749465815231099763685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12775832977210154066509123 19163749465815231099763685)
          ·
            refine ⟨3593203024840355831205691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19163749465815231099763685 3593203024840355831205691)
            ·
              refine ⟨5389804537260533746808537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593203024840355831205691 5389804537260533746808537)
              ·
                refine ⟨4042353402945400310106403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389804537260533746808537 4042353402945400310106403)
                ·
                  refine ⟨6063530104418100465159605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042353402945400310106403 6063530104418100465159605)
                  ·
                    refine ⟨568455947289196918608713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6063530104418100465159605 568455947289196918608713)
                    ·
                      refine ⟨426341960466897688956535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568455947289196918608713 426341960466897688956535)
                      ·
                        rfl

theorem cell23_830298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_830298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830298 prefixEnd_830298 := by exact prefixLift 830298
  have htrace : WordTrace (prefixWord ++ tailWord_830298) baseStart_830298 baseEnd_830298 := by
    simpa [prefixWord, tailWord_830298, baseEnd_830298] using wordTrace_append hprefix tailTrace_830298
  have hstable : (prefixWord ++ tailWord_830298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830298).length < 2 ^ (prefixWord ++ tailWord_830298).sum := by decide
  have hdescent : baseEnd_830298 < baseStart_830298 := by decide
  rcases family_descends (prefixWord ++ tailWord_830298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830308 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_830308 : Nat := 118140960795 + 830308 * 2 ^ 59
def prefixEnd_830308 : Nat := 4983230072969 + 3 ^ 40 * 830308 * 2
def baseEnd_830308 : Nat := 142115698424480883277163

theorem tailTrace_830308 : CollatzResearch.WordTrace tailWord_830308 prefixEnd_830308 142115698424480883277163 := by
  unfold tailWord_830308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15141910337971698080905789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20189213783962264107874385 15141910337971698080905789)
  ·
    refine ⟨5678216376739386780339671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15141910337971698080905789 5678216376739386780339671)
    ·
      refine ⟨8517324565109080170509507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678216376739386780339671 8517324565109080170509507)
      ·
        refine ⟨12775986847663620255764261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8517324565109080170509507 12775986847663620255764261)
        ·
          refine ⟨2395497533936928797955799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12775986847663620255764261 2395497533936928797955799)
          ·
            refine ⟨3593246300905393196933699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395497533936928797955799 3593246300905393196933699)
            ·
              refine ⟨5389869451358089795400549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593246300905393196933699 5389869451358089795400549)
              ·
                refine ⟨1010600522129641836637603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5389869451358089795400549 1010600522129641836637603)
                ·
                  refine ⟨1515900783194462754956405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010600522129641836637603 1515900783194462754956405)
                  ·
                    refine ⟨142115698424480883277163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1515900783194462754956405 142115698424480883277163)
                    ·
                      rfl

theorem cell23_830308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_830308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830308 prefixEnd_830308 := by exact prefixLift 830308
  have htrace : WordTrace (prefixWord ++ tailWord_830308) baseStart_830308 baseEnd_830308 := by
    simpa [prefixWord, tailWord_830308, baseEnd_830308] using wordTrace_append hprefix tailTrace_830308
  have hstable : (prefixWord ++ tailWord_830308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830308).length < 2 ^ (prefixWord ++ tailWord_830308).sum := by decide
  have hdescent : baseEnd_830308 < baseStart_830308 := by decide
  rcases family_descends (prefixWord ++ tailWord_830308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830322 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_830322 : Nat := 118140960795 + 830322 * 2 ^ 59
def prefixEnd_830322 : Nat := 4983230072969 + 3 ^ 40 * 830322 * 2
def baseEnd_830322 : Nat := 426354284002605595056425

theorem tailTrace_830322 : CollatzResearch.WordTrace tailWord_830322 prefixEnd_830322 426354284002605595056425 := by
  unfold tailWord_830322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571082824473169138205305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20189554198595117701880813 7571082824473169138205305)
  ·
    refine ⟨5678312118354876853653979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7571082824473169138205305 5678312118354876853653979)
    ·
      refine ⟨8517468177532315280480969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678312118354876853653979 8517468177532315280480969)
      ·
        refine ⟨6388101133149236460360727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8517468177532315280480969 6388101133149236460360727)
        ·
          refine ⟨9582151699723854690541091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6388101133149236460360727 9582151699723854690541091)
          ·
            refine ⟨14373227549585782035811637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582151699723854690541091 14373227549585782035811637)
            ·
              refine ⟨1347490082773667065857341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14373227549585782035811637 1347490082773667065857341)
              ·
                refine ⟨505308781040125149696503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1347490082773667065857341 505308781040125149696503)
                ·
                  refine ⟨757963171560187724544755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505308781040125149696503 757963171560187724544755)
                  ·
                    refine ⟨1136944757340281586817133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757963171560187724544755 1136944757340281586817133)
                    ·
                      refine ⟨426354284002605595056425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1136944757340281586817133 426354284002605595056425)
                      ·
                        rfl

theorem cell23_830322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_830322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830322 prefixEnd_830322 := by exact prefixLift 830322
  have htrace : WordTrace (prefixWord ++ tailWord_830322) baseStart_830322 baseEnd_830322 := by
    simpa [prefixWord, tailWord_830322, baseEnd_830322] using wordTrace_append hprefix tailTrace_830322
  have hstable : (prefixWord ++ tailWord_830322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830322).length < 2 ^ (prefixWord ++ tailWord_830322).sum := by decide
  have hdescent : baseEnd_830322 < baseStart_830322 := by decide
  rcases family_descends (prefixWord ++ tailWord_830322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830331 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5]
def baseStart_830331 : Nat := 118140960795 + 830331 * 2 ^ 59
def prefixEnd_830331 : Nat := 4983230072969 + 3 ^ 40 * 830331 * 2
def baseEnd_830331 : Nat := 426358905328496059843883

theorem tailTrace_830331 : CollatzResearch.WordTrace tailWord_830331 prefixEnd_830331 426358905328496059843883 := by
  unfold tailWord_830331
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284659554860071089898847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20189773036573380726599231 30284659554860071089898847)
  ·
    refine ⟨45426989332290106634848271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30284659554860071089898847 45426989332290106634848271)
    ·
      refine ⟨68140483998435159952272407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45426989332290106634848271 68140483998435159952272407)
      ·
        refine ⟨102210725997652739928408611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68140483998435159952272407 102210725997652739928408611)
        ·
          refine ⟨153316088996479109892612917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102210725997652739928408611 153316088996479109892612917)
          ·
            refine ⟨14373383343419916552432461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153316088996479109892612917 14373383343419916552432461)
            ·
              refine ⟨5390018753782468707162173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14373383343419916552432461 5390018753782468707162173)
              ·
                refine ⟨2021257032668425765185815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5390018753782468707162173 2021257032668425765185815)
                ·
                  refine ⟨3031885549002638647778723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021257032668425765185815 3031885549002638647778723)
                  ·
                    refine ⟨4547828323503957971668085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031885549002638647778723 4547828323503957971668085)
                    ·
                      refine ⟨426358905328496059843883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4547828323503957971668085 426358905328496059843883)
                      ·
                        rfl

theorem cell23_830331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].length) (baseStart_830331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830331 prefixEnd_830331 := by exact prefixLift 830331
  have htrace : WordTrace (prefixWord ++ tailWord_830331) baseStart_830331 baseEnd_830331 := by
    simpa [prefixWord, tailWord_830331, baseEnd_830331] using wordTrace_append hprefix tailTrace_830331
  have hstable : (prefixWord ++ tailWord_830331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830331).length < 2 ^ (prefixWord ++ tailWord_830331).sum := by decide
  have hdescent : baseEnd_830331 < baseStart_830331 := by decide
  rcases family_descends (prefixWord ++ tailWord_830331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830341 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_830341 : Nat := 118140960795 + 830341 * 2 ^ 59
def prefixEnd_830341 : Nat := 4983230072969 + 3 ^ 40 * 830341 * 2
def baseEnd_830341 : Nat := 426364040135041020718837

theorem tailTrace_830341 : CollatzResearch.WordTrace tailWord_830341 prefixEnd_830341 426364040135041020718837 := by
  unfold tailWord_830341
  simp only [CollatzResearch.WordTrace]
  refine ⟨30285024284823842797762877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20190016189882561865175251 30285024284823842797762877)
  ·
    refine ⟨11356884106808941049161079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30285024284823842797762877 11356884106808941049161079)
    ·
      refine ⟨17035326160213411573741619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11356884106808941049161079 17035326160213411573741619)
      ·
        refine ⟨25552989240320117360612429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17035326160213411573741619 25552989240320117360612429)
        ·
          refine ⟨9582370965120044010229661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25552989240320117360612429 9582370965120044010229661)
          ·
            refine ⟨3593389111920016503836123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9582370965120044010229661 3593389111920016503836123)
            ·
              refine ⟨5390083667880024755754185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593389111920016503836123 5390083667880024755754185)
              ·
                refine ⟨4042562750910018566815639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5390083667880024755754185 4042562750910018566815639)
                ·
                  refine ⟨6063844126365027850223459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042562750910018566815639 6063844126365027850223459)
                  ·
                    refine ⟨9095766189547541775335189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6063844126365027850223459 9095766189547541775335189)
                    ·
                      refine ⟨426364040135041020718837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9095766189547541775335189 426364040135041020718837)
                      ·
                        rfl

theorem cell23_830341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_830341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830341 prefixEnd_830341 := by exact prefixLift 830341
  have htrace : WordTrace (prefixWord ++ tailWord_830341) baseStart_830341 baseEnd_830341 := by
    simpa [prefixWord, tailWord_830341, baseEnd_830341] using wordTrace_append hprefix tailTrace_830341
  have hstable : (prefixWord ++ tailWord_830341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830341).length < 2 ^ (prefixWord ++ tailWord_830341).sum := by decide
  have hdescent : baseEnd_830341 < baseStart_830341 := by decide
  rcases family_descends (prefixWord ++ tailWord_830341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830362 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_830362 : Nat := 118140960795 + 830362 * 2 ^ 59
def prefixEnd_830362 : Nat := 4983230072969 + 3 ^ 40 * 830362 * 2
def baseEnd_830362 : Nat := 426374823228785438556241

theorem tailTrace_830362 : CollatzResearch.WordTrace tailWord_830362 prefixEnd_830362 426374823228785438556241 := by
  unfold tailWord_830362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571447554436940846069335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20190526811831842256184893 7571447554436940846069335)
  ·
    refine ⟨11357171331655411269104003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7571447554436940846069335 11357171331655411269104003)
    ·
      refine ⟨17035756997483116903656005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11357171331655411269104003 17035756997483116903656005)
      ·
        refine ⟨3194204437028084419435501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17035756997483116903656005 3194204437028084419435501)
        ·
          refine ⟨1197826663885531657288313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3194204437028084419435501 1197826663885531657288313)
          ·
            refine ⟨898369997914148742966235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197826663885531657288313 898369997914148742966235)
            ·
              refine ⟨1347554996871223114449353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898369997914148742966235 1347554996871223114449353)
              ·
                refine ⟨1010666247653417335837015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347554996871223114449353 1010666247653417335837015)
                ·
                  refine ⟨1515999371480126003755523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010666247653417335837015 1515999371480126003755523)
                  ·
                    refine ⟨2273999057220189005633285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1515999371480126003755523 2273999057220189005633285)
                    ·
                      refine ⟨426374823228785438556241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2273999057220189005633285 426374823228785438556241)
                      ·
                        rfl

theorem cell23_830362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_830362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830362 prefixEnd_830362 := by exact prefixLift 830362
  have htrace : WordTrace (prefixWord ++ tailWord_830362) baseStart_830362 baseEnd_830362 := by
    simpa [prefixWord, tailWord_830362, baseEnd_830362] using wordTrace_append hprefix tailTrace_830362
  have hstable : (prefixWord ++ tailWord_830362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830362).length < 2 ^ (prefixWord ++ tailWord_830362).sum := by decide
  have hdescent : baseEnd_830362 < baseStart_830362 := by decide
  rcases family_descends (prefixWord ++ tailWord_830362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830375 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_830375 : Nat := 118140960795 + 830375 * 2 ^ 59
def prefixEnd_830375 : Nat := 4983230072969 + 3 ^ 40 * 830375 * 2
def baseEnd_830375 : Nat := 426381498477293887693681

theorem tailTrace_830375 : CollatzResearch.WordTrace tailWord_830375 prefixEnd_830375 426381498477293887693681 := by
  unfold tailWord_830375
  simp only [CollatzResearch.WordTrace]
  refine ⟨30286264366700666604500579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20190842911133777736333719 30286264366700666604500579)
  ·
    refine ⟨45429396550050999906750869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30286264366700666604500579 45429396550050999906750869)
    ·
      refine ⟨2129502963283640620628947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45429396550050999906750869 2129502963283640620628947)
      ·
        refine ⟨3194254444925460930943421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129502963283640620628947 3194254444925460930943421)
        ·
          refine ⟨1197845416847047849103783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3194254444925460930943421 1197845416847047849103783)
          ·
            refine ⟨1796768125270571773655675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197845416847047849103783 1796768125270571773655675)
            ·
              refine ⟨2695152187905857660483513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796768125270571773655675 2695152187905857660483513)
              ·
                refine ⟨2021364140929393245362635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695152187905857660483513 2021364140929393245362635)
                ·
                  refine ⟨3032046211394089868043953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021364140929393245362635 3032046211394089868043953)
                  ·
                    refine ⟨2274034658545567401032965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3032046211394089868043953 2274034658545567401032965)
                    ·
                      refine ⟨426381498477293887693681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2274034658545567401032965 426381498477293887693681)
                      ·
                        rfl

theorem cell23_830375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_830375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830375 prefixEnd_830375 := by exact prefixLift 830375
  have htrace : WordTrace (prefixWord ++ tailWord_830375) baseStart_830375 baseEnd_830375 := by
    simpa [prefixWord, tailWord_830375, baseEnd_830375] using wordTrace_append hprefix tailTrace_830375
  have hstable : (prefixWord ++ tailWord_830375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830375).length < 2 ^ (prefixWord ++ tailWord_830375).sum := by decide
  have hdescent : baseEnd_830375 < baseStart_830375 := by decide
  rcases family_descends (prefixWord ++ tailWord_830375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830391 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_830391 : Nat := 118140960795 + 830391 * 2 ^ 59
def prefixEnd_830391 : Nat := 4983230072969 + 3 ^ 40 * 830391 * 2
def baseEnd_830391 : Nat := 426389714167765825093607

theorem tailTrace_830391 : CollatzResearch.WordTrace tailWord_830391 prefixEnd_830391 426389714167765825093607 := by
  unfold tailWord_830391
  simp only [CollatzResearch.WordTrace]
  refine ⟨30286847934642701337083027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20191231956428467558055351 30286847934642701337083027)
  ·
    refine ⟨45430271901964052005624541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30286847934642701337083027 45430271901964052005624541)
    ·
      refine ⟨17036351963236519502109203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45430271901964052005624541 17036351963236519502109203)
      ·
        refine ⟨25554527944854779253163805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17036351963236519502109203 25554527944854779253163805)
        ·
          refine ⟨9582947979320542219936427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25554527944854779253163805 9582947979320542219936427)
          ·
            refine ⟨14374421968980813329904641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582947979320542219936427 14374421968980813329904641)
            ·
              refine ⟨10780816476735609997428481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14374421968980813329904641 10780816476735609997428481)
              ·
                refine ⟨8085612357551707498071361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10780816476735609997428481 8085612357551707498071361)
                ·
                  refine ⟨6064209268163780623553521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8085612357551707498071361 6064209268163780623553521)
                  ·
                    refine ⟨4548156951122835467665141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6064209268163780623553521 4548156951122835467665141)
                    ·
                      refine ⟨426389714167765825093607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4548156951122835467665141 426389714167765825093607)
                      ·
                        rfl

theorem cell23_830391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_830391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830391 prefixEnd_830391 := by exact prefixLift 830391
  have htrace : WordTrace (prefixWord ++ tailWord_830391) baseStart_830391 baseEnd_830391 := by
    simpa [prefixWord, tailWord_830391, baseEnd_830391] using wordTrace_append hprefix tailTrace_830391
  have hstable : (prefixWord ++ tailWord_830391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830391).length < 2 ^ (prefixWord ++ tailWord_830391).sum := by decide
  have hdescent : baseEnd_830391 < baseStart_830391 := by decide
  rcases family_descends (prefixWord ++ tailWord_830391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830406 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_830406 : Nat := 118140960795 + 830406 * 2 ^ 59
def prefixEnd_830406 : Nat := 4983230072969 + 3 ^ 40 * 830406 * 2
def baseEnd_830406 : Nat := 142132472125861088802013

theorem tailTrace_830406 : CollatzResearch.WordTrace tailWord_830406 prefixEnd_830406 142132472125861088802013 := by
  unfold tailWord_830406
  simp only [CollatzResearch.WordTrace]
  refine ⟨946481094674636215589971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20191596686392239265919381 946481094674636215589971)
  ·
    refine ⟨1419721642011954323384957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 946481094674636215589971 1419721642011954323384957)
    ·
      refine ⟨532395615754482871269359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1419721642011954323384957 532395615754482871269359)
      ·
        refine ⟨798593423631724306904039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532395615754482871269359 798593423631724306904039)
        ·
          refine ⟨1197890135447586460356059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798593423631724306904039 1197890135447586460356059)
          ·
            refine ⟨1796835203171379690534089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197890135447586460356059 1796835203171379690534089)
            ·
              refine ⟨1347626402378534767900567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1796835203171379690534089 1347626402378534767900567)
              ·
                refine ⟨2021439603567802151850851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347626402378534767900567 2021439603567802151850851)
                ·
                  refine ⟨3032159405351703227776277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021439603567802151850851 3032159405351703227776277)
                  ·
                    refine ⟨142132472125861088802013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3032159405351703227776277 142132472125861088802013)
                    ·
                      rfl

theorem cell23_830406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_830406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830406 prefixEnd_830406 := by exact prefixLift 830406
  have htrace : WordTrace (prefixWord ++ tailWord_830406) baseStart_830406 baseEnd_830406 := by
    simpa [prefixWord, tailWord_830406, baseEnd_830406] using wordTrace_append hprefix tailTrace_830406
  have hstable : (prefixWord ++ tailWord_830406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830406).length < 2 ^ (prefixWord ++ tailWord_830406).sum := by decide
  have hdescent : baseEnd_830406 < baseStart_830406 := by decide
  rcases family_descends (prefixWord ++ tailWord_830406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830411 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 8]
def baseStart_830411 : Nat := 118140960795 + 830411 * 2 ^ 59
def prefixEnd_830411 : Nat := 4983230072969 + 3 ^ 40 * 830411 * 2
def baseEnd_830411 : Nat := 142133327926951915614505

theorem tailTrace_830411 : CollatzResearch.WordTrace tailWord_830411 prefixEnd_830411 142133327926951915614505 := by
  unfold tailWord_830411
  simp only [CollatzResearch.WordTrace]
  refine ⟨30287577394570244752811087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20191718263046829835207391 30287577394570244752811087)
  ·
    refine ⟨45431366091855367129216631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30287577394570244752811087 45431366091855367129216631)
    ·
      refine ⟨68147049137783050693824947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45431366091855367129216631 68147049137783050693824947)
      ·
        refine ⟨102220573706674576040737421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68147049137783050693824947 102220573706674576040737421)
        ·
          refine ⟨38332715140002966015276533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102220573706674576040737421 38332715140002966015276533)
          ·
            refine ⟨3593692044375278063932175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38332715140002966015276533 3593692044375278063932175)
            ·
              refine ⟨5390538066562917095898263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593692044375278063932175 5390538066562917095898263)
              ·
                refine ⟨8085807099844375643847395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390538066562917095898263 8085807099844375643847395)
                ·
                  refine ⟨12128710649766563465771093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8085807099844375643847395 12128710649766563465771093)
                  ·
                    refine ⟨142133327926951915614505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12128710649766563465771093 142133327926951915614505)
                    ·
                      rfl

theorem cell23_830411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_830411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830411 prefixEnd_830411 := by exact prefixLift 830411
  have htrace : WordTrace (prefixWord ++ tailWord_830411) baseStart_830411 baseEnd_830411 := by
    simpa [prefixWord, tailWord_830411, baseEnd_830411] using wordTrace_append hprefix tailTrace_830411
  have hstable : (prefixWord ++ tailWord_830411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830411).length < 2 ^ (prefixWord ++ tailWord_830411).sum := by decide
  have hdescent : baseEnd_830411 < baseStart_830411 := by decide
  rcases family_descends (prefixWord ++ tailWord_830411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830413 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_830413 : Nat := 118140960795 + 830413 * 2 ^ 59
def prefixEnd_830413 : Nat := 4983230072969 + 3 ^ 40 * 830413 * 2
def baseEnd_830413 : Nat := 426401010742164739018507

theorem tailTrace_830413 : CollatzResearch.WordTrace tailWord_830413 prefixEnd_830413 426401010742164739018507 := by
  unfold tailWord_830413
  simp only [CollatzResearch.WordTrace]
  refine ⟨30287650340562999094383893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20191766893708666062922595 30287650340562999094383893)
  ·
    refine ⟨1419733609713890582549245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30287650340562999094383893 1419733609713890582549245)
    ·
      refine ⟨532400103642708968455967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1419733609713890582549245 532400103642708968455967)
      ·
        refine ⟨798600155464063452683951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532400103642708968455967 798600155464063452683951)
        ·
          refine ⟨1197900233196095179025927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798600155464063452683951 1197900233196095179025927)
          ·
            refine ⟨1796850349794142768538891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197900233196095179025927 1796850349794142768538891)
            ·
              refine ⟨2695275524691214152808337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796850349794142768538891 2695275524691214152808337)
              ·
                refine ⟨2021456643518410614606253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695275524691214152808337 2021456643518410614606253)
                ·
                  refine ⟨758046241319403980477345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2021456643518410614606253 758046241319403980477345)
                  ·
                    refine ⟨568534680989552985358009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 758046241319403980477345 568534680989552985358009)
                    ·
                      refine ⟨426401010742164739018507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568534680989552985358009 426401010742164739018507)
                      ·
                        rfl

theorem cell23_830413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_830413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830413 prefixEnd_830413 := by exact prefixLift 830413
  have htrace : WordTrace (prefixWord ++ tailWord_830413) baseStart_830413 baseEnd_830413 := by
    simpa [prefixWord, tailWord_830413, baseEnd_830413] using wordTrace_append hprefix tailTrace_830413
  have hstable : (prefixWord ++ tailWord_830413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830413).length < 2 ^ (prefixWord ++ tailWord_830413).sum := by decide
  have hdescent : baseEnd_830413 < baseStart_830413 := by decide
  rcases family_descends (prefixWord ++ tailWord_830413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830435 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 1, 4, 2]
def baseStart_830435 : Nat := 118140960795 + 830435 * 2 ^ 59
def prefixEnd_830435 : Nat := 4983230072969 + 3 ^ 40 * 830435 * 2
def baseEnd_830435 : Nat := 426412307316563652943405

theorem tailTrace_830435 : CollatzResearch.WordTrace tailWord_830435 prefixEnd_830435 426412307316563652943405 := by
  unfold tailWord_830435
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288452746483296851684759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20192301830988864567789839 30288452746483296851684759)
  ·
    refine ⟨45432679119724945277527139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30288452746483296851684759 45432679119724945277527139)
    ·
      refine ⟨68149018679587417916290709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45432679119724945277527139 68149018679587417916290709)
      ·
        refine ⟨3194485250605660214826127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68149018679587417916290709 3194485250605660214826127)
        ·
          refine ⟨4791727875908490322239191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194485250605660214826127 4791727875908490322239191)
          ·
            refine ⟨7187591813862735483358787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791727875908490322239191 7187591813862735483358787)
            ·
              refine ⟨10781387720794103225038181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187591813862735483358787 10781387720794103225038181)
              ·
                refine ⟨2021510197648894354694659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10781387720794103225038181 2021510197648894354694659)
                ·
                  refine ⟨3032265296473341532041989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021510197648894354694659 3032265296473341532041989)
                  ·
                    refine ⟨568549743088751537257873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032265296473341532041989 568549743088751537257873)
                    ·
                      refine ⟨426412307316563652943405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568549743088751537257873 426412307316563652943405)
                      ·
                        rfl

theorem cell23_830435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_830435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830435 prefixEnd_830435 := by exact prefixLift 830435
  have htrace : WordTrace (prefixWord ++ tailWord_830435) baseStart_830435 baseEnd_830435 := by
    simpa [prefixWord, tailWord_830435, baseEnd_830435] using wordTrace_append hprefix tailTrace_830435
  have hstable : (prefixWord ++ tailWord_830435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830435).length < 2 ^ (prefixWord ++ tailWord_830435).sum := by decide
  have hdescent : baseEnd_830435 < baseStart_830435 := by decide
  rcases family_descends (prefixWord ++ tailWord_830435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830439 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_830439 : Nat := 118140960795 + 830439 * 2 ^ 59
def prefixEnd_830439 : Nat := 4983230072969 + 3 ^ 40 * 830439 * 2
def baseEnd_830439 : Nat := 426414361239181637293387

theorem tailTrace_830439 : CollatzResearch.WordTrace tailWord_830439 prefixEnd_830439 426414361239181637293387 := by
  unfold tailWord_830439
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288598638468805534830371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20192399092312537023220247 30288598638468805534830371)
  ·
    refine ⟨45432897957703208302245557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30288598638468805534830371 45432897957703208302245557)
    ·
      refine ⟨4259334183534675778335521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45432897957703208302245557 4259334183534675778335521)
      ·
        refine ⟨3194500637651006833751641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4259334183534675778335521 3194500637651006833751641)
        ·
          refine ⟨2395875478238255125313731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3194500637651006833751641 2395875478238255125313731)
          ·
            refine ⟨3593813217357382687970597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395875478238255125313731 3593813217357382687970597)
            ·
              refine ⟨673839978254509253994487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3593813217357382687970597 673839978254509253994487)
              ·
                refine ⟨1010759967381763880991731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673839978254509253994487 1010759967381763880991731)
                ·
                  refine ⟨1516139951072645821487597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010759967381763880991731 1516139951072645821487597)
                  ·
                    refine ⟨568552481652242183057849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516139951072645821487597 568552481652242183057849)
                    ·
                      refine ⟨426414361239181637293387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568552481652242183057849 426414361239181637293387)
                      ·
                        rfl

theorem cell23_830439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_830439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830439 prefixEnd_830439 := by exact prefixLift 830439
  have htrace : WordTrace (prefixWord ++ tailWord_830439) baseStart_830439 baseEnd_830439 := by
    simpa [prefixWord, tailWord_830439, baseEnd_830439] using wordTrace_append hprefix tailTrace_830439
  have hstable : (prefixWord ++ tailWord_830439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830439).length < 2 ^ (prefixWord ++ tailWord_830439).sum := by decide
  have hdescent : baseEnd_830439 < baseStart_830439 := by decide
  rcases family_descends (prefixWord ++ tailWord_830439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830446 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_830446 : Nat := 118140960795 + 830446 * 2 ^ 59
def prefixEnd_830446 : Nat := 4983230072969 + 3 ^ 40 * 830446 * 2
def baseEnd_830446 : Nat := 426417955603763109905855

theorem tailTrace_830446 : CollatzResearch.WordTrace tailWord_830446 prefixEnd_830446 426417955603763109905855 := by
  unfold tailWord_830446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786106743680430716291899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20192569299628963820223461 3786106743680430716291899)
  ·
    refine ⟨5679160115520646074437849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786106743680430716291899 5679160115520646074437849)
    ·
      refine ⟨4259370086640484555828387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5679160115520646074437849 4259370086640484555828387)
      ·
        refine ⟨6389055129960726833742581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259370086640484555828387 6389055129960726833742581)
        ·
          refine ⟨598973918433818140663367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6389055129960726833742581 598973918433818140663367)
          ·
            refine ⟨898460877650727210995051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598973918433818140663367 898460877650727210995051)
            ·
              refine ⟨1347691316476090816492577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898460877650727210995051 1347691316476090816492577)
              ·
                refine ⟨1010768487357068112369433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347691316476090816492577 1010768487357068112369433)
                ·
                  refine ⟨758076365517801084277075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010768487357068112369433 758076365517801084277075)
                  ·
                    refine ⟨1137114548276701626415613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 758076365517801084277075 1137114548276701626415613)
                    ·
                      refine ⟨426417955603763109905855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137114548276701626415613 426417955603763109905855)
                      ·
                        rfl

theorem cell23_830446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_830446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830446 prefixEnd_830446 := by exact prefixLift 830446
  have htrace : WordTrace (prefixWord ++ tailWord_830446) baseStart_830446 baseEnd_830446 := by
    simpa [prefixWord, tailWord_830446, baseEnd_830446] using wordTrace_append hprefix tailTrace_830446
  have hstable : (prefixWord ++ tailWord_830446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830446).length < 2 ^ (prefixWord ++ tailWord_830446).sum := by decide
  have hdescent : baseEnd_830446 < baseStart_830446 := by decide
  rcases family_descends (prefixWord ++ tailWord_830446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830469 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 2, 2, 2]
def baseStart_830469 : Nat := 118140960795 + 830469 * 2 ^ 59
def prefixEnd_830469 : Nat := 4983230072969 + 3 ^ 40 * 830469 * 2
def baseEnd_830469 : Nat := 426429765658816519918249

theorem tailTrace_830469 : CollatzResearch.WordTrace tailWord_830469 prefixEnd_830469 426429765658816519918249 := by
  unfold tailWord_830469
  simp only [CollatzResearch.WordTrace]
  refine ⟨30289692828360120658422461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20193128552240080438948307 30289692828360120658422461)
  ·
    refine ⟨11358634810635045246908423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30289692828360120658422461 11358634810635045246908423)
    ·
      refine ⟨17037952215952567870362635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11358634810635045246908423 17037952215952567870362635)
      ·
        refine ⟨25556928323928851805543953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17037952215952567870362635 25556928323928851805543953)
        ·
          refine ⟨19167696242946638854157965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25556928323928851805543953 19167696242946638854157965)
          ·
            refine ⟨7187886091104989570309237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19167696242946638854157965 7187886091104989570309237)
            ·
              refine ⟨673864321041092772216491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7187886091104989570309237 673864321041092772216491)
              ·
                refine ⟨1010796481561639158324737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673864321041092772216491 1010796481561639158324737)
                ·
                  refine ⟨758097361171229368743553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010796481561639158324737 758097361171229368743553)
                  ·
                    refine ⟨568573020878422026557665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 758097361171229368743553 568573020878422026557665)
                    ·
                      refine ⟨426429765658816519918249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568573020878422026557665 426429765658816519918249)
                      ·
                        rfl

theorem cell23_830469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_830469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830469 prefixEnd_830469 := by exact prefixLift 830469
  have htrace : WordTrace (prefixWord ++ tailWord_830469) baseStart_830469 baseEnd_830469 := by
    simpa [prefixWord, tailWord_830469, baseEnd_830469] using wordTrace_append hprefix tailTrace_830469
  have hstable : (prefixWord ++ tailWord_830469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830469).length < 2 ^ (prefixWord ++ tailWord_830469).sum := by decide
  have hdescent : baseEnd_830469 < baseStart_830469 := by decide
  rcases family_descends (prefixWord ++ tailWord_830469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830488 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_830488 : Nat := 118140960795 + 830488 * 2 ^ 59
def prefixEnd_830488 : Nat := 4983230072969 + 3 ^ 40 * 830488 * 2
def baseEnd_830488 : Nat := 142146507263750648526887

theorem tailTrace_830488 : CollatzResearch.WordTrace tailWord_830488 prefixEnd_830488 142146507263750648526887 := by
  unfold tailWord_830488
  simp only [CollatzResearch.WordTrace]
  refine ⟨15145192907645643451682059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20193590543527524602242745 15145192907645643451682059)
  ·
    refine ⟨22717789361468465177523089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15145192907645643451682059 22717789361468465177523089)
    ·
      refine ⟨17038342021101348883142317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22717789361468465177523089 17038342021101348883142317)
      ·
        refine ⟨6389378257913005831178369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17038342021101348883142317 6389378257913005831178369)
        ·
          refine ⟨4792033693434754373383777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6389378257913005831178369 4792033693434754373383777)
          ·
            refine ⟨3594025270076065780037833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4792033693434754373383777 3594025270076065780037833)
            ·
              refine ⟨2695518952557049335028375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594025270076065780037833 2695518952557049335028375)
              ·
                refine ⟨4043278428835574002542563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695518952557049335028375 4043278428835574002542563)
                ·
                  refine ⟨6064917643253361003813845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043278428835574002542563 6064917643253361003813845)
                  ·
                    refine ⟨142146507263750648526887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6064917643253361003813845 142146507263750648526887)
                    ·
                      rfl

theorem cell23_830488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_830488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830488 prefixEnd_830488 := by exact prefixLift 830488
  have htrace : WordTrace (prefixWord ++ tailWord_830488) baseStart_830488 baseEnd_830488 := by
    simpa [prefixWord, tailWord_830488, baseEnd_830488] using wordTrace_append hprefix tailTrace_830488
  have hstable : (prefixWord ++ tailWord_830488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830488).length < 2 ^ (prefixWord ++ tailWord_830488).sum := by decide
  have hdescent : baseEnd_830488 < baseStart_830488 := by decide
  rcases family_descends (prefixWord ++ tailWord_830488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830491 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_830491 : Nat := 118140960795 + 830491 * 2 ^ 59
def prefixEnd_830491 : Nat := 4983230072969 + 3 ^ 40 * 830491 * 2
def baseEnd_830491 : Nat := 426441062233215433843147

theorem tailTrace_830491 : CollatzResearch.WordTrace tailWord_830491 prefixEnd_830491 426441062233215433843147 := by
  unfold tailWord_830491
  simp only [CollatzResearch.WordTrace]
  refine ⟨30290495234280418415723327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20193663489520278943815551 30290495234280418415723327)
  ·
    refine ⟨45435742851420627623584991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30290495234280418415723327 45435742851420627623584991)
    ·
      refine ⟨68153614277130941435377487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45435742851420627623584991 68153614277130941435377487)
      ·
        refine ⟨102230421415696412153066231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68153614277130941435377487 102230421415696412153066231)
        ·
          refine ⟨153345632123544618229599347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102230421415696412153066231 153345632123544618229599347)
          ·
            refine ⟨230018448185316927344399021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153345632123544618229599347 230018448185316927344399021)
            ·
              refine ⟨86256918069493847754149633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230018448185316927344399021 86256918069493847754149633)
              ·
                refine ⟨64692688552120385815612225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86256918069493847754149633 64692688552120385815612225)
                ·
                  refine ⟨48519516414090289361709169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64692688552120385815612225 48519516414090289361709169)
                  ·
                    refine ⟨36389637310567717021281877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48519516414090289361709169 36389637310567717021281877)
                    ·
                      refine ⟨426441062233215433843147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36389637310567717021281877 426441062233215433843147)
                      ·
                        rfl

theorem cell23_830491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_830491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830491 prefixEnd_830491 := by exact prefixLift 830491
  have htrace : WordTrace (prefixWord ++ tailWord_830491) baseStart_830491 baseEnd_830491 := by
    simpa [prefixWord, tailWord_830491, baseEnd_830491] using wordTrace_append hprefix tailTrace_830491
  have hstable : (prefixWord ++ tailWord_830491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830491).length < 2 ^ (prefixWord ++ tailWord_830491).sum := by decide
  have hdescent : baseEnd_830491 < baseStart_830491 := by decide
  rcases family_descends (prefixWord ++ tailWord_830491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830538 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_830538 : Nat := 118140960795 + 830538 * 2 ^ 59
def prefixEnd_830538 : Nat := 4983230072969 + 3 ^ 40 * 830538 * 2
def baseEnd_830538 : Nat := 426465195823976749955431

theorem tailTrace_830538 : CollatzResearch.WordTrace tailWord_830538 prefixEnd_830538 426465195823976749955431 := by
  unfold tailWord_830538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7573052366277536360671067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20194806310073430295122845 7573052366277536360671067)
  ·
    refine ⟨11359578549416304541006601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7573052366277536360671067 11359578549416304541006601)
    ·
      refine ⟨8519683912062228405754951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11359578549416304541006601 8519683912062228405754951)
      ·
        refine ⟨12779525868093342608632427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519683912062228405754951 12779525868093342608632427)
        ·
          refine ⟨19169288802140013912948641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779525868093342608632427 19169288802140013912948641)
          ·
            refine ⟨14376966601605010434711481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19169288802140013912948641 14376966601605010434711481)
            ·
              refine ⟨10782724951203757826033611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14376966601605010434711481 10782724951203757826033611)
              ·
                refine ⟨16174087426805636739050417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10782724951203757826033611 16174087426805636739050417)
                ·
                  refine ⟨12130565570104227554287813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16174087426805636739050417 12130565570104227554287813)
                  ·
                    refine ⟨2274481044394542666428965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12130565570104227554287813 2274481044394542666428965)
                    ·
                      refine ⟨426465195823976749955431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2274481044394542666428965 426465195823976749955431)
                      ·
                        rfl

theorem cell23_830538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_830538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830538 prefixEnd_830538 := by exact prefixLift 830538
  have htrace : WordTrace (prefixWord ++ tailWord_830538) baseStart_830538 baseEnd_830538 := by
    simpa [prefixWord, tailWord_830538, baseEnd_830538] using wordTrace_append hprefix tailTrace_830538
  have hstable : (prefixWord ++ tailWord_830538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830538).length < 2 ^ (prefixWord ++ tailWord_830538).sum := by decide
  have hdescent : baseEnd_830538 < baseStart_830538 := by decide
  rcases family_descends (prefixWord ++ tailWord_830538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830545 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_830545 : Nat := 118140960795 + 830545 * 2 ^ 59
def prefixEnd_830545 : Nat := 4983230072969 + 3 ^ 40 * 830545 * 2
def baseEnd_830545 : Nat := 426468790188558222567899

theorem tailTrace_830545 : CollatzResearch.WordTrace tailWord_830545 prefixEnd_830545 426468790188558222567899 := by
  unfold tailWord_830545
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292464776084785638189089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20194976517389857092126059 30292464776084785638189089)
  ·
    refine ⟨22719348582063589228641817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30292464776084785638189089 22719348582063589228641817)
    ·
      refine ⟨17039511436547691921481363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22719348582063589228641817 17039511436547691921481363)
      ·
        refine ⟨25559267154821537882222045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039511436547691921481363 25559267154821537882222045)
        ·
          refine ⟨9584725183058076705833267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25559267154821537882222045 9584725183058076705833267)
          ·
            refine ⟨14377087774587115058749901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584725183058076705833267 14377087774587115058749901)
            ·
              refine ⟨5391407915470168147031213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14377087774587115058749901 5391407915470168147031213)
              ·
                refine ⟨2021777968301313055136705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5391407915470168147031213 2021777968301313055136705)
                ·
                  refine ⟨1516333476225984791352529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2021777968301313055136705 1516333476225984791352529)
                  ·
                    refine ⟨1137250107169488593514397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1516333476225984791352529 1137250107169488593514397)
                    ·
                      refine ⟨426468790188558222567899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137250107169488593514397 426468790188558222567899)
                      ·
                        rfl

theorem cell23_830545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_830545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830545 prefixEnd_830545 := by exact prefixLift 830545
  have htrace : WordTrace (prefixWord ++ tailWord_830545) baseStart_830545 baseEnd_830545 := by
    simpa [prefixWord, tailWord_830545, baseEnd_830545] using wordTrace_append hprefix tailTrace_830545
  have hstable : (prefixWord ++ tailWord_830545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830545).length < 2 ^ (prefixWord ++ tailWord_830545).sum := by decide
  have hdescent : baseEnd_830545 < baseStart_830545 := by decide
  rcases family_descends (prefixWord ++ tailWord_830545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830548 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 10]
def baseStart_830548 : Nat := 118140960795 + 830548 * 2 ^ 59
def prefixEnd_830548 : Nat := 4983230072969 + 3 ^ 40 * 830548 * 2
def baseEnd_830548 : Nat := 47385592292280190092265

theorem tailTrace_830548 : CollatzResearch.WordTrace tailWord_830548 prefixEnd_830548 47385592292280190092265 := by
  unfold tailWord_830548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15146287097536958575274149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20195049463382611433698865 15146287097536958575274149)
  ·
    refine ⟨2839928830788179732863903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15146287097536958575274149 2839928830788179732863903)
    ·
      refine ⟨4259893246182269599295855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2839928830788179732863903 4259893246182269599295855)
      ·
        refine ⟨6389839869273404398943783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259893246182269599295855 6389839869273404398943783)
        ·
          refine ⟨9584759803910106598415675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389839869273404398943783 9584759803910106598415675)
          ·
            refine ⟨14377139705865159897623513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584759803910106598415675 14377139705865159897623513)
            ·
              refine ⟨10782854779398869923217635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14377139705865159897623513 10782854779398869923217635)
              ·
                refine ⟨16174282169098304884826453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10782854779398869923217635 16174282169098304884826453)
                ·
                  refine ⟨47385592292280190092265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 16174282169098304884826453 47385592292280190092265)
                  ·
                    rfl

theorem cell23_830548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_830548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830548 prefixEnd_830548 := by exact prefixLift 830548
  have htrace : WordTrace (prefixWord ++ tailWord_830548) baseStart_830548 baseEnd_830548 := by
    simpa [prefixWord, tailWord_830548, baseEnd_830548] using wordTrace_append hprefix tailTrace_830548
  have hstable : (prefixWord ++ tailWord_830548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830548).length < 2 ^ (prefixWord ++ tailWord_830548).sum := by decide
  have hdescent : baseEnd_830548 < baseStart_830548 := by decide
  rcases family_descends (prefixWord ++ tailWord_830548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830552 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 1, 4]
def baseStart_830552 : Nat := 118140960795 + 830552 * 2 ^ 59
def prefixEnd_830552 : Nat := 4983230072969 + 3 ^ 40 * 830552 * 2
def baseEnd_830552 : Nat := 142157461517713231726789

theorem tailTrace_830552 : CollatzResearch.WordTrace tailWord_830552 prefixEnd_830552 142157461517713231726789 := by
  unfold tailWord_830552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15146360043529712916846955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20195146724706283889129273 15146360043529712916846955)
  ·
    refine ⟨22719540065294569375270433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15146360043529712916846955 22719540065294569375270433)
    ·
      refine ⟨17039655048970927031452825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22719540065294569375270433 17039655048970927031452825)
      ·
        refine ⟨12779741286728195273589619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17039655048970927031452825 12779741286728195273589619)
        ·
          refine ⟨19169611930092292910384429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779741286728195273589619 19169611930092292910384429)
          ·
            refine ⟨7188604473784609841394161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19169611930092292910384429 7188604473784609841394161)
            ·
              refine ⟨5391453355338457381045621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188604473784609841394161 5391453355338457381045621)
              ·
                refine ⟨505448752062980379473027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5391453355338457381045621 505448752062980379473027)
                ·
                  refine ⟨758173128094470569209541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505448752062980379473027 758173128094470569209541)
                  ·
                    refine ⟨142157461517713231726789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758173128094470569209541 142157461517713231726789)
                    ·
                      rfl

theorem cell23_830552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_830552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830552 prefixEnd_830552 := by exact prefixLift 830552
  have htrace : WordTrace (prefixWord ++ tailWord_830552) baseStart_830552 baseEnd_830552 := by
    simpa [prefixWord, tailWord_830552, baseEnd_830552] using wordTrace_append hprefix tailTrace_830552
  have hstable : (prefixWord ++ tailWord_830552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830552).length < 2 ^ (prefixWord ++ tailWord_830552).sum := by decide
  have hdescent : baseEnd_830552 < baseStart_830552 := by decide
  rcases family_descends (prefixWord ++ tailWord_830552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830565 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 6]
def baseStart_830565 : Nat := 118140960795 + 830565 * 2 ^ 59
def prefixEnd_830565 : Nat := 4983230072969 + 3 ^ 40 * 830565 * 2
def baseEnd_830565 : Nat := 47386562200183127146423

theorem tailTrace_830565 : CollatzResearch.WordTrace tailWord_830565 prefixEnd_830565 47386562200183127146423 := by
  unfold tailWord_830565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30293194236012329053917149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20195462824008219369278099 30293194236012329053917149)
  ·
    refine ⟨11359947838504623395218931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30293194236012329053917149 11359947838504623395218931)
    ·
      refine ⟨17039921757756935092828397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11359947838504623395218931 17039921757756935092828397)
      ·
        refine ⟨6389970659158850659810649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17039921757756935092828397 6389970659158850659810649)
        ·
          refine ⟨4792477994369137994857987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6389970659158850659810649 4792477994369137994857987)
          ·
            refine ⟨7188716991553706992286981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792477994369137994857987 7188716991553706992286981)
            ·
              refine ⟨1347884435916320061053809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7188716991553706992286981 1347884435916320061053809)
              ·
                refine ⟨1010913326937240045790357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347884435916320061053809 1010913326937240045790357)
                ·
                  refine ⟨47386562200183127146423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1010913326937240045790357 47386562200183127146423)
                  ·
                    rfl

theorem cell23_830565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_830565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830565 prefixEnd_830565 := by exact prefixLift 830565
  have htrace : WordTrace (prefixWord ++ tailWord_830565) baseStart_830565 baseEnd_830565 := by
    simpa [prefixWord, tailWord_830565, baseEnd_830565] using wordTrace_append hprefix tailTrace_830565
  have hstable : (prefixWord ++ tailWord_830565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830565).length < 2 ^ (prefixWord ++ tailWord_830565).sum := by decide
  have hdescent : baseEnd_830565 < baseStart_830565 := by decide
  rcases family_descends (prefixWord ++ tailWord_830565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830569 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 1, 4]
def baseStart_830569 : Nat := 118140960795 + 830569 * 2 ^ 59
def prefixEnd_830569 : Nat := 4983230072969 + 3 ^ 40 * 830569 * 2
def baseEnd_830569 : Nat := 142160371241422042889263

theorem tailTrace_830569 : CollatzResearch.WordTrace tailWord_830569 prefixEnd_830569 142160371241422042889263 := by
  unfold tailWord_830569
  simp only [CollatzResearch.WordTrace]
  refine ⟨30293340127997837737062761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20195560085331891824708507 30293340127997837737062761)
  ·
    refine ⟨22720005095998378302797071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30293340127997837737062761 22720005095998378302797071)
    ·
      refine ⟨34080007643997567454195607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22720005095998378302797071 34080007643997567454195607)
      ·
        refine ⟨51120011465996351181293411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34080007643997567454195607 51120011465996351181293411)
        ·
          refine ⟨76680017198994526771940117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51120011465996351181293411 76680017198994526771940117)
          ·
            refine ⟨3594375806202868442434693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76680017198994526771940117 3594375806202868442434693)
            ·
              refine ⟨673945463663037832956505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3594375806202868442434693 673945463663037832956505)
              ·
                refine ⟨505459097747278374717379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673945463663037832956505 505459097747278374717379)
                ·
                  refine ⟨758188646620917562076069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505459097747278374717379 758188646620917562076069)
                  ·
                    refine ⟨142160371241422042889263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758188646620917562076069 142160371241422042889263)
                    ·
                      rfl

theorem cell23_830569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 4].length) (baseStart_830569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830569 prefixEnd_830569 := by exact prefixLift 830569
  have htrace : WordTrace (prefixWord ++ tailWord_830569) baseStart_830569 baseEnd_830569 := by
    simpa [prefixWord, tailWord_830569, baseEnd_830569] using wordTrace_append hprefix tailTrace_830569
  have hstable : (prefixWord ++ tailWord_830569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830569).length < 2 ^ (prefixWord ++ tailWord_830569).sum := by decide
  have hdescent : baseEnd_830569 < baseStart_830569 := by decide
  rcases family_descends (prefixWord ++ tailWord_830569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830588 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_830588 : Nat := 118140960795 + 830588 * 2 ^ 59
def prefixEnd_830588 : Nat := 4983230072969 + 3 ^ 40 * 830588 * 2
def baseEnd_830588 : Nat := 426490869856701554330201

theorem tailTrace_830588 : CollatzResearch.WordTrace tailWord_830588 prefixEnd_830588 426490869856701554330201 := by
  unfold tailWord_830588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147016557464501991002209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20196022076619335988002945 15147016557464501991002209)
  ·
    refine ⟨11360262418098376493251657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15147016557464501991002209 11360262418098376493251657)
    ·
      refine ⟨8520196813573782369938743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11360262418098376493251657 8520196813573782369938743)
      ·
        refine ⟨12780295220360673554908115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8520196813573782369938743 12780295220360673554908115)
        ·
          refine ⟨19170442830541010332362173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780295220360673554908115 19170442830541010332362173)
          ·
            refine ⟨7188916061452878874635815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19170442830541010332362173 7188916061452878874635815)
            ·
              refine ⟨10783374092179318311953723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188916061452878874635815 10783374092179318311953723)
              ·
                refine ⟨16175061138268977467930585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10783374092179318311953723 16175061138268977467930585)
                ·
                  refine ⟨12131295853701733100947939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16175061138268977467930585 12131295853701733100947939)
                  ·
                    refine ⟨18196943780552599651421909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12131295853701733100947939 18196943780552599651421909)
                    ·
                      refine ⟨426490869856701554330201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18196943780552599651421909 426490869856701554330201)
                      ·
                        rfl

theorem cell23_830588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_830588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830588 prefixEnd_830588 := by exact prefixLift 830588
  have htrace : WordTrace (prefixWord ++ tailWord_830588) baseStart_830588 baseEnd_830588 := by
    simpa [prefixWord, tailWord_830588, baseEnd_830588] using wordTrace_append hprefix tailTrace_830588
  have hstable : (prefixWord ++ tailWord_830588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830588).length < 2 ^ (prefixWord ++ tailWord_830588).sum := by decide
  have hdescent : baseEnd_830588 < baseStart_830588 := by decide
  rcases family_descends (prefixWord ++ tailWord_830588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830595 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 1, 5]
def baseStart_830595 : Nat := 118140960795 + 830595 * 2 ^ 59
def prefixEnd_830595 : Nat := 4983230072969 + 3 ^ 40 * 830595 * 2
def baseEnd_830595 : Nat := 142164821407094342314223

theorem tailTrace_830595 : CollatzResearch.WordTrace tailWord_830595 prefixEnd_830595 142164821407094342314223 := by
  unfold tailWord_830595
  simp only [CollatzResearch.WordTrace]
  refine ⟨30294288425903644177509239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20196192283935762785006159 30294288425903644177509239)
  ·
    refine ⟨45441432638855466266263859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30294288425903644177509239 45441432638855466266263859)
    ·
      refine ⟨68162148958283199399395789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45441432638855466266263859 68162148958283199399395789)
      ·
        refine ⟨25560805859356199774773421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68162148958283199399395789 25560805859356199774773421)
        ·
          refine ⟨9585302197258574915540033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25560805859356199774773421 9585302197258574915540033)
          ·
            refine ⟨7188976647943931186655025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9585302197258574915540033 7188976647943931186655025)
            ·
              refine ⟨5391732485957948389991269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188976647943931186655025 5391732485957948389991269)
              ·
                refine ⟨1010949841117115323123363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5391732485957948389991269 1010949841117115323123363)
                ·
                  refine ⟨1516424761675672984685045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010949841117115323123363 1516424761675672984685045)
                  ·
                    refine ⟨142164821407094342314223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1516424761675672984685045 142164821407094342314223)
                    ·
                      rfl

theorem cell23_830595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 5].length) (baseStart_830595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830595 prefixEnd_830595 := by exact prefixLift 830595
  have htrace : WordTrace (prefixWord ++ tailWord_830595) baseStart_830595 baseEnd_830595 := by
    simpa [prefixWord, tailWord_830595, baseEnd_830595] using wordTrace_append hprefix tailTrace_830595
  have hstable : (prefixWord ++ tailWord_830595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830595).length < 2 ^ (prefixWord ++ tailWord_830595).sum := by decide
  have hdescent : baseEnd_830595 < baseStart_830595 := by decide
  rcases family_descends (prefixWord ++ tailWord_830595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830602 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_830602 : Nat := 118140960795 + 830602 * 2 ^ 59
def prefixEnd_830602 : Nat := 4983230072969 + 3 ^ 40 * 830602 * 2
def baseEnd_830602 : Nat := 426498058585864499555137

theorem tailTrace_830602 : CollatzResearch.WordTrace tailWord_830602 prefixEnd_830602 426498058585864499555137 := by
  unfold tailWord_830602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7573635934219571093253515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20196362491252189582009373 7573635934219571093253515)
  ·
    refine ⟨11360453901329356639880273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7573635934219571093253515 11360453901329356639880273)
    ·
      refine ⟨8520340425997017479910205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11360453901329356639880273 8520340425997017479910205)
      ·
        refine ⟨3195127659748881554966327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8520340425997017479910205 3195127659748881554966327)
        ·
          refine ⟨4792691489623322332449491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195127659748881554966327 4792691489623322332449491)
          ·
            refine ⟨7189037234434983498674237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792691489623322332449491 7189037234434983498674237)
            ·
              refine ⟨2695888962913118812002839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7189037234434983498674237 2695888962913118812002839)
              ·
                refine ⟨4043833444369678218004259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695888962913118812002839 4043833444369678218004259)
                ·
                  refine ⟨6065750166554517327006389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043833444369678218004259 6065750166554517327006389)
                  ·
                    refine ⟨568664078114485999406849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6065750166554517327006389 568664078114485999406849)
                    ·
                      refine ⟨426498058585864499555137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568664078114485999406849 426498058585864499555137)
                      ·
                        rfl

theorem cell23_830602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_830602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830602 prefixEnd_830602 := by exact prefixLift 830602
  have htrace : WordTrace (prefixWord ++ tailWord_830602) baseStart_830602 baseEnd_830602 := by
    simpa [prefixWord, tailWord_830602, baseEnd_830602] using wordTrace_append hprefix tailTrace_830602
  have hstable : (prefixWord ++ tailWord_830602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830602).length < 2 ^ (prefixWord ++ tailWord_830602).sum := by decide
  have hdescent : baseEnd_830602 < baseStart_830602 := by decide
  rcases family_descends (prefixWord ++ tailWord_830602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830608 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_830608 : Nat := 118140960795 + 830608 * 2 ^ 59
def prefixEnd_830608 : Nat := 4983230072969 + 3 ^ 40 * 830608 * 2
def baseEnd_830608 : Nat := 142167046489930492026703

theorem tailTrace_830608 : CollatzResearch.WordTrace tailWord_830608 prefixEnd_830608 142167046489930492026703 := by
  unfold tailWord_830608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147381287428273698866239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20196508383237698265154985 15147381287428273698866239)
  ·
    refine ⟨22721071931142410548299359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15147381287428273698866239 22721071931142410548299359)
    ·
      refine ⟨34081607896713615822449039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22721071931142410548299359 34081607896713615822449039)
      ·
        refine ⟨51122411845070423733673559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34081607896713615822449039 51122411845070423733673559)
        ·
          refine ⟨76683617767605635600510339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51122411845070423733673559 76683617767605635600510339)
          ·
            refine ⟨115025426651408453400765509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76683617767605635600510339 115025426651408453400765509)
            ·
              refine ⟨21567267497139085012643533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115025426651408453400765509 21567267497139085012643533)
              ·
                refine ⟨8087725311427156879741325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21567267497139085012643533 8087725311427156879741325)
                ·
                  refine ⟨3032896991785183829902997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8087725311427156879741325 3032896991785183829902997)
                  ·
                    refine ⟨142167046489930492026703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3032896991785183829902997 142167046489930492026703)
                    ·
                      rfl

theorem cell23_830608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_830608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830608 prefixEnd_830608 := by exact prefixLift 830608
  have htrace : WordTrace (prefixWord ++ tailWord_830608) baseStart_830608 baseEnd_830608 := by
    simpa [prefixWord, tailWord_830608, baseEnd_830608] using wordTrace_append hprefix tailTrace_830608
  have hstable : (prefixWord ++ tailWord_830608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830608).length < 2 ^ (prefixWord ++ tailWord_830608).sum := by decide
  have hdescent : baseEnd_830608 < baseStart_830608 := by decide
  rcases family_descends (prefixWord ++ tailWord_830608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830626 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_830626 : Nat := 118140960795 + 830626 * 2 ^ 59
def prefixEnd_830626 : Nat := 4983230072969 + 3 ^ 40 * 830626 * 2
def baseEnd_830626 : Nat := 426510382121572405655027

theorem tailTrace_830626 : CollatzResearch.WordTrace tailWord_830626 prefixEnd_830626 426510382121572405655027 := by
  unfold tailWord_830626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7573854772197834117971933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20196946059194224314591821 7573854772197834117971933)
  ·
    refine ⟨2840195539574187794239475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7573854772197834117971933 2840195539574187794239475)
    ·
      refine ⟨4260293309361281691359213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840195539574187794239475 4260293309361281691359213)
      ·
        refine ⟨1597609991010480634259705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4260293309361281691359213 1597609991010480634259705)
        ·
          refine ⟨1198207493257860475694779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597609991010480634259705 1198207493257860475694779)
          ·
            refine ⟨1797311239886790713542169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198207493257860475694779 1797311239886790713542169)
            ·
              refine ⟨1347983429915093035156627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797311239886790713542169 1347983429915093035156627)
              ·
                refine ⟨2021975144872639552734941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347983429915093035156627 2021975144872639552734941)
                ·
                  refine ⟨758240679327239832275603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2021975144872639552734941 758240679327239832275603)
                  ·
                    refine ⟨1137361018990859748413405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 758240679327239832275603 1137361018990859748413405)
                    ·
                      refine ⟨426510382121572405655027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137361018990859748413405 426510382121572405655027)
                      ·
                        rfl

theorem cell23_830626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_830626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830626 prefixEnd_830626 := by exact prefixLift 830626
  have htrace : WordTrace (prefixWord ++ tailWord_830626) baseStart_830626 baseEnd_830626 := by
    simpa [prefixWord, tailWord_830626, baseEnd_830626] using wordTrace_append hprefix tailTrace_830626
  have hstable : (prefixWord ++ tailWord_830626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830626).length < 2 ^ (prefixWord ++ tailWord_830626).sum := by decide
  have hdescent : baseEnd_830626 < baseStart_830626 := by decide
  rcases family_descends (prefixWord ++ tailWord_830626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830642 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_830642 : Nat := 118140960795 + 830642 * 2 ^ 59
def prefixEnd_830642 : Nat := 4983230072969 + 3 ^ 40 * 830642 * 2
def baseEnd_830642 : Nat := 142172865937348114351651

theorem tailTrace_830642 : CollatzResearch.WordTrace tailWord_830642 prefixEnd_830642 142172865937348114351651 := by
  unfold tailWord_830642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574000664183342801117545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20197335104488914136313453 7574000664183342801117545)
  ·
    refine ⟨5680500498137507100838159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7574000664183342801117545 5680500498137507100838159)
    ·
      refine ⟨8520750747206260651257239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5680500498137507100838159 8520750747206260651257239)
      ·
        refine ⟨12781126120809390976885859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8520750747206260651257239 12781126120809390976885859)
        ·
          refine ⟨19171689181214086465328789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12781126120809390976885859 19171689181214086465328789)
          ·
            refine ⟨898672930369410303062287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19171689181214086465328789 898672930369410303062287)
            ·
              refine ⟨1348009395554115454593431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898672930369410303062287 1348009395554115454593431)
              ·
                refine ⟨2022014093331173181890147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348009395554115454593431 2022014093331173181890147)
                ·
                  refine ⟨3033021139996759772835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022014093331173181890147 3033021139996759772835221)
                  ·
                    refine ⟨142172865937348114351651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3033021139996759772835221 142172865937348114351651)
                    ·
                      rfl

theorem cell23_830642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_830642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830642 prefixEnd_830642 := by exact prefixLift 830642
  have htrace : WordTrace (prefixWord ++ tailWord_830642) baseStart_830642 baseEnd_830642 := by
    simpa [prefixWord, tailWord_830642, baseEnd_830642] using wordTrace_append hprefix tailTrace_830642
  have hstable : (prefixWord ++ tailWord_830642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830642).length < 2 ^ (prefixWord ++ tailWord_830642).sum := by decide
  have hdescent : baseEnd_830642 < baseStart_830642 := by decide
  rcases family_descends (prefixWord ++ tailWord_830642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830649 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 3, 2, 2]
def baseStart_830649 : Nat := 118140960795 + 830649 * 2 ^ 59
def prefixEnd_830649 : Nat := 4983230072969 + 3 ^ 40 * 830649 * 2
def baseEnd_830649 : Nat := 426522192176625815667421

theorem tailTrace_830649 : CollatzResearch.WordTrace tailWord_830649 prefixEnd_830649 426522192176625815667421 := by
  unfold tailWord_830649
  simp only [CollatzResearch.WordTrace]
  refine ⟨30296257967708011399975001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20197505311805340933316667 30296257967708011399975001)
  ·
    refine ⟨22722193475781008549981251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30296257967708011399975001 22722193475781008549981251)
    ·
      refine ⟨34083290213671512824971877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22722193475781008549981251 34083290213671512824971877)
      ·
        refine ⟨6390616915063408654682227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34083290213671512824971877 6390616915063408654682227)
        ·
          refine ⟨9585925372595112982023341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6390616915063408654682227 9585925372595112982023341)
          ·
            refine ⟨3594722014723167368258753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9585925372595112982023341 3594722014723167368258753)
            ·
              refine ⟨2696041511042375526194065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594722014723167368258753 2696041511042375526194065)
              ·
                refine ⟨2022031133281781644645549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696041511042375526194065 2022031133281781644645549)
                ·
                  refine ⟨758261674980668116742081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2022031133281781644645549 758261674980668116742081)
                  ·
                    refine ⟨568696256235501087556561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 758261674980668116742081 568696256235501087556561)
                    ·
                      refine ⟨426522192176625815667421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568696256235501087556561 426522192176625815667421)
                      ·
                        rfl

theorem cell23_830649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_830649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830649 prefixEnd_830649 := by exact prefixLift 830649
  have htrace : WordTrace (prefixWord ++ tailWord_830649) baseStart_830649 baseEnd_830649 := by
    simpa [prefixWord, tailWord_830649, baseEnd_830649] using wordTrace_append hprefix tailTrace_830649
  have hstable : (prefixWord ++ tailWord_830649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830649).length < 2 ^ (prefixWord ++ tailWord_830649).sum := by decide
  have hdescent : baseEnd_830649 < baseStart_830649 := by decide
  rcases family_descends (prefixWord ++ tailWord_830649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830655 : List Nat := [1, 1, 2, 2, 2, 2, 6, 7]
def baseStart_830655 : Nat := 118140960795 + 830655 * 2 ^ 59
def prefixEnd_830655 : Nat := 4983230072969 + 3 ^ 40 * 830655 * 2
def baseEnd_830655 : Nat := 15797232335576029340459

theorem tailTrace_830655 : CollatzResearch.WordTrace tailWord_830655 prefixEnd_830655 15797232335576029340459 := by
  unfold tailWord_830655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30296476805686274424693419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20197651203790849616462279 30296476805686274424693419)
  ·
    refine ⟨45444715208529411637040129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30296476805686274424693419 45444715208529411637040129)
    ·
      refine ⟨34083536406397058727780097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45444715208529411637040129 34083536406397058727780097)
      ·
        refine ⟨25562652304797794045835073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34083536406397058727780097 25562652304797794045835073)
        ·
          refine ⟨19171989228598345534376305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25562652304797794045835073 19171989228598345534376305)
          ·
            refine ⟨14378991921448759150782229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19171989228598345534376305 14378991921448759150782229)
            ·
              refine ⟨674015246317910585192917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14378991921448759150782229 674015246317910585192917)
              ·
                refine ⟨15797232335576029340459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 674015246317910585192917 15797232335576029340459)
                ·
                  rfl

theorem cell23_830655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 7].length) (baseStart_830655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830655 prefixEnd_830655 := by exact prefixLift 830655
  have htrace : WordTrace (prefixWord ++ tailWord_830655) baseStart_830655 baseEnd_830655 := by
    simpa [prefixWord, tailWord_830655, baseEnd_830655] using wordTrace_append hprefix tailTrace_830655
  have hstable : (prefixWord ++ tailWord_830655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830655).length < 2 ^ (prefixWord ++ tailWord_830655).sum := by decide
  have hdescent : baseEnd_830655 < baseStart_830655 := by decide
  rcases family_descends (prefixWord ++ tailWord_830655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830660 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_830660 : Nat := 118140960795 + 830660 * 2 ^ 59
def prefixEnd_830660 : Nat := 4983230072969 + 3 ^ 40 * 830660 * 2
def baseEnd_830660 : Nat := 426527840463825272629871

theorem tailTrace_830660 : CollatzResearch.WordTrace tailWord_830660 prefixEnd_830660 426527840463825272629871 := by
  unfold tailWord_830660
  simp only [CollatzResearch.WordTrace]
  refine ⟨15148329585334080139312717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20197772780445440185750289 15148329585334080139312717)
  ·
    refine ⟨5680623594500280052242269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15148329585334080139312717 5680623594500280052242269)
    ·
      refine ⟨2130233847937605019590851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5680623594500280052242269 2130233847937605019590851)
      ·
        refine ⟨3195350771906407529386277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130233847937605019590851 3195350771906407529386277)
        ·
          refine ⟨599128269732451411759927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3195350771906407529386277 599128269732451411759927)
          ·
            refine ⟨898692404598677117639891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599128269732451411759927 898692404598677117639891)
            ·
              refine ⟨1348038606898015676459837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898692404598677117639891 1348038606898015676459837)
              ·
                refine ⟨505514477586755878672439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348038606898015676459837 505514477586755878672439)
                ·
                  refine ⟨758271716380133818008659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505514477586755878672439 758271716380133818008659)
                  ·
                    refine ⟨1137407574570200727012989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 758271716380133818008659 1137407574570200727012989)
                    ·
                      refine ⟨426527840463825272629871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137407574570200727012989 426527840463825272629871)
                      ·
                        rfl

theorem cell23_830660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_830660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830660 prefixEnd_830660 := by exact prefixLift 830660
  have htrace : WordTrace (prefixWord ++ tailWord_830660) baseStart_830660 baseEnd_830660 := by
    simpa [prefixWord, tailWord_830660, baseEnd_830660] using wordTrace_append hprefix tailTrace_830660
  have hstable : (prefixWord ++ tailWord_830660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830660).length < 2 ^ (prefixWord ++ tailWord_830660).sum := by decide
  have hdescent : baseEnd_830660 < baseStart_830660 := by decide
  rcases family_descends (prefixWord ++ tailWord_830660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830693 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_830693 : Nat := 118140960795 + 830693 * 2 ^ 59
def prefixEnd_830693 : Nat := 4983230072969 + 3 ^ 40 * 830693 * 2
def baseEnd_830693 : Nat := 142181595108474547839073

theorem tailTrace_830693 : CollatzResearch.WordTrace tailWord_830693 prefixEnd_830693 142181595108474547839073 := by
  unfold tailWord_830693
  simp only [CollatzResearch.WordTrace]
  refine ⟨30297862779548606914576733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20198575186365737943051155 30297862779548606914576733)
  ·
    refine ⟨11361698542330727592966275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30297862779548606914576733 11361698542330727592966275)
    ·
      refine ⟨17042547813496091389449413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361698542330727592966275 17042547813496091389449413)
      ·
        refine ⟨3195477715030517135521765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17042547813496091389449413 3195477715030517135521765)
        ·
          refine ⟨599152071568221962910331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3195477715030517135521765 599152071568221962910331)
          ·
            refine ⟨898728107352332944365497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599152071568221962910331 898728107352332944365497)
            ·
              refine ⟨674046080514249708274123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898728107352332944365497 674046080514249708274123)
              ·
                refine ⟨1011069120771374562411185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674046080514249708274123 1011069120771374562411185)
                ·
                  refine ⟨758301840578530921808389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011069120771374562411185 758301840578530921808389)
                  ·
                    refine ⟨142181595108474547839073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758301840578530921808389 142181595108474547839073)
                    ·
                      rfl

theorem cell23_830693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_830693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830693 prefixEnd_830693 := by exact prefixLift 830693
  have htrace : WordTrace (prefixWord ++ tailWord_830693) baseStart_830693 baseEnd_830693 := by
    simpa [prefixWord, tailWord_830693, baseEnd_830693] using wordTrace_append hprefix tailTrace_830693
  have hstable : (prefixWord ++ tailWord_830693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830693).length < 2 ^ (prefixWord ++ tailWord_830693).sum := by decide
  have hdescent : baseEnd_830693 < baseStart_830693 := by decide
  rcases family_descends (prefixWord ++ tailWord_830693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830699 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 3]
def baseStart_830699 : Nat := 118140960795 + 830699 * 2 ^ 59
def prefixEnd_830699 : Nat := 4983230072969 + 3 ^ 40 * 830699 * 2
def baseEnd_830699 : Nat := 426547866209350620042191

theorem tailTrace_830699 : CollatzResearch.WordTrace tailWord_830699 prefixEnd_830699 426547866209350620042191 := by
  unfold tailWord_830699
  simp only [CollatzResearch.WordTrace]
  refine ⟨30298081617526869939295151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20198721078351246626196767 30298081617526869939295151)
  ·
    refine ⟨45447122426290304908942727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30298081617526869939295151 45447122426290304908942727)
    ·
      refine ⟨68170683639435457363414091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45447122426290304908942727 68170683639435457363414091)
      ·
        refine ⟨102256025459153186045121137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68170683639435457363414091 102256025459153186045121137)
        ·
          refine ⟨76692019094364889533840853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102256025459153186045121137 76692019094364889533840853)
          ·
            refine ⟨1797469197524177098449395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 76692019094364889533840853 1797469197524177098449395)
            ·
              refine ⟨2696203796286265647674093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797469197524177098449395 2696203796286265647674093)
              ·
                refine ⟨1011076423607349617877785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2696203796286265647674093 1011076423607349617877785)
                ·
                  refine ⟨758307317705512213408339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011076423607349617877785 758307317705512213408339)
                  ·
                    refine ⟨1137460976558268320112509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 758307317705512213408339 1137460976558268320112509)
                    ·
                      refine ⟨426547866209350620042191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137460976558268320112509 426547866209350620042191)
                      ·
                        rfl

theorem cell23_830699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 3].length) (baseStart_830699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830699 prefixEnd_830699 := by exact prefixLift 830699
  have htrace : WordTrace (prefixWord ++ tailWord_830699) baseStart_830699 baseEnd_830699 := by
    simpa [prefixWord, tailWord_830699, baseEnd_830699] using wordTrace_append hprefix tailTrace_830699
  have hstable : (prefixWord ++ tailWord_830699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830699).length < 2 ^ (prefixWord ++ tailWord_830699).sum := by decide
  have hdescent : baseEnd_830699 < baseStart_830699 := by decide
  rcases family_descends (prefixWord ++ tailWord_830699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830725 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_830725 : Nat := 118140960795 + 830725 * 2 ^ 59
def prefixEnd_830725 : Nat := 4983230072969 + 3 ^ 40 * 830725 * 2
def baseEnd_830725 : Nat := 426561216706367518317071

theorem tailTrace_830725 : CollatzResearch.WordTrace tailWord_830725 prefixEnd_830725 426561216706367518317071 := by
  unfold tailWord_830725
  simp only [CollatzResearch.WordTrace]
  refine ⟨30299029915432676379741629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20199353276955117586494419 30299029915432676379741629)
  ·
    refine ⟨11362136218287253642403111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30299029915432676379741629 11362136218287253642403111)
    ·
      refine ⟨17043204327430880463604667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11362136218287253642403111 17043204327430880463604667)
      ·
        refine ⟨25564806491146320695407001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17043204327430880463604667 25564806491146320695407001)
        ·
          refine ⟨19173604868359740521555251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25564806491146320695407001 19173604868359740521555251)
          ·
            refine ⟨28760407302539610782332877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19173604868359740521555251 28760407302539610782332877)
            ·
              refine ⟨10785152738452354043374829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28760407302539610782332877 10785152738452354043374829)
              ·
                refine ⟨4044432276919632766265561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10785152738452354043374829 4044432276919632766265561)
                ·
                  refine ⟨3033324207689724574699171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044432276919632766265561 3033324207689724574699171)
                  ·
                    refine ⟨4549986311534586862048757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3033324207689724574699171 4549986311534586862048757)
                    ·
                      refine ⟨426561216706367518317071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4549986311534586862048757 426561216706367518317071)
                      ·
                        rfl

theorem cell23_830725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_830725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830725 prefixEnd_830725 := by exact prefixLift 830725
  have htrace : WordTrace (prefixWord ++ tailWord_830725) baseStart_830725 baseEnd_830725 := by
    simpa [prefixWord, tailWord_830725, baseEnd_830725] using wordTrace_append hprefix tailTrace_830725
  have hstable : (prefixWord ++ tailWord_830725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830725).length < 2 ^ (prefixWord ++ tailWord_830725).sum := by decide
  have hdescent : baseEnd_830725 < baseStart_830725 := by decide
  rcases family_descends (prefixWord ++ tailWord_830725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830756 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_830756 : Nat := 118140960795 + 830756 * 2 ^ 59
def prefixEnd_830756 : Nat := 4983230072969 + 3 ^ 40 * 830756 * 2
def baseEnd_830756 : Nat := 426577134606656897029429

theorem tailTrace_830756 : CollatzResearch.WordTrace tailWord_830756 prefixEnd_830756 426577134606656897029429 := by
  unfold tailWord_830756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15150080289160184337060061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20200107052213579116080081 15150080289160184337060061)
  ·
    refine ⟨5681280108435069126397523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15150080289160184337060061 5681280108435069126397523)
    ·
      refine ⟨8521920162652603689596285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5681280108435069126397523 8521920162652603689596285)
      ·
        refine ⟨3195720060994726383598607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8521920162652603689596285 3195720060994726383598607)
        ·
          refine ⟨4793580091492089575397911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195720060994726383598607 4793580091492089575397911)
          ·
            refine ⟨7190370137238134363096867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793580091492089575397911 7190370137238134363096867)
            ·
              refine ⟨10785555205857201544645301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190370137238134363096867 10785555205857201544645301)
              ·
                refine ⟨1011145800549112644810497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10785555205857201544645301 1011145800549112644810497)
                ·
                  refine ⟨758359350411834483607873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011145800549112644810497 758359350411834483607873)
                  ·
                    refine ⟨568769512808875862705905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 758359350411834483607873 568769512808875862705905)
                    ·
                      refine ⟨426577134606656897029429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568769512808875862705905 426577134606656897029429)
                      ·
                        rfl

theorem cell23_830756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_830756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830756 prefixEnd_830756 := by exact prefixLift 830756
  have htrace : WordTrace (prefixWord ++ tailWord_830756) baseStart_830756 baseEnd_830756 := by
    simpa [prefixWord, tailWord_830756, baseEnd_830756] using wordTrace_append hprefix tailTrace_830756
  have hstable : (prefixWord ++ tailWord_830756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830756).length < 2 ^ (prefixWord ++ tailWord_830756).sum := by decide
  have hdescent : baseEnd_830756 < baseStart_830756 := by decide
  rcases family_descends (prefixWord ++ tailWord_830756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830762 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_830762 : Nat := 118140960795 + 830762 * 2 ^ 59
def prefixEnd_830762 : Nat := 4983230072969 + 3 ^ 40 * 830762 * 2
def baseEnd_830762 : Nat := 47397801721175985950489

theorem tailTrace_830762 : CollatzResearch.WordTrace tailWord_830762 prefixEnd_830762 47397801721175985950489 := by
  unfold tailWord_830762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575094854074657924709635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20200252944199087799225693 7575094854074657924709635)
  ·
    refine ⟨11362642281111986887064453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7575094854074657924709635 11362642281111986887064453)
    ·
      refine ⟨2130495427708497541324585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11362642281111986887064453 2130495427708497541324585)
      ·
        refine ⟨1597871570781373155993439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2130495427708497541324585 1597871570781373155993439)
        ·
          refine ⟨2396807356172059733990159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597871570781373155993439 2396807356172059733990159)
          ·
            refine ⟨3595211034258089600985239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396807356172059733990159 3595211034258089600985239)
            ·
              refine ⟨5392816551387134401477859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595211034258089600985239 5392816551387134401477859)
              ·
                refine ⟨8089224827080701602216789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392816551387134401477859 8089224827080701602216789)
                ·
                  refine ⟨47397801721175985950489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8089224827080701602216789 47397801721175985950489)
                  ·
                    rfl

theorem cell23_830762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_830762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830762 prefixEnd_830762 := by exact prefixLift 830762
  have htrace : WordTrace (prefixWord ++ tailWord_830762) baseStart_830762 baseEnd_830762 := by
    simpa [prefixWord, tailWord_830762, baseEnd_830762] using wordTrace_append hprefix tailTrace_830762
  have hstable : (prefixWord ++ tailWord_830762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830762).length < 2 ^ (prefixWord ++ tailWord_830762).sum := by decide
  have hdescent : baseEnd_830762 < baseStart_830762 := by decide
  rcases family_descends (prefixWord ++ tailWord_830762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830825 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_830825 : Nat := 118140960795 + 830825 * 2 ^ 59
def prefixEnd_830825 : Nat := 4983230072969 + 3 ^ 40 * 830825 * 2
def baseEnd_830825 : Nat := 426612564771817127066611

theorem tailTrace_830825 : CollatzResearch.WordTrace tailWord_830825 prefixEnd_830825 426612564771817127066611 := by
  unfold tailWord_830825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30302677215070393458381929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20201784810046928972254619 30302677215070393458381929)
  ·
    refine ⟨22727007911302795093786447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30302677215070393458381929 22727007911302795093786447)
    ·
      refine ⟨34090511866954192640679671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22727007911302795093786447 34090511866954192640679671)
      ·
        refine ⟨51135767800431288961019507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34090511866954192640679671 51135767800431288961019507)
        ·
          refine ⟨76703651700646933441529261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51135767800431288961019507 76703651700646933441529261)
          ·
            refine ⟨28763869387742600040573473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76703651700646933441529261 28763869387742600040573473)
            ·
              refine ⟨21572902040806950030430105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28763869387742600040573473 21572902040806950030430105)
              ·
                refine ⟨16179676530605212522822579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21572902040806950030430105 16179676530605212522822579)
                ·
                  refine ⟨24269514795907818784233869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16179676530605212522822579 24269514795907818784233869)
                  ·
                    refine ⟨9101068048465432044087701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24269514795907818784233869 9101068048465432044087701)
                    ·
                      refine ⟨426612564771817127066611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9101068048465432044087701 426612564771817127066611)
                      ·
                        rfl

theorem cell23_830825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_830825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830825 prefixEnd_830825 := by exact prefixLift 830825
  have htrace : WordTrace (prefixWord ++ tailWord_830825) baseStart_830825 baseEnd_830825 := by
    simpa [prefixWord, tailWord_830825, baseEnd_830825] using wordTrace_append hprefix tailTrace_830825
  have hstable : (prefixWord ++ tailWord_830825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830825).length < 2 ^ (prefixWord ++ tailWord_830825).sum := by decide
  have hdescent : baseEnd_830825 < baseStart_830825 := by decide
  rcases family_descends (prefixWord ++ tailWord_830825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830830 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_830830 : Nat := 118140960795 + 830830 * 2 ^ 59
def prefixEnd_830830 : Nat := 4983230072969 + 3 ^ 40 * 830830 * 2
def baseEnd_830830 : Nat := 47401681352787734167121

theorem tailTrace_830830 : CollatzResearch.WordTrace tailWord_830830 prefixEnd_830830 47401681352787734167121 := by
  unfold tailWord_830830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787857447506534914039243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20201906386701519541542629 3787857447506534914039243)
  ·
    refine ⟨5681786171259802371058865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787857447506534914039243 5681786171259802371058865)
    ·
      refine ⟨4261339628444851778294149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5681786171259802371058865 4261339628444851778294149)
      ·
        refine ⟨799001180333409708430153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4261339628444851778294149 799001180333409708430153)
        ·
          refine ⟨599250885250057281322615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799001180333409708430153 599250885250057281322615)
          ·
            refine ⟨898876327875085921983923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599250885250057281322615 898876327875085921983923)
            ·
              refine ⟨1348314491812628882975885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898876327875085921983923 1348314491812628882975885)
              ·
                refine ⟨505617934429735831115957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348314491812628882975885 505617934429735831115957)
                ·
                  refine ⟨47401681352787734167121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 505617934429735831115957 47401681352787734167121)
                  ·
                    rfl

theorem cell23_830830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_830830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830830 prefixEnd_830830 := by exact prefixLift 830830
  have htrace : WordTrace (prefixWord ++ tailWord_830830) baseStart_830830 baseEnd_830830 := by
    simpa [prefixWord, tailWord_830830, baseEnd_830830] using wordTrace_append hprefix tailTrace_830830
  have hstable : (prefixWord ++ tailWord_830830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830830).length < 2 ^ (prefixWord ++ tailWord_830830).sum := by decide
  have hdescent : baseEnd_830830 < baseStart_830830 := by decide
  rcases family_descends (prefixWord ++ tailWord_830830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830832 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_830832 : Nat := 118140960795 + 830832 * 2 ^ 59
def prefixEnd_830832 : Nat := 4983230072969 + 3 ^ 40 * 830832 * 2
def baseEnd_830832 : Nat := 426616159136398599679079

theorem tailTrace_830832 : CollatzResearch.WordTrace tailWord_830832 prefixEnd_830832 426616159136398599679079 := by
  unfold tailWord_830832
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151466263022516826943375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20201955017363355769257833 15151466263022516826943375)
  ·
    refine ⟨22727199394533775240415063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15151466263022516826943375 22727199394533775240415063)
    ·
      refine ⟨34090799091800662860622595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22727199394533775240415063 34090799091800662860622595)
      ·
        refine ⟨51136198637700994290933893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34090799091800662860622595 51136198637700994290933893)
        ·
          refine ⟨9588037244568936429550105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51136198637700994290933893 9588037244568936429550105)
          ·
            refine ⟨7191027933426702322162579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9588037244568936429550105 7191027933426702322162579)
            ·
              refine ⟨10786541900140053483243869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191027933426702322162579 10786541900140053483243869)
              ·
                refine ⟨4044953212552520056216451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10786541900140053483243869 4044953212552520056216451)
                ·
                  refine ⟨6067429818828780084324677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044953212552520056216451 6067429818828780084324677)
                  ·
                    refine ⟨1137643091030396265810877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6067429818828780084324677 1137643091030396265810877)
                    ·
                      refine ⟨426616159136398599679079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137643091030396265810877 426616159136398599679079)
                      ·
                        rfl

theorem cell23_830832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_830832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830832 prefixEnd_830832 := by exact prefixLift 830832
  have htrace : WordTrace (prefixWord ++ tailWord_830832) baseStart_830832 baseEnd_830832 := by
    simpa [prefixWord, tailWord_830832, baseEnd_830832] using wordTrace_append hprefix tailTrace_830832
  have hstable : (prefixWord ++ tailWord_830832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830832).length < 2 ^ (prefixWord ++ tailWord_830832).sum := by decide
  have hdescent : baseEnd_830832 < baseStart_830832 := by decide
  rcases family_descends (prefixWord ++ tailWord_830832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830852 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 8]
def baseStart_830852 : Nat := 118140960795 + 830852 * 2 ^ 59
def prefixEnd_830852 : Nat := 4983230072969 + 3 ^ 40 * 830852 * 2
def baseEnd_830852 : Nat := 47402936527720946825443

theorem tailTrace_830852 : CollatzResearch.WordTrace tailWord_830852 prefixEnd_830852 47402936527720946825443 := by
  unfold tailWord_830852
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151830992986288534807405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20202441323981718046409873 15151830992986288534807405)
  ·
    refine ⟨5681936622369858200552777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15151830992986288534807405 5681936622369858200552777)
    ·
      refine ⟨4261452466777393650414583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5681936622369858200552777 4261452466777393650414583)
      ·
        refine ⟨6392178700166090475621875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261452466777393650414583 6392178700166090475621875)
        ·
          refine ⟨9588268050249135713432813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6392178700166090475621875 9588268050249135713432813)
          ·
            refine ⟨3595600518843425892537305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9588268050249135713432813 3595600518843425892537305)
            ·
              refine ⟨2696700389132569419402979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3595600518843425892537305 2696700389132569419402979)
              ·
                refine ⟨4045050583698854129104469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696700389132569419402979 4045050583698854129104469)
                ·
                  refine ⟨47402936527720946825443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4045050583698854129104469 47402936527720946825443)
                  ·
                    rfl

theorem cell23_830852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_830852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830852 prefixEnd_830852 := by exact prefixLift 830852
  have htrace : WordTrace (prefixWord ++ tailWord_830852) baseStart_830852 baseEnd_830852 := by
    simpa [prefixWord, tailWord_830852, baseEnd_830852] using wordTrace_append hprefix tailTrace_830852
  have hstable : (prefixWord ++ tailWord_830852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830852).length < 2 ^ (prefixWord ++ tailWord_830852).sum := by decide
  have hdescent : baseEnd_830852 < baseStart_830852 := by decide
  rcases family_descends (prefixWord ++ tailWord_830852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830856 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 3, 4]
def baseStart_830856 : Nat := 118140960795 + 830856 * 2 ^ 59
def prefixEnd_830856 : Nat := 4983230072969 + 3 ^ 40 * 830856 * 2
def baseEnd_830856 : Nat := 142209494224035501926323

theorem tailTrace_830856 : CollatzResearch.WordTrace tailWord_830856 prefixEnd_830856 142209494224035501926323 := by
  unfold tailWord_830856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151903938979042876380211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20202538585305390501840281 15151903938979042876380211)
  ·
    refine ⟨22727855908468564314570317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15151903938979042876380211 22727855908468564314570317)
    ·
      refine ⟨8522945965675711617963869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22727855908468564314570317 8522945965675711617963869)
      ·
        refine ⟨3196104737128391856736451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8522945965675711617963869 3196104737128391856736451)
        ·
          refine ⟨4794157105692587785104677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196104737128391856736451 4794157105692587785104677)
          ·
            refine ⟨898904457317360209707127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4794157105692587785104677 898904457317360209707127)
            ·
              refine ⟨1348356685976040314560691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898904457317360209707127 1348356685976040314560691)
              ·
                refine ⟨2022535028964060471841037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348356685976040314560691 2022535028964060471841037)
                ·
                  refine ⟨758450635861522676940389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2022535028964060471841037 758450635861522676940389)
                  ·
                    refine ⟨142209494224035501926323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758450635861522676940389 142209494224035501926323)
                    ·
                      rfl

theorem cell23_830856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_830856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830856 prefixEnd_830856 := by exact prefixLift 830856
  have htrace : WordTrace (prefixWord ++ tailWord_830856) baseStart_830856 baseEnd_830856 := by
    simpa [prefixWord, tailWord_830856, baseEnd_830856] using wordTrace_append hprefix tailTrace_830856
  have hstable : (prefixWord ++ tailWord_830856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830856).length < 2 ^ (prefixWord ++ tailWord_830856).sum := by decide
  have hdescent : baseEnd_830856 < baseStart_830856 := by decide
  rcases family_descends (prefixWord ++ tailWord_830856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830869 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 6]
def baseStart_830869 : Nat := 118140960795 + 830869 * 2 ^ 59
def prefixEnd_830869 : Nat := 4983230072969 + 3 ^ 40 * 830869 * 2
def baseEnd_830869 : Nat := 47403906435623883879601

theorem tailTrace_830869 : CollatzResearch.WordTrace tailWord_830869 prefixEnd_830869 47403906435623883879601 := by
  unfold tailWord_830869
  simp only [CollatzResearch.WordTrace]
  refine ⟨30304282026910988972983661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20202854684607325981989107 30304282026910988972983661)
  ·
    refine ⟨11364105760091620864868873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30304282026910988972983661 11364105760091620864868873)
    ·
      refine ⟨8523079320068715648651655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11364105760091620864868873 8523079320068715648651655)
      ·
        refine ⟨12784618980103073472977483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523079320068715648651655 12784618980103073472977483)
        ·
          refine ⟨19176928470154610209466225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784618980103073472977483 19176928470154610209466225)
          ·
            refine ⟨14382696352615957657099669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19176928470154610209466225 14382696352615957657099669)
            ·
              refine ⟨674188891528873015176547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14382696352615957657099669 674188891528873015176547)
              ·
                refine ⟨1011283337293309522764821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674188891528873015176547 1011283337293309522764821)
                ·
                  refine ⟨47403906435623883879601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1011283337293309522764821 47403906435623883879601)
                  ·
                    rfl

theorem cell23_830869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_830869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830869 prefixEnd_830869 := by exact prefixLift 830869
  have htrace : WordTrace (prefixWord ++ tailWord_830869) baseStart_830869 baseEnd_830869 := by
    simpa [prefixWord, tailWord_830869, baseEnd_830869] using wordTrace_append hprefix tailTrace_830869
  have hstable : (prefixWord ++ tailWord_830869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830869).length < 2 ^ (prefixWord ++ tailWord_830869).sum := by decide
  have hdescent : baseEnd_830869 < baseStart_830869 := by decide
  rcases family_descends (prefixWord ++ tailWord_830869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830936 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2]
def baseStart_830936 : Nat := 118140960795 + 830936 * 2 ^ 59
def prefixEnd_830936 : Nat := 4983230072969 + 3 ^ 40 * 830936 * 2
def baseEnd_830936 : Nat := 426669561124466192778601

theorem tailTrace_830936 : CollatzResearch.WordTrace tailWord_830936 prefixEnd_830936 426669561124466192778601 := by
  unfold tailWord_830936
  simp only [CollatzResearch.WordTrace]
  refine ⟨15153362858834129707836331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20204483811778839610448441 15153362858834129707836331)
  ·
    refine ⟨22730044288251194561754497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15153362858834129707836331 22730044288251194561754497)
    ·
      refine ⟨17047533216188395921315873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22730044288251194561754497 17047533216188395921315873)
      ·
        refine ⟨12785649912141296940986905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17047533216188395921315873 12785649912141296940986905)
        ·
          refine ⟨9589237434105972705740179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12785649912141296940986905 9589237434105972705740179)
          ·
            refine ⟨14383856151158959058610269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589237434105972705740179 14383856151158959058610269)
            ·
              refine ⟨5393946056684609646978851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14383856151158959058610269 5393946056684609646978851)
              ·
                refine ⟨8090919085026914470468277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393946056684609646978851 8090919085026914470468277)
                ·
                  refine ⟨758523664221273231606401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8090919085026914470468277 758523664221273231606401)
                  ·
                    refine ⟨568892748165954923704801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 758523664221273231606401 568892748165954923704801)
                    ·
                      refine ⟨426669561124466192778601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568892748165954923704801 426669561124466192778601)
                      ·
                        rfl

theorem cell23_830936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_830936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830936 prefixEnd_830936 := by exact prefixLift 830936
  have htrace : WordTrace (prefixWord ++ tailWord_830936) baseStart_830936 baseEnd_830936 := by
    simpa [prefixWord, tailWord_830936, baseEnd_830936] using wordTrace_append hprefix tailTrace_830936
  have hstable : (prefixWord ++ tailWord_830936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830936).length < 2 ^ (prefixWord ++ tailWord_830936).sum := by decide
  have hdescent : baseEnd_830936 < baseStart_830936 := by decide
  rcases family_descends (prefixWord ++ tailWord_830936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830972 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_830972 : Nat := 118140960795 + 830972 * 2 ^ 59
def prefixEnd_830972 : Nat := 4983230072969 + 3 ^ 40 * 830972 * 2
def baseEnd_830972 : Nat := 142229348809342683976145

theorem tailTrace_830972 : CollatzResearch.WordTrace tailWord_830972 prefixEnd_830972 142229348809342683976145 := by
  unfold tailWord_830972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15154019372768918781991585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20205359163691891709322113 15154019372768918781991585)
  ·
    refine ⟨11365514529576689086493689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15154019372768918781991585 11365514529576689086493689)
    ·
      refine ⟨8524135897182516814870267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11365514529576689086493689 8524135897182516814870267)
      ·
        refine ⟨12786203845773775222305401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524135897182516814870267 12786203845773775222305401)
        ·
          refine ⟨9589652884330331416729051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12786203845773775222305401 9589652884330331416729051)
          ·
            refine ⟨14384479326495497125093577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589652884330331416729051 14384479326495497125093577)
            ·
              refine ⟨10788359494871622843820183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14384479326495497125093577 10788359494871622843820183)
              ·
                refine ⟨16182539242307434265730275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788359494871622843820183 16182539242307434265730275)
                ·
                  refine ⟨24273808863461151398595413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16182539242307434265730275 24273808863461151398595413)
                  ·
                    refine ⟨142229348809342683976145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24273808863461151398595413 142229348809342683976145)
                    ·
                      rfl

theorem cell23_830972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_830972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830972 prefixEnd_830972 := by exact prefixLift 830972
  have htrace : WordTrace (prefixWord ++ tailWord_830972) baseStart_830972 baseEnd_830972 := by
    simpa [prefixWord, tailWord_830972, baseEnd_830972] using wordTrace_append hprefix tailTrace_830972
  have hstable : (prefixWord ++ tailWord_830972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830972).length < 2 ^ (prefixWord ++ tailWord_830972).sum := by decide
  have hdescent : baseEnd_830972 < baseStart_830972 := by decide
  rcases family_descends (prefixWord ++ tailWord_830972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830979 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 7, 2]
def baseStart_830979 : Nat := 118140960795 + 830979 * 2 ^ 59
def prefixEnd_830979 : Nat := 4983230072969 + 3 ^ 40 * 830979 * 2
def baseEnd_830979 : Nat := 426691640792609524540903

theorem tailTrace_830979 : CollatzResearch.WordTrace tailWord_830979 prefixEnd_830979 426691640792609524540903 := by
  unfold tailWord_830979
  simp only [CollatzResearch.WordTrace]
  refine ⟨30308294056512477759487991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20205529371008318506325327 30308294056512477759487991)
  ·
    refine ⟨45462441084768716639231987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30308294056512477759487991 45462441084768716639231987)
    ·
      refine ⟨68193661627153074958847981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45462441084768716639231987 68193661627153074958847981)
      ·
        refine ⟨25572623110182403109567993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68193661627153074958847981 25572623110182403109567993)
        ·
          refine ⟨19179467332636802332175995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25572623110182403109567993 19179467332636802332175995)
          ·
            refine ⟨28769200998955203498263993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19179467332636802332175995 28769200998955203498263993)
            ·
              refine ⟨21576900749216402623697995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28769200998955203498263993 21576900749216402623697995)
              ·
                refine ⟨32365351123824603935546993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21576900749216402623697995 32365351123824603935546993)
                ·
                  refine ⟨24274013342868452951660245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32365351123824603935546993 24274013342868452951660245)
                  ·
                    refine ⟨568922187723479366054537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24274013342868452951660245 568922187723479366054537)
                    ·
                      refine ⟨426691640792609524540903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568922187723479366054537 426691640792609524540903)
                      ·
                        rfl

theorem cell23_830979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_830979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830979 prefixEnd_830979 := by exact prefixLift 830979
  have htrace : WordTrace (prefixWord ++ tailWord_830979) baseStart_830979 baseEnd_830979 := by
    simpa [prefixWord, tailWord_830979, baseEnd_830979] using wordTrace_append hprefix tailTrace_830979
  have hstable : (prefixWord ++ tailWord_830979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830979).length < 2 ^ (prefixWord ++ tailWord_830979).sum := by decide
  have hdescent : baseEnd_830979 < baseStart_830979 := by decide
  rcases family_descends (prefixWord ++ tailWord_830979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830980 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_830980 : Nat := 118140960795 + 830980 * 2 ^ 59
def prefixEnd_830980 : Nat := 4983230072969 + 3 ^ 40 * 830980 * 2
def baseEnd_830980 : Nat := 142230718091088006876133

theorem tailTrace_830980 : CollatzResearch.WordTrace tailWord_830980 prefixEnd_830980 142230718091088006876133 := by
  unfold tailWord_830980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15154165264754427465137197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20205553686339236620182929 15154165264754427465137197)
  ·
    refine ⟨5682811974282910299426449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15154165264754427465137197 5682811974282910299426449)
    ·
      refine ⟨4262108980712182724569837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5682811974282910299426449 4262108980712182724569837)
      ·
        refine ⟨1598290867767068521713689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4262108980712182724569837 1598290867767068521713689)
        ·
          refine ⟨1198718150825301391285267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598290867767068521713689 1198718150825301391285267)
          ·
            refine ⟨1798077226237952086927901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198718150825301391285267 1798077226237952086927901)
            ·
              refine ⟨674278959839232032597963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1798077226237952086927901 674278959839232032597963)
              ·
                refine ⟨1011418439758848048896945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674278959839232032597963 1011418439758848048896945)
                ·
                  refine ⟨758563829819136036672709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011418439758848048896945 758563829819136036672709)
                  ·
                    refine ⟨142230718091088006876133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758563829819136036672709 142230718091088006876133)
                    ·
                      rfl

theorem cell23_830980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_830980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830980 prefixEnd_830980 := by exact prefixLift 830980
  have htrace : WordTrace (prefixWord ++ tailWord_830980) baseStart_830980 baseEnd_830980 := by
    simpa [prefixWord, tailWord_830980, baseEnd_830980] using wordTrace_append hprefix tailTrace_830980
  have hstable : (prefixWord ++ tailWord_830980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830980).length < 2 ^ (prefixWord ++ tailWord_830980).sum := by decide
  have hdescent : baseEnd_830980 < baseStart_830980 := by decide
  rcases family_descends (prefixWord ++ tailWord_830980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830986 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_830986 : Nat := 118140960795 + 830986 * 2 ^ 59
def prefixEnd_830986 : Nat := 4983230072969 + 3 ^ 40 * 830986 * 2
def baseEnd_830986 : Nat := 426695235157190997153371

theorem tailTrace_830986 : CollatzResearch.WordTrace tailWord_830986 prefixEnd_830986 426695235157190997153371 := by
  unfold tailWord_830986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577137341871779488748203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20205699578324745303328541 7577137341871779488748203)
  ·
    refine ⟨11365706012807669233122305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7577137341871779488748203 11365706012807669233122305)
    ·
      refine ⟨8524279509605751924841729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11365706012807669233122305 8524279509605751924841729)
      ·
        refine ⟨6393209632204313943631297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8524279509605751924841729 6393209632204313943631297)
        ·
          refine ⟨4794907224153235457723473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6393209632204313943631297 4794907224153235457723473)
          ·
            refine ⟨3596180418114926593292605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4794907224153235457723473 3596180418114926593292605)
            ·
              refine ⟨1348567656793097472484727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3596180418114926593292605 1348567656793097472484727)
              ·
                refine ⟨2022851485189646208727091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348567656793097472484727 2022851485189646208727091)
                ·
                  refine ⟨3034277227784469313090637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022851485189646208727091 3034277227784469313090637)
                  ·
                    refine ⟨1137853960419175992408989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034277227784469313090637 1137853960419175992408989)
                    ·
                      refine ⟨426695235157190997153371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137853960419175992408989 426695235157190997153371)
                      ·
                        rfl

theorem cell23_830986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_830986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_830986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_830986 prefixEnd_830986 := by exact prefixLift 830986
  have htrace : WordTrace (prefixWord ++ tailWord_830986) baseStart_830986 baseEnd_830986 := by
    simpa [prefixWord, tailWord_830986, baseEnd_830986] using wordTrace_append hprefix tailTrace_830986
  have hstable : (prefixWord ++ tailWord_830986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830986).length < 2 ^ (prefixWord ++ tailWord_830986).sum := by decide
  have hdescent : baseEnd_830986 < baseStart_830986 := by decide
  rcases family_descends (prefixWord ++ tailWord_830986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831037 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_831037 : Nat := 118140960795 + 831037 * 2 ^ 59
def prefixEnd_831037 : Nat := 4983230072969 + 3 ^ 40 * 831037 * 2
def baseEnd_831037 : Nat := 426721422670570297615637

theorem tailTrace_831037 : CollatzResearch.WordTrace tailWord_831037 prefixEnd_831037 426721422670570297615637 := by
  unfold tailWord_831037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30310409490302353665099365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20206939660201569110066243 30310409490302353665099365)
  ·
    refine ⟨5683201779431691312206131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30310409490302353665099365 5683201779431691312206131)
    ·
      refine ⟨8524802669147536968309197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5683201779431691312206131 8524802669147536968309197)
      ·
        refine ⟨3196801000930326363115949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8524802669147536968309197 3196801000930326363115949)
        ·
          refine ⟨1198800375348872386168481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3196801000930326363115949 1198800375348872386168481)
          ·
            refine ⟨899100281511654289626361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198800375348872386168481 899100281511654289626361)
            ·
              refine ⟨674325211133740717219771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899100281511654289626361 674325211133740717219771)
              ·
                refine ⟨1011487816700611075829657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674325211133740717219771 1011487816700611075829657)
                ·
                  refine ⟨758615862525458306872243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011487816700611075829657 758615862525458306872243)
                  ·
                    refine ⟨1137923793788187460308365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 758615862525458306872243 1137923793788187460308365)
                    ·
                      refine ⟨426721422670570297615637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1137923793788187460308365 426721422670570297615637)
                      ·
                        rfl

theorem cell23_831037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_831037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831037 prefixEnd_831037 := by exact prefixLift 831037
  have htrace : WordTrace (prefixWord ++ tailWord_831037) baseStart_831037 baseEnd_831037 := by
    simpa [prefixWord, tailWord_831037, baseEnd_831037] using wordTrace_append hprefix tailTrace_831037
  have hstable : (prefixWord ++ tailWord_831037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831037).length < 2 ^ (prefixWord ++ tailWord_831037).sum := by decide
  have hdescent : baseEnd_831037 < baseStart_831037 := by decide
  rcases family_descends (prefixWord ++ tailWord_831037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831047 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_831047 : Nat := 118140960795 + 831047 * 2 ^ 59
def prefixEnd_831047 : Nat := 4983230072969 + 3 ^ 40 * 831047 * 2
def baseEnd_831047 : Nat := 426726557477115258490591

theorem tailTrace_831047 : CollatzResearch.WordTrace tailWord_831047 prefixEnd_831047 426726557477115258490591 := by
  unfold tailWord_831047
  simp only [CollatzResearch.WordTrace]
  refine ⟨30310774220266125372963395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20207182813510750248642263 30310774220266125372963395)
  ·
    refine ⟨45466161330399188059445093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30310774220266125372963395 45466161330399188059445093)
    ·
      refine ⟨8524905249449847761145955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45466161330399188059445093 8524905249449847761145955)
      ·
        refine ⟨12787357874174771641718933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524905249449847761145955 12787357874174771641718933)
        ·
          refine ⟨599407400351942420705575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12787357874174771641718933 599407400351942420705575)
          ·
            refine ⟨899111100527913631058363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599407400351942420705575 899111100527913631058363)
            ·
              refine ⟨1348666650791870446587545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899111100527913631058363 1348666650791870446587545)
              ·
                refine ⟨1011499988093902834940659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348666650791870446587545 1011499988093902834940659)
                ·
                  refine ⟨1517249982140854252410989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011499988093902834940659 1517249982140854252410989)
                  ·
                    refine ⟨568968743302820344654121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517249982140854252410989 568968743302820344654121)
                    ·
                      refine ⟨426726557477115258490591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 568968743302820344654121 426726557477115258490591)
                      ·
                        rfl

theorem cell23_831047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_831047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831047 prefixEnd_831047 := by exact prefixLift 831047
  have htrace : WordTrace (prefixWord ++ tailWord_831047) baseStart_831047 baseEnd_831047 := by
    simpa [prefixWord, tailWord_831047, baseEnd_831047] using wordTrace_append hprefix tailTrace_831047
  have hstable : (prefixWord ++ tailWord_831047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831047).length < 2 ^ (prefixWord ++ tailWord_831047).sum := by decide
  have hdescent : baseEnd_831047 < baseStart_831047 := by decide
  rcases family_descends (prefixWord ++ tailWord_831047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831093 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_831093 : Nat := 118140960795 + 831093 * 2 ^ 59
def prefixEnd_831093 : Nat := 4983230072969 + 3 ^ 40 * 831093 * 2
def baseEnd_831093 : Nat := 426750177587222078515379

theorem tailTrace_831093 : CollatzResearch.WordTrace tailWord_831093 prefixEnd_831093 426750177587222078515379 := by
  unfold tailWord_831093
  simp only [CollatzResearch.WordTrace]
  refine ⟨30312451978099475229137933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20208301318732983486091955 30312451978099475229137933)
  ·
    refine ⟨11367169491787303210926725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30312451978099475229137933 11367169491787303210926725)
    ·
      refine ⟨2131344279710119352048761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11367169491787303210926725 2131344279710119352048761)
      ·
        refine ⟨1598508209782589514036571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2131344279710119352048761 1598508209782589514036571)
        ·
          refine ⟨2397762314673884271054857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598508209782589514036571 2397762314673884271054857)
          ·
            refine ⟨1798321736005413203291143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397762314673884271054857 1798321736005413203291143)
            ·
              refine ⟨2697482604008119804936715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798321736005413203291143 2697482604008119804936715)
              ·
                refine ⟨4046223906012179707405073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697482604008119804936715 4046223906012179707405073)
                ·
                  refine ⟨3034667929509134780553805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046223906012179707405073 3034667929509134780553805)
                  ·
                    refine ⟨1138000473565925542707677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034667929509134780553805 1138000473565925542707677)
                    ·
                      refine ⟨426750177587222078515379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1138000473565925542707677 426750177587222078515379)
                      ·
                        rfl

theorem cell23_831093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_831093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831093 prefixEnd_831093 := by exact prefixLift 831093
  have htrace : WordTrace (prefixWord ++ tailWord_831093) baseStart_831093 baseEnd_831093 := by
    simpa [prefixWord, tailWord_831093, baseEnd_831093] using wordTrace_append hprefix tailTrace_831093
  have hstable : (prefixWord ++ tailWord_831093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831093).length < 2 ^ (prefixWord ++ tailWord_831093).sum := by decide
  have hdescent : baseEnd_831093 < baseStart_831093 := by decide
  rcases family_descends (prefixWord ++ tailWord_831093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831099 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4]
def baseStart_831099 : Nat := 118140960795 + 831099 * 2 ^ 59
def prefixEnd_831099 : Nat := 4983230072969 + 3 ^ 40 * 831099 * 2
def baseEnd_831099 : Nat := 426753258471149055040351

theorem tailTrace_831099 : CollatzResearch.WordTrace tailWord_831099 prefixEnd_831099 426753258471149055040351 := by
  unfold tailWord_831099
  simp only [CollatzResearch.WordTrace]
  refine ⟨30312670816077738253856351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20208447210718492169237567 30312670816077738253856351)
  ·
    refine ⟨45469006224116607380784527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30312670816077738253856351 45469006224116607380784527)
    ·
      refine ⟨68203509336174911071176791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45469006224116607380784527 68203509336174911071176791)
      ·
        refine ⟨102305264004262366606765187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68203509336174911071176791 102305264004262366606765187)
        ·
          refine ⟨153457896006393549910147781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102305264004262366606765187 153457896006393549910147781)
          ·
            refine ⟨28773355501198790608152709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153457896006393549910147781 28773355501198790608152709)
            ·
              refine ⟨5395004156474773239028633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28773355501198790608152709 5395004156474773239028633)
              ·
                refine ⟨4046253117356079929271475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395004156474773239028633 4046253117356079929271475)
                ·
                  refine ⟨6069379676034119893907213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046253117356079929271475 6069379676034119893907213)
                  ·
                    refine ⟨2276017378512794960215205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6069379676034119893907213 2276017378512794960215205)
                    ·
                      refine ⟨426753258471149055040351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2276017378512794960215205 426753258471149055040351)
                      ·
                        rfl

theorem cell23_831099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_831099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831099 prefixEnd_831099 := by exact prefixLift 831099
  have htrace : WordTrace (prefixWord ++ tailWord_831099) baseStart_831099 baseEnd_831099 := by
    simpa [prefixWord, tailWord_831099, baseEnd_831099] using wordTrace_append hprefix tailTrace_831099
  have hstable : (prefixWord ++ tailWord_831099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831099).length < 2 ^ (prefixWord ++ tailWord_831099).sum := by decide
  have hdescent : baseEnd_831099 < baseStart_831099 := by decide
  rcases family_descends (prefixWord ++ tailWord_831099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831116 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 6, 2]
def baseStart_831116 : Nat := 118140960795 + 831116 * 2 ^ 59
def prefixEnd_831116 : Nat := 4983230072969 + 3 ^ 40 * 831116 * 2
def baseEnd_831116 : Nat := 426761987642275488527773

theorem tailTrace_831116 : CollatzResearch.WordTrace tailWord_831116 prefixEnd_831116 426761987642275488527773 := by
  unfold tailWord_831116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156645428508075078612601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20208860571344100104816801 15156645428508075078612601)
  ·
    refine ⟨11367484071381056308959451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15156645428508075078612601 11367484071381056308959451)
    ·
      refine ⟨17051226107071584463439177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367484071381056308959451 17051226107071584463439177)
      ·
        refine ⟨12788419580303688347579383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17051226107071584463439177 12788419580303688347579383)
        ·
          refine ⟨19182629370455532521369075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12788419580303688347579383 19182629370455532521369075)
          ·
            refine ⟨28773944055683298782053613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19182629370455532521369075 28773944055683298782053613)
            ·
              refine ⟨10790229020881237043270105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28773944055683298782053613 10790229020881237043270105)
              ·
                refine ⟨8092671765660927782452579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10790229020881237043270105 8092671765660927782452579)
                ·
                  refine ⟨12139007648491391673678869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8092671765660927782452579 12139007648491391673678869)
                  ·
                    refine ⟨569015983523033984703697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12139007648491391673678869 569015983523033984703697)
                    ·
                      refine ⟨426761987642275488527773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569015983523033984703697 426761987642275488527773)
                      ·
                        rfl

theorem cell23_831116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_831116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831116 prefixEnd_831116 := by exact prefixLift 831116
  have htrace : WordTrace (prefixWord ++ tailWord_831116) baseStart_831116 baseEnd_831116 := by
    simpa [prefixWord, tailWord_831116, baseEnd_831116] using wordTrace_append hprefix tailTrace_831116
  have hstable : (prefixWord ++ tailWord_831116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831116).length < 2 ^ (prefixWord ++ tailWord_831116).sum := by decide
  have hdescent : baseEnd_831116 < baseStart_831116 := by decide
  rcases family_descends (prefixWord ++ tailWord_831116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831139 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 8]
def baseStart_831139 : Nat := 118140960795 + 831139 * 2 ^ 59
def prefixEnd_831139 : Nat := 4983230072969 + 3 ^ 40 * 831139 * 2
def baseEnd_831139 : Nat := 47419310855258766504463

theorem tailTrace_831139 : CollatzResearch.WordTrace tailWord_831139 prefixEnd_831139 47419310855258766504463 := by
  unfold tailWord_831139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30314129735932825085312471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20209419823955216723541647 30314129735932825085312471)
  ·
    refine ⟨45471194603899237627968707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30314129735932825085312471 45471194603899237627968707)
    ·
      refine ⟨68206791905848856441953061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45471194603899237627968707 68206791905848856441953061)
      ·
        refine ⟨12788773482346660582866199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68206791905848856441953061 12788773482346660582866199)
        ·
          refine ⟨19183160223519990874299299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12788773482346660582866199 19183160223519990874299299)
          ·
            refine ⟨28774740335279986311448949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19183160223519990874299299 28774740335279986311448949)
            ·
              refine ⟨2697631906432498716698339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28774740335279986311448949 2697631906432498716698339)
              ·
                refine ⟨4046447859648748075047509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697631906432498716698339 4046447859648748075047509)
                ·
                  refine ⟨47419310855258766504463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4046447859648748075047509 47419310855258766504463)
                  ·
                    rfl

theorem cell23_831139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 8].length) (baseStart_831139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831139 prefixEnd_831139 := by exact prefixLift 831139
  have htrace : WordTrace (prefixWord ++ tailWord_831139) baseStart_831139 baseEnd_831139 := by
    simpa [prefixWord, tailWord_831139, baseEnd_831139] using wordTrace_append hprefix tailTrace_831139
  have hstable : (prefixWord ++ tailWord_831139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831139).length < 2 ^ (prefixWord ++ tailWord_831139).sum := by decide
  have hdescent : baseEnd_831139 < baseStart_831139 := by decide
  rcases family_descends (prefixWord ++ tailWord_831139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831193 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 4, 3, 2]
def baseStart_831193 : Nat := 118140960795 + 831193 * 2 ^ 59
def prefixEnd_831193 : Nat := 4983230072969 + 3 ^ 40 * 831193 * 2
def baseEnd_831193 : Nat := 426801525652671687264919

theorem tailTrace_831193 : CollatzResearch.WordTrace tailWord_831193 prefixEnd_831193 426801525652671687264919 := by
  unfold tailWord_831193
  simp only [CollatzResearch.WordTrace]
  refine ⟨30316099277737192307778233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20210732851824794871852155 30316099277737192307778233)
  ·
    refine ⟨22737074458302894230833675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30316099277737192307778233 22737074458302894230833675)
    ·
      refine ⟨34105611687454341346250513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22737074458302894230833675 34105611687454341346250513)
      ·
        refine ⟨25579208765590756009687885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34105611687454341346250513 25579208765590756009687885)
        ·
          refine ⟨9592203287096533503632957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25579208765590756009687885 9592203287096533503632957)
          ·
            refine ⟨3597076232661200063862359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9592203287096533503632957 3597076232661200063862359)
            ·
              refine ⟨5395614348991800095793539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597076232661200063862359 5395614348991800095793539)
              ·
                refine ⟨8093421523487700143690309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395614348991800095793539 8093421523487700143690309)
                ·
                  refine ⟨1517516535653943776941933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8093421523487700143690309 1517516535653943776941933)
                  ·
                    refine ⟨569068700870228916353225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517516535653943776941933 569068700870228916353225)
                    ·
                      refine ⟨426801525652671687264919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569068700870228916353225 426801525652671687264919)
                      ·
                        rfl

theorem cell23_831193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_831193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831193 prefixEnd_831193 := by exact prefixLift 831193
  have htrace : WordTrace (prefixWord ++ tailWord_831193) baseStart_831193 baseEnd_831193 := by
    simpa [prefixWord, tailWord_831193, baseEnd_831193] using wordTrace_append hprefix tailTrace_831193
  have hstable : (prefixWord ++ tailWord_831193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831193).length < 2 ^ (prefixWord ++ tailWord_831193).sum := by decide
  have hdescent : baseEnd_831193 < baseStart_831193 := by decide
  rcases family_descends (prefixWord ++ tailWord_831193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831200 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 1, 1, 3]
def baseStart_831200 : Nat := 118140960795 + 831200 * 2 ^ 59
def prefixEnd_831200 : Nat := 4983230072969 + 3 ^ 40 * 831200 * 2
def baseEnd_831200 : Nat := 426805120017253159877387

theorem tailTrace_831200 : CollatzResearch.WordTrace tailWord_831200 prefixEnd_831200 426805120017253159877387 := by
  unfold tailWord_831200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158177294355916251641527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20210903059141221668855369 15158177294355916251641527)
  ·
    refine ⟨22737265941533874377462291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15158177294355916251641527 22737265941533874377462291)
    ·
      refine ⟨34105898912300811566193437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22737265941533874377462291 34105898912300811566193437)
      ·
        refine ⟨12789712092112804337322539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34105898912300811566193437 12789712092112804337322539)
        ·
          refine ⟨19184568138169206505983809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12789712092112804337322539 19184568138169206505983809)
          ·
            refine ⟨14388426103626904879487857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19184568138169206505983809 14388426103626904879487857)
            ·
              refine ⟨10791319577720178659615893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14388426103626904879487857 10791319577720178659615893)
              ·
                refine ⟨505843105205633374669495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10791319577720178659615893 505843105205633374669495)
                ·
                  refine ⟨758764657808450062004243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505843105205633374669495 758764657808450062004243)
                  ·
                    refine ⟨1138146986712675093006365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 758764657808450062004243 1138146986712675093006365)
                    ·
                      refine ⟨426805120017253159877387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1138146986712675093006365 426805120017253159877387)
                      ·
                        rfl

theorem cell23_831200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_831200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831200 prefixEnd_831200 := by exact prefixLift 831200
  have htrace : WordTrace (prefixWord ++ tailWord_831200) baseStart_831200 baseEnd_831200 := by
    simpa [prefixWord, tailWord_831200, baseEnd_831200] using wordTrace_append hprefix tailTrace_831200
  have hstable : (prefixWord ++ tailWord_831200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831200).length < 2 ^ (prefixWord ++ tailWord_831200).sum := by decide
  have hdescent : baseEnd_831200 < baseStart_831200 := by decide
  rcases family_descends (prefixWord ++ tailWord_831200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831207 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 6]
def baseStart_831207 : Nat := 118140960795 + 831207 * 2 ^ 59
def prefixEnd_831207 : Nat := 4983230072969 + 3 ^ 40 * 831207 * 2
def baseEnd_831207 : Nat := 47423190486870514721095

theorem tailTrace_831207 : CollatzResearch.WordTrace tailWord_831207 prefixEnd_831207 47423190486870514721095 := by
  unfold tailWord_831207
  simp only [CollatzResearch.WordTrace]
  refine ⟨30316609899686472698787875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20211073266457648465858583 30316609899686472698787875)
  ·
    refine ⟨45474914849529709048181813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30316609899686472698787875 45474914849529709048181813)
    ·
      refine ⟨4263273267143410223267045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45474914849529709048181813 4263273267143410223267045)
      ·
        refine ⟨799363737589389416862571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4263273267143410223267045 799363737589389416862571)
        ·
          refine ⟨1199045606384084125293857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799363737589389416862571 1199045606384084125293857)
          ·
            refine ⟨899284204788063093970393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199045606384084125293857 899284204788063093970393)
            ·
              refine ⟨674463153591047320477795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899284204788063093970393 674463153591047320477795)
              ·
                refine ⟨1011694730386570980716693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674463153591047320477795 1011694730386570980716693)
                ·
                  refine ⟨47423190486870514721095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1011694730386570980716693 47423190486870514721095)
                  ·
                    rfl

theorem cell23_831207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 6].length) (baseStart_831207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831207 prefixEnd_831207 := by exact prefixLift 831207
  have htrace : WordTrace (prefixWord ++ tailWord_831207) baseStart_831207 baseEnd_831207 := by
    simpa [prefixWord, tailWord_831207, baseEnd_831207] using wordTrace_append hprefix tailTrace_831207
  have hstable : (prefixWord ++ tailWord_831207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831207).length < 2 ^ (prefixWord ++ tailWord_831207).sum := by decide
  have hdescent : baseEnd_831207 < baseStart_831207 := by decide
  rcases family_descends (prefixWord ++ tailWord_831207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831216 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 6, 4]
def baseStart_831216 : Nat := 118140960795 + 831216 * 2 ^ 59
def prefixEnd_831216 : Nat := 4983230072969 + 3 ^ 40 * 831216 * 2
def baseEnd_831216 : Nat := 142271111902575032425771

theorem tailTrace_831216 : CollatzResearch.WordTrace tailWord_831216 prefixEnd_831216 142271111902575032425771 := by
  unfold tailWord_831216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158469078326933617932751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20211292104435911490577001 15158469078326933617932751)
  ·
    refine ⟨22737703617490400426899127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15158469078326933617932751 22737703617490400426899127)
    ·
      refine ⟨34106555426235600640348691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22737703617490400426899127 34106555426235600640348691)
      ·
        refine ⟨51159833139353400960523037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34106555426235600640348691 51159833139353400960523037)
        ·
          refine ⟨19184937427257525360196139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51159833139353400960523037 19184937427257525360196139)
          ·
            refine ⟨28777406140886288040294209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19184937427257525360196139 28777406140886288040294209)
            ·
              refine ⟨21583054605664716030220657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28777406140886288040294209 21583054605664716030220657)
              ·
                refine ⟨16187290954248537022665493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21583054605664716030220657 16187290954248537022665493)
                ·
                  refine ⟨758779263480400172937445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16187290954248537022665493 758779263480400172937445)
                  ·
                    refine ⟨142271111902575032425771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758779263480400172937445 142271111902575032425771)
                    ·
                      rfl

theorem cell23_831216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_831216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831216 prefixEnd_831216 := by exact prefixLift 831216
  have htrace : WordTrace (prefixWord ++ tailWord_831216) baseStart_831216 baseEnd_831216 := by
    simpa [prefixWord, tailWord_831216, baseEnd_831216] using wordTrace_append hprefix tailTrace_831216
  have hstable : (prefixWord ++ tailWord_831216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831216).length < 2 ^ (prefixWord ++ tailWord_831216).sum := by decide
  have hdescent : baseEnd_831216 < baseStart_831216 := by decide
  rcases family_descends (prefixWord ++ tailWord_831216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831223 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_831223 : Nat := 118140960795 + 831223 * 2 ^ 59
def prefixEnd_831223 : Nat := 4983230072969 + 3 ^ 40 * 831223 * 2
def baseEnd_831223 : Nat := 426816930072306569889781

theorem tailTrace_831223 : CollatzResearch.WordTrace tailWord_831223 prefixEnd_831223 426816930072306569889781 := by
  unfold tailWord_831223
  simp only [CollatzResearch.WordTrace]
  refine ⟨30317193467628507431370323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20211462311752338287580215 30317193467628507431370323)
  ·
    refine ⟨45475790201442761147055485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30317193467628507431370323 45475790201442761147055485)
    ·
      refine ⟨17053421325541035430145807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45475790201442761147055485 17053421325541035430145807)
      ·
        refine ⟨25580131988311553145218711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17053421325541035430145807 25580131988311553145218711)
        ·
          refine ⟨38370197982467329717828067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25580131988311553145218711 38370197982467329717828067)
          ·
            refine ⟨57555296973700994576742101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38370197982467329717828067 57555296973700994576742101)
            ·
              refine ⟨1348952272821117060392393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57555296973700994576742101 1348952272821117060392393)
              ·
                refine ⟨1011714204615837795294295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348952272821117060392393 1011714204615837795294295)
                ·
                  refine ⟨1517571306923756692941443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011714204615837795294295 1517571306923756692941443)
                  ·
                    refine ⟨2276356960385635039412165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1517571306923756692941443 2276356960385635039412165)
                    ·
                      refine ⟨426816930072306569889781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2276356960385635039412165 426816930072306569889781)
                      ·
                        rfl

theorem cell23_831223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_831223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831223 prefixEnd_831223 := by exact prefixLift 831223
  have htrace : WordTrace (prefixWord ++ tailWord_831223) baseStart_831223 baseEnd_831223 := by
    simpa [prefixWord, tailWord_831223, baseEnd_831223] using wordTrace_append hprefix tailTrace_831223
  have hstable : (prefixWord ++ tailWord_831223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831223).length < 2 ^ (prefixWord ++ tailWord_831223).sum := by decide
  have hdescent : baseEnd_831223 < baseStart_831223 := by decide
  rcases family_descends (prefixWord ++ tailWord_831223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831240 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_831240 : Nat := 118140960795 + 831240 * 2 ^ 59
def prefixEnd_831240 : Nat := 4983230072969 + 3 ^ 40 * 831240 * 2
def baseEnd_831240 : Nat := 426825659243433003377203

theorem tailTrace_831240 : CollatzResearch.WordTrace tailWord_831240 prefixEnd_831240 426825659243433003377203 := by
  unfold tailWord_831240
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158906754283459667369587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20211875672377946223159449 15158906754283459667369587)
  ·
    refine ⟨22738360131425189501054381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15158906754283459667369587 22738360131425189501054381)
    ·
      refine ⟨8526885049284446062895393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22738360131425189501054381 8526885049284446062895393)
      ·
        refine ⟨6395163786963334547171545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8526885049284446062895393 6395163786963334547171545)
        ·
          refine ⟨4796372840222500910378659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6395163786963334547171545 4796372840222500910378659)
          ·
            refine ⟨7194559260333751365567989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4796372840222500910378659 7194559260333751365567989)
            ·
              refine ⟨674489930656289190521999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7194559260333751365567989 674489930656289190521999)
              ·
                refine ⟨1011734895984433785782999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674489930656289190521999 1011734895984433785782999)
                ·
                  refine ⟨1517602343976650678674499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011734895984433785782999 1517602343976650678674499)
                  ·
                    refine ⟨2276403515964976018011749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1517602343976650678674499 2276403515964976018011749)
                    ·
                      refine ⟨426825659243433003377203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2276403515964976018011749 426825659243433003377203)
                      ·
                        rfl

theorem cell23_831240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_831240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831240 prefixEnd_831240 := by exact prefixLift 831240
  have htrace : WordTrace (prefixWord ++ tailWord_831240) baseStart_831240 baseEnd_831240 := by
    simpa [prefixWord, tailWord_831240, baseEnd_831240] using wordTrace_append hprefix tailTrace_831240
  have hstable : (prefixWord ++ tailWord_831240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831240).length < 2 ^ (prefixWord ++ tailWord_831240).sum := by decide
  have hdescent : baseEnd_831240 < baseStart_831240 := by decide
  rcases family_descends (prefixWord ++ tailWord_831240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831243 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 3]
def baseStart_831243 : Nat := 118140960795 + 831243 * 2 ^ 59
def prefixEnd_831243 : Nat := 4983230072969 + 3 ^ 40 * 831243 * 2
def baseEnd_831243 : Nat := 426827199685396491639689

theorem tailTrace_831243 : CollatzResearch.WordTrace tailWord_831243 prefixEnd_831243 426827199685396491639689 := by
  unfold tailWord_831243
  simp only [CollatzResearch.WordTrace]
  refine ⟨30317922927556050847098383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20211948618370700564732255 30317922927556050847098383)
  ·
    refine ⟨45476884391334076270647575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30317922927556050847098383 45476884391334076270647575)
    ·
      refine ⟨68215326587001114405971363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45476884391334076270647575 68215326587001114405971363)
      ·
        refine ⟨102322989880501671608957045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68215326587001114405971363 102322989880501671608957045)
        ·
          refine ⟨9592780301297031713339723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102322989880501671608957045 9592780301297031713339723)
          ·
            refine ⟨14389170451945547570009585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592780301297031713339723 14389170451945547570009585)
            ·
              refine ⟨10791877838959160677507189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14389170451945547570009585 10791877838959160677507189)
              ·
                refine ⟨1011738547402421313516299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10791877838959160677507189 1011738547402421313516299)
                ·
                  refine ⟨1517607821103631970274449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011738547402421313516299 1517607821103631970274449)
                  ·
                    refine ⟨1138205865827723977705837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517607821103631970274449 1138205865827723977705837)
                    ·
                      refine ⟨426827199685396491639689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1138205865827723977705837 426827199685396491639689)
                      ·
                        rfl

theorem cell23_831243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 3].length) (baseStart_831243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831243 prefixEnd_831243 := by exact prefixLift 831243
  have htrace : WordTrace (prefixWord ++ tailWord_831243) baseStart_831243 baseEnd_831243 := by
    simpa [prefixWord, tailWord_831243, baseEnd_831243] using wordTrace_append hprefix tailTrace_831243
  have hstable : (prefixWord ++ tailWord_831243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831243).length < 2 ^ (prefixWord ++ tailWord_831243).sum := by decide
  have hdescent : baseEnd_831243 < baseStart_831243 := by decide
  rcases family_descends (prefixWord ++ tailWord_831243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831245 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_831245 : Nat := 118140960795 + 831245 * 2 ^ 59
def prefixEnd_831245 : Nat := 4983230072969 + 3 ^ 40 * 831245 * 2
def baseEnd_831245 : Nat := 142276075548901827938227

theorem tailTrace_831245 : CollatzResearch.WordTrace tailWord_831245 prefixEnd_831245 142276075548901827938227 := by
  unfold tailWord_831245
  simp only [CollatzResearch.WordTrace]
  refine ⟨30317995873548805188671189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20211997249032536792447459 30317995873548805188671189)
  ·
    refine ⟨710578028286300121609481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30317995873548805188671189 710578028286300121609481)
    ·
      refine ⟨532933521214725091207111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 710578028286300121609481 532933521214725091207111)
      ·
        refine ⟨799400281822087636810667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532933521214725091207111 799400281822087636810667)
        ·
          refine ⟨1199100422733131455216001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799400281822087636810667 1199100422733131455216001)
          ·
            refine ⟨899325317049848591412001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199100422733131455216001 899325317049848591412001)
            ·
              refine ⟨674493987787386443559001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899325317049848591412001 674493987787386443559001)
              ·
                refine ⟨505870490840539832669251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674493987787386443559001 505870490840539832669251)
                ·
                  refine ⟨758805736260809749003877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505870490840539832669251 758805736260809749003877)
                  ·
                    refine ⟨142276075548901827938227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758805736260809749003877 142276075548901827938227)
                    ·
                      rfl

theorem cell23_831245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_831245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831245 prefixEnd_831245 := by exact prefixLift 831245
  have htrace : WordTrace (prefixWord ++ tailWord_831245) baseStart_831245 baseEnd_831245 := by
    simpa [prefixWord, tailWord_831245, baseEnd_831245] using wordTrace_append hprefix tailTrace_831245
  have hstable : (prefixWord ++ tailWord_831245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831245).length < 2 ^ (prefixWord ++ tailWord_831245).sum := by decide
  have hdescent : baseEnd_831245 < baseStart_831245 := by decide
  rcases family_descends (prefixWord ++ tailWord_831245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831294 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_831294 : Nat := 118140960795 + 831294 * 2 ^ 59
def prefixEnd_831294 : Nat := 4983230072969 + 3 ^ 40 * 831294 * 2
def baseEnd_831294 : Nat := 426853387198775792101955

theorem tailTrace_831294 : CollatzResearch.WordTrace tailWord_831294 prefixEnd_831294 426853387198775792101955 := by
  unfold tailWord_831294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789972881296410819650617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20213188700247524371469957 3789972881296410819650617)
  ·
    refine ⟨2842479660972308114737963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3789972881296410819650617 2842479660972308114737963)
    ·
      refine ⟨4263719491458462172106945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2842479660972308114737963 4263719491458462172106945)
      ·
        refine ⟨3197789618593846629080209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4263719491458462172106945 3197789618593846629080209)
        ·
          refine ⟨2398342213945384971810157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3197789618593846629080209 2398342213945384971810157)
          ·
            refine ⟨899378330229519364428809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2398342213945384971810157 899378330229519364428809)
            ·
              refine ⟨674533747672139523321607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899378330229519364428809 674533747672139523321607)
              ·
                refine ⟨1011800621508209284982411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674533747672139523321607 1011800621508209284982411)
                ·
                  refine ⟨1517700932262313927473617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011800621508209284982411 1517700932262313927473617)
                  ·
                    refine ⟨1138275699196735445605213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517700932262313927473617 1138275699196735445605213)
                    ·
                      refine ⟨426853387198775792101955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1138275699196735445605213 426853387198775792101955)
                      ·
                        rfl

theorem cell23_831294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_831294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831294 prefixEnd_831294 := by exact prefixLift 831294
  have htrace : WordTrace (prefixWord ++ tailWord_831294) baseStart_831294 baseEnd_831294 := by
    simpa [prefixWord, tailWord_831294, baseEnd_831294] using wordTrace_append hprefix tailTrace_831294
  have hstable : (prefixWord ++ tailWord_831294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831294).length < 2 ^ (prefixWord ++ tailWord_831294).sum := by decide
  have hdescent : baseEnd_831294 < baseStart_831294 := by decide
  rcases family_descends (prefixWord ++ tailWord_831294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831306 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_831306 : Nat := 118140960795 + 831306 * 2 ^ 59
def prefixEnd_831306 : Nat := 4983230072969 + 3 ^ 40 * 831306 * 2
def baseEnd_831306 : Nat := 142286516322209915050633

theorem tailTrace_831306 : CollatzResearch.WordTrace tailWord_831306 prefixEnd_831306 142286516322209915050633 := by
  unfold tailWord_831306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580055181581953151660443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20213480484218541737761181 7580055181581953151660443)
  ·
    refine ⟨11370082772372929727490665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7580055181581953151660443 11370082772372929727490665)
    ·
      refine ⟨8527562079279697295617999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11370082772372929727490665 8527562079279697295617999)
      ·
        refine ⟨12791343118919545943426999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527562079279697295617999 12791343118919545943426999)
        ·
          refine ⟨19187014678379318915140499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791343118919545943426999 19187014678379318915140499)
          ·
            refine ⟨28780522017568978372710749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19187014678379318915140499 28780522017568978372710749)
            ·
              refine ⟨10792695756588366889766531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28780522017568978372710749 10792695756588366889766531)
              ·
                refine ⟨16189043634882550334649797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10792695756588366889766531 16189043634882550334649797)
                ·
                  refine ⟨3035445681540478187746837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16189043634882550334649797 3035445681540478187746837)
                  ·
                    refine ⟨142286516322209915050633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3035445681540478187746837 142286516322209915050633)
                    ·
                      rfl

theorem cell23_831306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_831306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831306 prefixEnd_831306 := by exact prefixLift 831306
  have htrace : WordTrace (prefixWord ++ tailWord_831306) baseStart_831306 baseEnd_831306 := by
    simpa [prefixWord, tailWord_831306, baseEnd_831306] using wordTrace_append hprefix tailTrace_831306
  have hstable : (prefixWord ++ tailWord_831306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831306).length < 2 ^ (prefixWord ++ tailWord_831306).sum := by decide
  have hdescent : baseEnd_831306 < baseStart_831306 := by decide
  rcases family_descends (prefixWord ++ tailWord_831306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831324 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_831324 : Nat := 118140960795 + 831324 * 2 ^ 59
def prefixEnd_831324 : Nat := 4983230072969 + 3 ^ 40 * 831324 * 2
def baseEnd_831324 : Nat := 426868791618410674726817

theorem tailTrace_831324 : CollatzResearch.WordTrace tailWord_831324 prefixEnd_831324 426868791618410674726817 := by
  unfold tailWord_831324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15160438620131300840398513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20213918160175067787198017 15160438620131300840398513)
  ·
    refine ⟨11370328965098475630298885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15160438620131300840398513 11370328965098475630298885)
    ·
      refine ⟨2131936680955964180681041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11370328965098475630298885 2131936680955964180681041)
      ·
        refine ⟨1598952510716973135510781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2131936680955964180681041 1598952510716973135510781)
        ·
          refine ⟨599607191518864925816543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1598952510716973135510781 599607191518864925816543)
          ·
            refine ⟨899410787278297388724815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599607191518864925816543 899410787278297388724815)
            ·
              refine ⟨1349116180917446083087223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899410787278297388724815 1349116180917446083087223)
              ·
                refine ⟨2023674271376169124630835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349116180917446083087223 2023674271376169124630835)
                ·
                  refine ⟨3035511407064253686946253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023674271376169124630835 3035511407064253686946253)
                  ·
                    refine ⟨1138316777649095132604845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035511407064253686946253 1138316777649095132604845)
                    ·
                      refine ⟨426868791618410674726817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1138316777649095132604845 426868791618410674726817)
                      ·
                        rfl

theorem cell23_831324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_831324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831324 prefixEnd_831324 := by exact prefixLift 831324
  have htrace : WordTrace (prefixWord ++ tailWord_831324) baseStart_831324 baseEnd_831324 := by
    simpa [prefixWord, tailWord_831324, baseEnd_831324] using wordTrace_append hprefix tailTrace_831324
  have hstable : (prefixWord ++ tailWord_831324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831324).length < 2 ^ (prefixWord ++ tailWord_831324).sum := by decide
  have hdescent : baseEnd_831324 < baseStart_831324 := by decide
  rcases family_descends (prefixWord ++ tailWord_831324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831356 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_831356 : Nat := 118140960795 + 831356 * 2 ^ 59
def prefixEnd_831356 : Nat := 4983230072969 + 3 ^ 40 * 831356 * 2
def baseEnd_831356 : Nat := 426885222999354549526669

theorem tailTrace_831356 : CollatzResearch.WordTrace tailWord_831356 prefixEnd_831356 426885222999354549526669 := by
  unfold tailWord_831356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161022188073335572980961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20214696250764447430641281 15161022188073335572980961)
  ·
    refine ⟨11370766641055001679735721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15161022188073335572980961 11370766641055001679735721)
    ·
      refine ⟨8528074980791251259801791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11370766641055001679735721 8528074980791251259801791)
      ·
        refine ⟨12792112471186876889702687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528074980791251259801791 12792112471186876889702687)
        ·
          refine ⟨19188168706780315334554031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792112471186876889702687 19188168706780315334554031)
          ·
            refine ⟨28782253060170473001831047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19188168706780315334554031 28782253060170473001831047)
            ·
              refine ⟨43173379590255709502746571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28782253060170473001831047 43173379590255709502746571)
              ·
                refine ⟨64760069385383564254119857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43173379590255709502746571 64760069385383564254119857)
                ·
                  refine ⟨48570052039037673190589893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64760069385383564254119857 48570052039037673190589893)
                  ·
                    refine ⟨9106884757319563723235605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48570052039037673190589893 9106884757319563723235605)
                    ·
                      refine ⟨426885222999354549526669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9106884757319563723235605 426885222999354549526669)
                      ·
                        rfl

theorem cell23_831356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_831356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831356 prefixEnd_831356 := by exact prefixLift 831356
  have htrace : WordTrace (prefixWord ++ tailWord_831356) baseStart_831356 baseEnd_831356 := by
    simpa [prefixWord, tailWord_831356, baseEnd_831356] using wordTrace_append hprefix tailTrace_831356
  have hstable : (prefixWord ++ tailWord_831356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831356).length < 2 ^ (prefixWord ++ tailWord_831356).sum := by decide
  have hdescent : baseEnd_831356 < baseStart_831356 := by decide
  rcases family_descends (prefixWord ++ tailWord_831356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831376 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_831376 : Nat := 118140960795 + 831376 * 2 ^ 59
def prefixEnd_831376 : Nat := 4983230072969 + 3 ^ 40 * 831376 * 2
def baseEnd_831376 : Nat := 426895492612444471276577

theorem tailTrace_831376 : CollatzResearch.WordTrace tailWord_831376 prefixEnd_831376 426895492612444471276577 := by
  unfold tailWord_831376
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161386918037107280844991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20215182557382809707793321 15161386918037107280844991)
  ·
    refine ⟨22742080377055660921267487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15161386918037107280844991 22742080377055660921267487)
    ·
      refine ⟨34113120565583491381901231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22742080377055660921267487 34113120565583491381901231)
      ·
        refine ⟨51169680848375237072851847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34113120565583491381901231 51169680848375237072851847)
        ·
          refine ⟨76754521272562855609277771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51169680848375237072851847 76754521272562855609277771)
          ·
            refine ⟨115131781908844283413916657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76754521272562855609277771 115131781908844283413916657)
            ·
              refine ⟨86348836431633212560437493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115131781908844283413916657 86348836431633212560437493)
              ·
                refine ⟨8095203415465613677541015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86348836431633212560437493 8095203415465613677541015)
                ·
                  refine ⟨12142805123198420516311523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095203415465613677541015 12142805123198420516311523)
                  ·
                    refine ⟨18214207684797630774467285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12142805123198420516311523 18214207684797630774467285)
                    ·
                      refine ⟨426895492612444471276577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18214207684797630774467285 426895492612444471276577)
                      ·
                        rfl

theorem cell23_831376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_831376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831376 prefixEnd_831376 := by exact prefixLift 831376
  have htrace : WordTrace (prefixWord ++ tailWord_831376) baseStart_831376 baseEnd_831376 := by
    simpa [prefixWord, tailWord_831376, baseEnd_831376] using wordTrace_append hprefix tailTrace_831376
  have hstable : (prefixWord ++ tailWord_831376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831376).length < 2 ^ (prefixWord ++ tailWord_831376).sum := by decide
  have hdescent : baseEnd_831376 < baseStart_831376 := by decide
  rcases family_descends (prefixWord ++ tailWord_831376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831513 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_831513 : Nat := 118140960795 + 831513 * 2 ^ 59
def prefixEnd_831513 : Nat := 4983230072969 + 3 ^ 40 * 831513 * 2
def baseEnd_831513 : Nat := 426965839462110435263447

theorem tailTrace_831513 : CollatzResearch.WordTrace tailWord_831513 prefixEnd_831513 426965839462110435263447 := by
  unfold tailWord_831513
  simp only [CollatzResearch.WordTrace]
  refine ⟨30327770636577886959427193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20218513757718591306284795 30327770636577886959427193)
  ·
    refine ⟨22745827977433415219570395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30327770636577886959427193 22745827977433415219570395)
    ·
      refine ⟨34118741966150122829355593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22745827977433415219570395 34118741966150122829355593)
      ·
        refine ⟨25589056474612592122016695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34118741966150122829355593 25589056474612592122016695)
        ·
          refine ⟨38383584711918888183025043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25589056474612592122016695 38383584711918888183025043)
          ·
            refine ⟨57575377067878332274537565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38383584711918888183025043 57575377067878332274537565)
            ·
              refine ⟨21590766400454374602951587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57575377067878332274537565 21590766400454374602951587)
              ·
                refine ⟨32386149600681561904427381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21590766400454374602951587 32386149600681561904427381)
                ·
                  refine ⟨3036201525063896428540067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32386149600681561904427381 3036201525063896428540067)
                  ·
                    refine ⟨4554302287595844642810101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3036201525063896428540067 4554302287595844642810101)
                    ·
                      refine ⟨426965839462110435263447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4554302287595844642810101 426965839462110435263447)
                      ·
                        rfl

theorem cell23_831513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_831513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831513 prefixEnd_831513 := by exact prefixLift 831513
  have htrace : WordTrace (prefixWord ++ tailWord_831513) baseStart_831513 baseEnd_831513 := by
    simpa [prefixWord, tailWord_831513, baseEnd_831513] using wordTrace_append hprefix tailTrace_831513
  have hstable : (prefixWord ++ tailWord_831513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831513).length < 2 ^ (prefixWord ++ tailWord_831513).sum := by decide
  have hdescent : baseEnd_831513 < baseStart_831513 := by decide
  rcases family_descends (prefixWord ++ tailWord_831513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831563 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 2, 7]
def baseStart_831563 : Nat := 118140960795 + 831563 * 2 ^ 59
def prefixEnd_831563 : Nat := 4983230072969 + 3 ^ 40 * 831563 * 2
def baseEnd_831563 : Nat := 142330504498278413212739

theorem tailTrace_831563 : CollatzResearch.WordTrace tailWord_831563 prefixEnd_831563 142330504498278413212739 := by
  unfold tailWord_831563
  simp only [CollatzResearch.WordTrace]
  refine ⟨30329594286396745498747343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20219729524264496999164895 30329594286396745498747343)
  ·
    refine ⟨45494391429595118248121015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30329594286396745498747343 45494391429595118248121015)
    ·
      refine ⟨68241587144392677372181523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45494391429595118248121015 68241587144392677372181523)
      ·
        refine ⟨102362380716589016058272285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68241587144392677372181523 102362380716589016058272285)
        ·
          refine ⟨38385892768720881021852107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102362380716589016058272285 38385892768720881021852107)
          ·
            refine ⟨57578839153081321532778161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38385892768720881021852107 57578839153081321532778161)
            ·
              refine ⟨43184129364810991149583621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57578839153081321532778161 43184129364810991149583621)
              ·
                refine ⟨8097024255902060840546929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43184129364810991149583621 8097024255902060840546929)
                ·
                  refine ⟨6072768191926545630410197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8097024255902060840546929 6072768191926545630410197)
                  ·
                    refine ⟨142330504498278413212739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6072768191926545630410197 142330504498278413212739)
                    ·
                      rfl

theorem cell23_831563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_831563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831563 prefixEnd_831563 := by exact prefixLift 831563
  have htrace : WordTrace (prefixWord ++ tailWord_831563) baseStart_831563 baseEnd_831563 := by
    simpa [prefixWord, tailWord_831563, baseEnd_831563] using wordTrace_append hprefix tailTrace_831563
  have hstable : (prefixWord ++ tailWord_831563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831563).length < 2 ^ (prefixWord ++ tailWord_831563).sum := by decide
  have hdescent : baseEnd_831563 < baseStart_831563 := by decide
  rcases family_descends (prefixWord ++ tailWord_831563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831574 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_831574 : Nat := 118140960795 + 831574 * 2 ^ 59
def prefixEnd_831574 : Nat := 4983230072969 + 3 ^ 40 * 831574 * 2
def baseEnd_831574 : Nat := 426997161782034696600667

theorem tailTrace_831574 : CollatzResearch.WordTrace tailWord_831574 prefixEnd_831574 426997161782034696600667 := by
  unfold tailWord_831574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895624718084805898587361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20219996992904596251598517 1895624718084805898587361)
  ·
    refine ⟨1421718538563604423940521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1895624718084805898587361 1421718538563604423940521)
    ·
      refine ⟨1066288903922703317955391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1421718538563604423940521 1066288903922703317955391)
      ·
        refine ⟨1599433355884054976933087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066288903922703317955391 1599433355884054976933087)
        ·
          refine ⟨2399150033826082465399631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599433355884054976933087 2399150033826082465399631)
          ·
            refine ⟨3598725050739123698099447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399150033826082465399631 3598725050739123698099447)
            ·
              refine ⟨5398087576108685547149171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598725050739123698099447 5398087576108685547149171)
              ·
                refine ⟨8097131364163028320723757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398087576108685547149171 8097131364163028320723757)
                ·
                  refine ⟨3036424261561135620271409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8097131364163028320723757 3036424261561135620271409)
                  ·
                    refine ⟨2277318196170851715203557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3036424261561135620271409 2277318196170851715203557)
                    ·
                      refine ⟨426997161782034696600667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2277318196170851715203557 426997161782034696600667)
                      ·
                        rfl

theorem cell23_831574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_831574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831574 prefixEnd_831574 := by exact prefixLift 831574
  have htrace : WordTrace (prefixWord ++ tailWord_831574) baseStart_831574 baseEnd_831574 := by
    simpa [prefixWord, tailWord_831574, baseEnd_831574] using wordTrace_append hprefix tailTrace_831574
  have hstable : (prefixWord ++ tailWord_831574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831574).length < 2 ^ (prefixWord ++ tailWord_831574).sum := by decide
  have hdescent : baseEnd_831574 < baseStart_831574 := by decide
  rcases family_descends (prefixWord ++ tailWord_831574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831600 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_831600 : Nat := 118140960795 + 831600 * 2 ^ 59
def prefixEnd_831600 : Nat := 4983230072969 + 3 ^ 40 * 831600 * 2
def baseEnd_831600 : Nat := 427010512279051594875547

theorem tailTrace_831600 : CollatzResearch.WordTrace tailWord_831600 prefixEnd_831600 427010512279051594875547 := by
  unfold tailWord_831600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165471893631350408922127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20220629191508467211896169 15165471893631350408922127)
  ·
    refine ⟨22748207840447025613383191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15165471893631350408922127 22748207840447025613383191)
    ·
      refine ⟨34122311760670538420074787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22748207840447025613383191 34122311760670538420074787)
      ·
        refine ⟨51183467641005807630112181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34122311760670538420074787 51183467641005807630112181)
        ·
          refine ⟨4798450091344294465323017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51183467641005807630112181 4798450091344294465323017)
          ·
            refine ⟨3598837568508220848992263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4798450091344294465323017 3598837568508220848992263)
            ·
              refine ⟨5398256352762331273488395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598837568508220848992263 5398256352762331273488395)
              ·
                refine ⟨8097384529143496910232593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398256352762331273488395 8097384529143496910232593)
                ·
                  refine ⟨6073038396857622682674445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8097384529143496910232593 6073038396857622682674445)
                  ·
                    refine ⟨2277389398821608506002917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6073038396857622682674445 2277389398821608506002917)
                    ·
                      refine ⟨427010512279051594875547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2277389398821608506002917 427010512279051594875547)
                      ·
                        rfl

theorem cell23_831600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_831600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831600 prefixEnd_831600 := by exact prefixLift 831600
  have htrace : WordTrace (prefixWord ++ tailWord_831600) baseStart_831600 baseEnd_831600 := by
    simpa [prefixWord, tailWord_831600, baseEnd_831600] using wordTrace_append hprefix tailTrace_831600
  have hstable : (prefixWord ++ tailWord_831600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831600).length < 2 ^ (prefixWord ++ tailWord_831600).sum := by decide
  have hdescent : baseEnd_831600 < baseStart_831600 := by decide
  rcases family_descends (prefixWord ++ tailWord_831600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831634 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_831634 : Nat := 118140960795 + 831634 * 2 ^ 59
def prefixEnd_831634 : Nat := 4983230072969 + 3 ^ 40 * 831634 * 2
def baseEnd_831634 : Nat := 427027970621304461850391

theorem tailTrace_831634 : CollatzResearch.WordTrace tailWord_831634 prefixEnd_831634 427027970621304461850391 := by
  unfold tailWord_831634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583045967284881156145489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20221455912759683083054637 7583045967284881156145489)
  ·
    refine ⟨5687284475463660867109117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7583045967284881156145489 5687284475463660867109117)
    ·
      refine ⟨2132731678298872825165919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5687284475463660867109117 2132731678298872825165919)
      ·
        refine ⟨3199097517448309237748879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132731678298872825165919 3199097517448309237748879)
        ·
          refine ⟨4798646276172463856623319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199097517448309237748879 4798646276172463856623319)
          ·
            refine ⟨7197969414258695784934979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798646276172463856623319 7197969414258695784934979)
            ·
              refine ⟨10796954121388043677402469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197969414258695784934979 10796954121388043677402469)
              ·
                refine ⟨2024428897760258189512963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10796954121388043677402469 2024428897760258189512963)
                ·
                  refine ⟨3036643346640387284269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024428897760258189512963 3036643346640387284269445)
                  ·
                    refine ⟨569370627495072615800521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3036643346640387284269445 569370627495072615800521)
                    ·
                      refine ⟨427027970621304461850391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569370627495072615800521 427027970621304461850391)
                      ·
                        rfl

theorem cell23_831634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_831634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831634 prefixEnd_831634 := by exact prefixLift 831634
  have htrace : WordTrace (prefixWord ++ tailWord_831634) baseStart_831634 baseEnd_831634 := by
    simpa [prefixWord, tailWord_831634, baseEnd_831634] using wordTrace_append hprefix tailTrace_831634
  have hstable : (prefixWord ++ tailWord_831634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831634).length < 2 ^ (prefixWord ++ tailWord_831634).sum := by decide
  have hdescent : baseEnd_831634 < baseStart_831634 := by decide
  rcases family_descends (prefixWord ++ tailWord_831634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831647 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_831647 : Nat := 118140960795 + 831647 * 2 ^ 59
def prefixEnd_831647 : Nat := 4983230072969 + 3 ^ 40 * 831647 * 2
def baseEnd_831647 : Nat := 427034645869812910987831

theorem tailTrace_831647 : CollatzResearch.WordTrace tailWord_831647 prefixEnd_831647 427034645869812910987831 := by
  unfold tailWord_831647
  simp only [CollatzResearch.WordTrace]
  refine ⟨30332658018092427844805195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20221772012061618563203463 30332658018092427844805195)
  ·
    refine ⟨45498987027138641767207793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30332658018092427844805195 45498987027138641767207793)
    ·
      refine ⟨34124240270353981325405845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45498987027138641767207793 34124240270353981325405845)
      ·
        refine ⟨1599573762672842874628399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34124240270353981325405845 1599573762672842874628399)
        ·
          refine ⟨2399360644009264311942599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599573762672842874628399 2399360644009264311942599)
          ·
            refine ⟨3599040966013896467913899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399360644009264311942599 3599040966013896467913899)
            ·
              refine ⟨5398561449020844701870849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599040966013896467913899 5398561449020844701870849)
              ·
                refine ⟨4048921086765633526403137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5398561449020844701870849 4048921086765633526403137)
                ·
                  refine ⟨3036690815074225144802353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4048921086765633526403137 3036690815074225144802353)
                  ·
                    refine ⟨2277518111305668858601765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3036690815074225144802353 2277518111305668858601765)
                    ·
                      refine ⟨427034645869812910987831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2277518111305668858601765 427034645869812910987831)
                      ·
                        rfl

theorem cell23_831647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_831647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831647 prefixEnd_831647 := by exact prefixLift 831647
  have htrace : WordTrace (prefixWord ++ tailWord_831647) baseStart_831647 baseEnd_831647 := by
    simpa [prefixWord, tailWord_831647, baseEnd_831647] using wordTrace_append hprefix tailTrace_831647
  have hstable : (prefixWord ++ tailWord_831647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831647).length < 2 ^ (prefixWord ++ tailWord_831647).sum := by decide
  have hdescent : baseEnd_831647 < baseStart_831647 := by decide
  rcases family_descends (prefixWord ++ tailWord_831647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831708 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 7]
def baseStart_831708 : Nat := 118140960795 + 831708 * 2 ^ 59
def prefixEnd_831708 : Nat := 4983230072969 + 3 ^ 40 * 831708 * 2
def baseEnd_831708 : Nat := 47451774243304130258339

theorem tailTrace_831708 : CollatzResearch.WordTrace tailWord_831708 prefixEnd_831708 47451774243304130258339 := by
  unfold tailWord_831708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167441435435717631387889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20223255247247623508517185 15167441435435717631387889)
  ·
    refine ⟨11375581076576788223540917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15167441435435717631387889 11375581076576788223540917)
    ·
      refine ⟨1066460725929073895956961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11375581076576788223540917 1066460725929073895956961)
      ·
        refine ⟨799845544446805421967721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1066460725929073895956961 799845544446805421967721)
        ·
          refine ⟨599884158335104066475791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799845544446805421967721 599884158335104066475791)
          ·
            refine ⟨899826237502656099713687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599884158335104066475791 899826237502656099713687)
            ·
              refine ⟨1349739356253984149570531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899826237502656099713687 1349739356253984149570531)
              ·
                refine ⟨2024609034380976224355797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349739356253984149570531 2024609034380976224355797)
                ·
                  refine ⟨47451774243304130258339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2024609034380976224355797 47451774243304130258339)
                  ·
                    rfl

theorem cell23_831708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_831708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831708 prefixEnd_831708 := by exact prefixLift 831708
  have htrace : WordTrace (prefixWord ++ tailWord_831708) baseStart_831708 baseEnd_831708 := by
    simpa [prefixWord, tailWord_831708, baseEnd_831708] using wordTrace_append hprefix tailTrace_831708
  have hstable : (prefixWord ++ tailWord_831708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831708).length < 2 ^ (prefixWord ++ tailWord_831708).sum := by decide
  have hdescent : baseEnd_831708 < baseStart_831708 := by decide
  rcases family_descends (prefixWord ++ tailWord_831708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831734 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_831734 : Nat := 118140960795 + 831734 * 2 ^ 59
def prefixEnd_831734 : Nat := 4983230072969 + 3 ^ 40 * 831734 * 2
def baseEnd_831734 : Nat := 142359772895584690199977

theorem tailTrace_831734 : CollatzResearch.WordTrace tailWord_831734 prefixEnd_831734 142359772895584690199977 := by
  unfold tailWord_831734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895989448048577606451391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20223887445851494468814837 1895989448048577606451391)
  ·
    refine ⟨2843984172072866409677087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895989448048577606451391 2843984172072866409677087)
    ·
      refine ⟨4265976258109299614515631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843984172072866409677087 4265976258109299614515631)
      ·
        refine ⟨6398964387163949421773447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265976258109299614515631 6398964387163949421773447)
        ·
          refine ⟨9598446580745924132660171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398964387163949421773447 9598446580745924132660171)
          ·
            refine ⟨14397669871118886198990257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9598446580745924132660171 14397669871118886198990257)
            ·
              refine ⟨10798252403339164649242693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14397669871118886198990257 10798252403339164649242693)
              ·
                refine ⟨2024672325626093371733005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10798252403339164649242693 2024672325626093371733005)
                ·
                  refine ⟨759252122109785014399877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2024672325626093371733005 759252122109785014399877)
                  ·
                    refine ⟨142359772895584690199977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759252122109785014399877 142359772895584690199977)
                    ·
                      rfl

theorem cell23_831734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_831734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831734 prefixEnd_831734 := by exact prefixLift 831734
  have htrace : WordTrace (prefixWord ++ tailWord_831734) baseStart_831734 baseEnd_831734 := by
    simpa [prefixWord, tailWord_831734, baseEnd_831734] using wordTrace_append hprefix tailTrace_831734
  have hstable : (prefixWord ++ tailWord_831734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831734).length < 2 ^ (prefixWord ++ tailWord_831734).sum := by decide
  have hdescent : baseEnd_831734 < baseStart_831734 := by decide
  rcases family_descends (prefixWord ++ tailWord_831734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831777 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_831777 : Nat := 118140960795 + 831777 * 2 ^ 59
def prefixEnd_831777 : Nat := 4983230072969 + 3 ^ 40 * 831777 * 2
def baseEnd_831777 : Nat := 142367132784965800787411

theorem tailTrace_831777 : CollatzResearch.WordTrace tailWord_831777 prefixEnd_831777 142367132784965800787411 := by
  unfold tailWord_831777
  simp only [CollatzResearch.WordTrace]
  refine ⟨30337399507621460047037585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20224933005080973364691723 30337399507621460047037585)
  ·
    refine ⟨22753049630716095035278189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30337399507621460047037585 22753049630716095035278189)
    ·
      refine ⟨8532393611518535638229321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22753049630716095035278189 8532393611518535638229321)
      ·
        refine ⟨6399295208638901728671991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8532393611518535638229321 6399295208638901728671991)
        ·
          refine ⟨9598942812958352593007987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399295208638901728671991 9598942812958352593007987)
          ·
            refine ⟨14398414219437528889511981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9598942812958352593007987 14398414219437528889511981)
            ·
              refine ⟨5399405332289073333566993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14398414219437528889511981 5399405332289073333566993)
              ·
                refine ⟨4049553999216805000175245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5399405332289073333566993 4049553999216805000175245)
                ·
                  refine ⟨1518582749706301875065717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4049553999216805000175245 1518582749706301875065717)
                  ·
                    refine ⟨142367132784965800787411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1518582749706301875065717 142367132784965800787411)
                    ·
                      rfl

theorem cell23_831777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_831777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831777 prefixEnd_831777 := by exact prefixLift 831777
  have htrace : WordTrace (prefixWord ++ tailWord_831777) baseStart_831777 baseEnd_831777 := by
    simpa [prefixWord, tailWord_831777, baseEnd_831777] using wordTrace_append hprefix tailTrace_831777
  have hstable : (prefixWord ++ tailWord_831777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831777).length < 2 ^ (prefixWord ++ tailWord_831777).sum := by decide
  have hdescent : baseEnd_831777 < baseStart_831777 := by decide
  rcases family_descends (prefixWord ++ tailWord_831777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831801 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 1, 5, 2]
def baseStart_831801 : Nat := 118140960795 + 831801 * 2 ^ 59
def prefixEnd_831801 : Nat := 4983230072969 + 3 ^ 40 * 831801 * 2
def baseEnd_831801 : Nat := 427113721890605308462123

theorem tailTrace_831801 : CollatzResearch.WordTrace tailWord_831801 prefixEnd_831801 427113721890605308462123 := by
  unfold tailWord_831801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30338274859534512145911257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20225516573023008097274171 30338274859534512145911257)
  ·
    refine ⟨22753706144650884109433443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30338274859534512145911257 22753706144650884109433443)
    ·
      refine ⟨34130559216976326164150165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22753706144650884109433443 34130559216976326164150165)
      ·
        refine ⟨1599869963295765288944539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34130559216976326164150165 1599869963295765288944539)
        ·
          refine ⟨2399804944943647933416809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599869963295765288944539 2399804944943647933416809)
          ·
            refine ⟨1799853708707735950062607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399804944943647933416809 1799853708707735950062607)
            ·
              refine ⟨2699780563061603925093911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799853708707735950062607 2699780563061603925093911)
              ·
                refine ⟨4049670844592405887640867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699780563061603925093911 4049670844592405887640867)
                ·
                  refine ⟨6074506266888608831461301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049670844592405887640867 6074506266888608831461301)
                  ·
                    refine ⟨569484962520807077949497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6074506266888608831461301 569484962520807077949497)
                    ·
                      refine ⟨427113721890605308462123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569484962520807077949497 427113721890605308462123)
                      ·
                        rfl

theorem cell23_831801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_831801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831801 prefixEnd_831801 := by exact prefixLift 831801
  have htrace : WordTrace (prefixWord ++ tailWord_831801) baseStart_831801 baseEnd_831801 := by
    simpa [prefixWord, tailWord_831801, baseEnd_831801] using wordTrace_append hprefix tailTrace_831801
  have hstable : (prefixWord ++ tailWord_831801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831801).length < 2 ^ (prefixWord ++ tailWord_831801).sum := by decide
  have hdescent : baseEnd_831801 < baseStart_831801 := by decide
  rcases family_descends (prefixWord ++ tailWord_831801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831807 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 1, 6]
def baseStart_831807 : Nat := 118140960795 + 831807 * 2 ^ 59
def prefixEnd_831807 : Nat := 4983230072969 + 3 ^ 40 * 831807 * 2
def baseEnd_831807 : Nat := 142372267591510761662365

theorem tailTrace_831807 : CollatzResearch.WordTrace tailWord_831807 prefixEnd_831807 142372267591510761662365 := by
  unfold tailWord_831807
  simp only [CollatzResearch.WordTrace]
  refine ⟨30338493697512775170629675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20225662465008516780419783 30338493697512775170629675)
  ·
    refine ⟨45507740546269162755944513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30338493697512775170629675 45507740546269162755944513)
    ·
      refine ⟨34130805409701872066958385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45507740546269162755944513 34130805409701872066958385)
      ·
        refine ⟨25598104057276404050218789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34130805409701872066958385 25598104057276404050218789)
        ·
          refine ⟨4799644510739325759416023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25598104057276404050218789 4799644510739325759416023)
          ·
            refine ⟨7199466766108988639124035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799644510739325759416023 7199466766108988639124035)
            ·
              refine ⟨10799200149163482958686053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199466766108988639124035 10799200149163482958686053)
              ·
                refine ⟨2024850027968153054753635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10799200149163482958686053 2024850027968153054753635)
                ·
                  refine ⟨3037275041952229582130453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024850027968153054753635 3037275041952229582130453)
                  ·
                    refine ⟨142372267591510761662365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3037275041952229582130453 142372267591510761662365)
                    ·
                      rfl

theorem cell23_831807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_831807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831807 prefixEnd_831807 := by exact prefixLift 831807
  have htrace : WordTrace (prefixWord ++ tailWord_831807) baseStart_831807 baseEnd_831807 := by
    simpa [prefixWord, tailWord_831807, baseEnd_831807] using wordTrace_append hprefix tailTrace_831807
  have hstable : (prefixWord ++ tailWord_831807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831807).length < 2 ^ (prefixWord ++ tailWord_831807).sum := by decide
  have hdescent : baseEnd_831807 < baseStart_831807 := by decide
  rcases family_descends (prefixWord ++ tailWord_831807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831817 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_831817 : Nat := 118140960795 + 831817 * 2 ^ 59
def prefixEnd_831817 : Nat := 4983230072969 + 3 ^ 40 * 831817 * 2
def baseEnd_831817 : Nat := 427121937581077245862049

theorem tailTrace_831817 : CollatzResearch.WordTrace tailWord_831817 prefixEnd_831817 427121937581077245862049 := by
  unfold tailWord_831817
  simp only [CollatzResearch.WordTrace]
  refine ⟨30338858427476546878493705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20225905618317697918995803 30338858427476546878493705)
  ·
    refine ⟨22754143820607410158870279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30338858427476546878493705 22754143820607410158870279)
    ·
      refine ⟨34131215730911115238305419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22754143820607410158870279 34131215730911115238305419)
      ·
        refine ⟨51196823596366672857458129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34131215730911115238305419 51196823596366672857458129)
        ·
          refine ⟨38397617697275004643093597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51196823596366672857458129 38397617697275004643093597)
          ·
            refine ⟨14399106636478126741160099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38397617697275004643093597 14399106636478126741160099)
            ·
              refine ⟨21598659954717190111740149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399106636478126741160099 21598659954717190111740149)
              ·
                refine ⟨2024874370754736572975639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21598659954717190111740149 2024874370754736572975639)
                ·
                  refine ⟨3037311556132104859463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024874370754736572975639 3037311556132104859463459)
                  ·
                    refine ⟨4555967334198157289195189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3037311556132104859463459 4555967334198157289195189)
                    ·
                      refine ⟨427121937581077245862049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4555967334198157289195189 427121937581077245862049)
                      ·
                        rfl

theorem cell23_831817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_831817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831817 prefixEnd_831817 := by exact prefixLift 831817
  have htrace : WordTrace (prefixWord ++ tailWord_831817) baseStart_831817 baseEnd_831817 := by
    simpa [prefixWord, tailWord_831817, baseEnd_831817] using wordTrace_append hprefix tailTrace_831817
  have hstable : (prefixWord ++ tailWord_831817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831817).length < 2 ^ (prefixWord ++ tailWord_831817).sum := by decide
  have hdescent : baseEnd_831817 < baseStart_831817 := by decide
  rcases family_descends (prefixWord ++ tailWord_831817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831824 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 4, 4]
def baseStart_831824 : Nat := 118140960795 + 831824 * 2 ^ 59
def prefixEnd_831824 : Nat := 4983230072969 + 3 ^ 40 * 831824 * 2
def baseEnd_831824 : Nat := 142375177315219572824839

theorem tailTrace_831824 : CollatzResearch.WordTrace tailWord_831824 prefixEnd_831824 142375177315219572824839 := by
  unfold tailWord_831824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169556869225593536999263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20226075825634124715999017 15169556869225593536999263)
  ·
    refine ⟨22754335303838390305498895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15169556869225593536999263 22754335303838390305498895)
    ·
      refine ⟨34131502955757585458248343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22754335303838390305498895 34131502955757585458248343)
      ·
        refine ⟨51197254433636378187372515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34131502955757585458248343 51197254433636378187372515)
        ·
          refine ⟨76795881650454567281058773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51197254433636378187372515 76795881650454567281058773)
          ·
            refine ⟨1799903476182528920649815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 76795881650454567281058773 1799903476182528920649815)
            ·
              refine ⟨2699855214273793380974723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799903476182528920649815 2699855214273793380974723)
              ·
                refine ⟨4049782821410690071462085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699855214273793380974723 4049782821410690071462085)
                ·
                  refine ⟨759334279014504388399141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4049782821410690071462085 759334279014504388399141)
                  ·
                    refine ⟨142375177315219572824839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759334279014504388399141 142375177315219572824839)
                    ·
                      rfl

theorem cell23_831824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_831824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831824 prefixEnd_831824 := by exact prefixLift 831824
  have htrace : WordTrace (prefixWord ++ tailWord_831824) baseStart_831824 baseEnd_831824 := by
    simpa [prefixWord, tailWord_831824, baseEnd_831824] using wordTrace_append hprefix tailTrace_831824
  have hstable : (prefixWord ++ tailWord_831824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831824).length < 2 ^ (prefixWord ++ tailWord_831824).sum := by decide
  have hdescent : baseEnd_831824 < baseStart_831824 := by decide
  rcases family_descends (prefixWord ++ tailWord_831824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831848 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_831848 : Nat := 118140960795 + 831848 * 2 ^ 59
def prefixEnd_831848 : Nat := 4983230072969 + 3 ^ 40 * 831848 * 2
def baseEnd_831848 : Nat := 427137855481366624574407

theorem tailTrace_831848 : CollatzResearch.WordTrace tailWord_831848 prefixEnd_831848 427137855481366624574407 := by
  unfold tailWord_831848
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169994545182119586436099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20226659393576159448581465 15169994545182119586436099)
  ·
    refine ⟨22754991817773179379654149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15169994545182119586436099 22754991817773179379654149)
    ·
      refine ⟨4266560965832471133685153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22754991817773179379654149 4266560965832471133685153)
      ·
        refine ⟨3199920724374353350263865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4266560965832471133685153 3199920724374353350263865)
        ·
          refine ⟨2399940543280765012697899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3199920724374353350263865 2399940543280765012697899)
          ·
            refine ⟨3599910814921147519046849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399940543280765012697899 3599910814921147519046849)
            ·
              refine ⟨2699933111190860639285137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599910814921147519046849 2699933111190860639285137)
              ·
                refine ⟨2024949833393145479463853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699933111190860639285137 2024949833393145479463853)
                ·
                  refine ⟨759356187522429554798945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2024949833393145479463853 759356187522429554798945)
                  ·
                    refine ⟨569517140641822166099209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759356187522429554798945 569517140641822166099209)
                    ·
                      refine ⟨427137855481366624574407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569517140641822166099209 427137855481366624574407)
                      ·
                        rfl

theorem cell23_831848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_831848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831848 prefixEnd_831848 := by exact prefixLift 831848
  have htrace : WordTrace (prefixWord ++ tailWord_831848) baseStart_831848 baseEnd_831848 := by
    simpa [prefixWord, tailWord_831848, baseEnd_831848] using wordTrace_append hprefix tailTrace_831848
  have hstable : (prefixWord ++ tailWord_831848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831848).length < 2 ^ (prefixWord ++ tailWord_831848).sum := by decide
  have hdescent : baseEnd_831848 < baseStart_831848 := by decide
  rcases family_descends (prefixWord ++ tailWord_831848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831877 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_831877 : Nat := 118140960795 + 831877 * 2 ^ 59
def prefixEnd_831877 : Nat := 4983230072969 + 3 ^ 40 * 831877 * 2
def baseEnd_831877 : Nat := 427152746420347011111773

theorem tailTrace_831877 : CollatzResearch.WordTrace tailWord_831877 prefixEnd_831877 427152746420347011111773 := by
  unfold tailWord_831877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30341046807259177125677885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20227364538172784750451923 30341046807259177125677885)
  ·
    refine ⟨11377892552722191422129207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30341046807259177125677885 11377892552722191422129207)
    ·
      refine ⟨17066838829083287133193811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11377892552722191422129207 17066838829083287133193811)
      ·
        refine ⟨25600258243624930699790717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17066838829083287133193811 25600258243624930699790717)
        ·
          refine ⟨9600096841359349012421519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25600258243624930699790717 9600096841359349012421519)
          ·
            refine ⟨14400145262039023518632279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600096841359349012421519 14400145262039023518632279)
            ·
              refine ⟨21600217893058535277948419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14400145262039023518632279 21600217893058535277948419)
              ·
                refine ⟨32400326839587802916922629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21600217893058535277948419 32400326839587802916922629)
                ·
                  refine ⟨6075061282422713046922993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32400326839587802916922629 6075061282422713046922993)
                  ·
                    refine ⟨4556295961817034785192245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075061282422713046922993 4556295961817034785192245)
                    ·
                      refine ⟨427152746420347011111773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4556295961817034785192245 427152746420347011111773)
                      ·
                        rfl

theorem cell23_831877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_831877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831877 prefixEnd_831877 := by exact prefixLift 831877
  have htrace : WordTrace (prefixWord ++ tailWord_831877) baseStart_831877 baseEnd_831877 := by
    simpa [prefixWord, tailWord_831877, baseEnd_831877] using wordTrace_append hprefix tailTrace_831877
  have hstable : (prefixWord ++ tailWord_831877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831877).length < 2 ^ (prefixWord ++ tailWord_831877).sum := by decide
  have hdescent : baseEnd_831877 < baseStart_831877 := by decide
  rcases family_descends (prefixWord ++ tailWord_831877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831881 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 3]
def baseStart_831881 : Nat := 118140960795 + 831881 * 2 ^ 59
def prefixEnd_831881 : Nat := 4983230072969 + 3 ^ 40 * 831881 * 2
def baseEnd_831881 : Nat := 427154800342964995461755

theorem tailTrace_831881 : CollatzResearch.WordTrace tailWord_831881 prefixEnd_831881 427154800342964995461755 := by
  unfold tailWord_831881
  simp only [CollatzResearch.WordTrace]
  refine ⟨30341192699244685808823497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20227461799496457205882331 30341192699244685808823497)
  ·
    refine ⟨22755894524433514356617623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30341192699244685808823497 22755894524433514356617623)
    ·
      refine ⟨34133841786650271534926435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22755894524433514356617623 34133841786650271534926435)
      ·
        refine ⟨51200762679975407302389653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34133841786650271534926435 51200762679975407302389653)
        ·
          refine ⟨2400035750623847217299515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51200762679975407302389653 2400035750623847217299515)
          ·
            refine ⟨3600053625935770825949273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400035750623847217299515 3600053625935770825949273)
            ·
              refine ⟨2700040219451828119461955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600053625935770825949273 2700040219451828119461955)
              ·
                refine ⟨4050060329177742179192933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700040219451828119461955 4050060329177742179192933)
                ·
                  refine ⟨759386311720826658598675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4050060329177742179192933 759386311720826658598675)
                  ·
                    refine ⟨1139079467581239987898013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 759386311720826658598675 1139079467581239987898013)
                    ·
                      refine ⟨427154800342964995461755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139079467581239987898013 427154800342964995461755)
                      ·
                        rfl

theorem cell23_831881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_831881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831881 prefixEnd_831881 := by exact prefixLift 831881
  have htrace : WordTrace (prefixWord ++ tailWord_831881) baseStart_831881 baseEnd_831881 := by
    simpa [prefixWord, tailWord_831881, baseEnd_831881] using wordTrace_append hprefix tailTrace_831881
  have hstable : (prefixWord ++ tailWord_831881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831881).length < 2 ^ (prefixWord ++ tailWord_831881).sum := by decide
  have hdescent : baseEnd_831881 < baseStart_831881 := by decide
  rcases family_descends (prefixWord ++ tailWord_831881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831882 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_831882 : Nat := 118140960795 + 831882 * 2 ^ 59
def prefixEnd_831882 : Nat := 4983230072969 + 3 ^ 40 * 831882 * 2
def baseEnd_831882 : Nat := 427155313823619491549251

theorem tailTrace_831882 : CollatzResearch.WordTrace tailWord_831882 prefixEnd_831882 427155313823619491549251 := by
  unfold tailWord_831882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585307293060265744902475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20227486114827375319739933 7585307293060265744902475)
  ·
    refine ⟨11377960939590398617353713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7585307293060265744902475 11377960939590398617353713)
    ·
      refine ⟨8533470704692798963015285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11377960939590398617353713 8533470704692798963015285)
      ·
        refine ⟨800012878564949902782683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8533470704692798963015285 800012878564949902782683)
        ·
          refine ⟨1200019317847424854174025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800012878564949902782683 1200019317847424854174025)
          ·
            refine ⟨900014488385568640630519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200019317847424854174025 900014488385568640630519)
            ·
              refine ⟨1350021732578352960945779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900014488385568640630519 1350021732578352960945779)
              ·
                refine ⟨2025032598867529441418669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350021732578352960945779 2025032598867529441418669)
                ·
                  refine ⟨759387224575323540532001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2025032598867529441418669 759387224575323540532001)
                  ·
                    refine ⟨569540418431492655399001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759387224575323540532001 569540418431492655399001)
                    ·
                      refine ⟨427155313823619491549251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569540418431492655399001 427155313823619491549251)
                      ·
                        rfl

theorem cell23_831882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_831882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831882 prefixEnd_831882 := by exact prefixLift 831882
  have htrace : WordTrace (prefixWord ++ tailWord_831882) baseStart_831882 baseEnd_831882 := by
    simpa [prefixWord, tailWord_831882, baseEnd_831882] using wordTrace_append hprefix tailTrace_831882
  have hstable : (prefixWord ++ tailWord_831882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831882).length < 2 ^ (prefixWord ++ tailWord_831882).sum := by decide
  have hdescent : baseEnd_831882 < baseStart_831882 := by decide
  rcases family_descends (prefixWord ++ tailWord_831882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831892 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_831892 : Nat := 118140960795 + 831892 * 2 ^ 59
def prefixEnd_831892 : Nat := 4983230072969 + 3 ^ 40 * 831892 * 2
def baseEnd_831892 : Nat := 142386816210054817474735

theorem tailTrace_831892 : CollatzResearch.WordTrace tailWord_831892 prefixEnd_831892 142386816210054817474735 := by
  unfold tailWord_831892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170796951102417343736965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20227729268136556458315953 15170796951102417343736965)
  ·
    refine ⟨2844524428331703251950681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15170796951102417343736965 2844524428331703251950681)
    ·
      refine ⟨2133393321248777438963011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2844524428331703251950681 2133393321248777438963011)
      ·
        refine ⟨3200089981873166158444517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133393321248777438963011 3200089981873166158444517)
        ·
          refine ⟨600016871601218654708347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3200089981873166158444517 600016871601218654708347)
          ·
            refine ⟨900025307401827982062521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600016871601218654708347 900025307401827982062521)
            ·
              refine ⟨675018980551370986546891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900025307401827982062521 675018980551370986546891)
              ·
                refine ⟨1012528470827056479820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675018980551370986546891 1012528470827056479820337)
                ·
                  refine ⟨759396353120292359865253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012528470827056479820337 759396353120292359865253)
                  ·
                    refine ⟨142386816210054817474735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759396353120292359865253 142386816210054817474735)
                    ·
                      rfl

theorem cell23_831892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_831892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831892 prefixEnd_831892 := by exact prefixLift 831892
  have htrace : WordTrace (prefixWord ++ tailWord_831892) baseStart_831892 baseEnd_831892 := by
    simpa [prefixWord, tailWord_831892, baseEnd_831892] using wordTrace_append hprefix tailTrace_831892
  have hstable : (prefixWord ++ tailWord_831892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831892).length < 2 ^ (prefixWord ++ tailWord_831892).sum := by decide
  have hdescent : baseEnd_831892 < baseStart_831892 := by decide
  rcases family_descends (prefixWord ++ tailWord_831892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831897 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_831897 : Nat := 118140960795 + 831897 * 2 ^ 59
def prefixEnd_831897 : Nat := 4983230072969 + 3 ^ 40 * 831897 * 2
def baseEnd_831897 : Nat := 142387672011145644287227

theorem tailTrace_831897 : CollatzResearch.WordTrace tailWord_831897 prefixEnd_831897 142387672011145644287227 := by
  unfold tailWord_831897
  simp only [CollatzResearch.WordTrace]
  refine ⟨30341776267186720541405945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20227850844791147027603963 30341776267186720541405945)
  ·
    refine ⟨22756332200390040406054459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30341776267186720541405945 22756332200390040406054459)
    ·
      refine ⟨34134498300585060609081689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22756332200390040406054459 34134498300585060609081689)
      ·
        refine ⟨25600873725438795456811267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34134498300585060609081689 25600873725438795456811267)
        ·
          refine ⟨38401310588158193185216901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25600873725438795456811267 38401310588158193185216901)
          ·
            refine ⟨7200245735279661222228169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38401310588158193185216901 7200245735279661222228169)
            ·
              refine ⟨5400184301459745916671127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7200245735279661222228169 5400184301459745916671127)
              ·
                refine ⟨8100276452189618875006691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400184301459745916671127 8100276452189618875006691)
                ·
                  refine ⟨12150414678284428312510037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8100276452189618875006691 12150414678284428312510037)
                  ·
                    refine ⟨142387672011145644287227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12150414678284428312510037 142387672011145644287227)
                    ·
                      rfl

theorem cell23_831897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_831897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831897 prefixEnd_831897 := by exact prefixLift 831897
  have htrace : WordTrace (prefixWord ++ tailWord_831897) baseStart_831897 baseEnd_831897 := by
    simpa [prefixWord, tailWord_831897, baseEnd_831897] using wordTrace_append hprefix tailTrace_831897
  have hstable : (prefixWord ++ tailWord_831897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831897).length < 2 ^ (prefixWord ++ tailWord_831897).sum := by decide
  have hdescent : baseEnd_831897 < baseStart_831897 := by decide
  rcases family_descends (prefixWord ++ tailWord_831897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831898 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_831898 : Nat := 118140960795 + 831898 * 2 ^ 59
def prefixEnd_831898 : Nat := 4983230072969 + 3 ^ 40 * 831898 * 2
def baseEnd_831898 : Nat := 427163529514091428949177

theorem tailTrace_831898 : CollatzResearch.WordTrace tailWord_831898 prefixEnd_831898 427163529514091428949177 := by
  unfold tailWord_831898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585453185045774428048087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20227875160122065141461565 7585453185045774428048087)
  ·
    refine ⟨11378179777568661642072131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7585453185045774428048087 11378179777568661642072131)
    ·
      refine ⟨17067269666352992463108197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11378179777568661642072131 17067269666352992463108197)
      ·
        refine ⟨3200113062441186086832787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17067269666352992463108197 3200113062441186086832787)
        ·
          refine ⟨4800169593661779130249181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200113062441186086832787 4800169593661779130249181)
          ·
            refine ⟨1800063597623167173843443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4800169593661779130249181 1800063597623167173843443)
            ·
              refine ⟨2700095396434750760765165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800063597623167173843443 2700095396434750760765165)
              ·
                refine ⟨1012535773663031535286937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700095396434750760765165 1012535773663031535286937)
                ·
                  refine ⟨759401830247273651465203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012535773663031535286937 759401830247273651465203)
                  ·
                    refine ⟨1139102745370910477197805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 759401830247273651465203 1139102745370910477197805)
                    ·
                      refine ⟨427163529514091428949177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139102745370910477197805 427163529514091428949177)
                      ·
                        rfl

theorem cell23_831898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_831898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831898 prefixEnd_831898 := by exact prefixLift 831898
  have htrace : WordTrace (prefixWord ++ tailWord_831898) baseStart_831898 baseEnd_831898 := by
    simpa [prefixWord, tailWord_831898, baseEnd_831898] using wordTrace_append hprefix tailTrace_831898
  have hstable : (prefixWord ++ tailWord_831898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831898).length < 2 ^ (prefixWord ++ tailWord_831898).sum := by decide
  have hdescent : baseEnd_831898 < baseStart_831898 := by decide
  rcases family_descends (prefixWord ++ tailWord_831898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831908 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_831908 : Nat := 118140960795 + 831908 * 2 ^ 59
def prefixEnd_831908 : Nat := 4983230072969 + 3 ^ 40 * 831908 * 2
def baseEnd_831908 : Nat := 427168664320636389824131

theorem tailTrace_831908 : CollatzResearch.WordTrace tailWord_831908 prefixEnd_831908 427168664320636389824131 := by
  unfold tailWord_831908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171088735073434710028189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20228118313431246280037585 15171088735073434710028189)
  ·
    refine ⟨5689158275652538016260571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15171088735073434710028189 5689158275652538016260571)
    ·
      refine ⟨8533737413478807024390857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689158275652538016260571 8533737413478807024390857)
      ·
        refine ⟨6400303060109105268293143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8533737413478807024390857 6400303060109105268293143)
        ·
          refine ⟨9600454590163657902439715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6400303060109105268293143 9600454590163657902439715)
          ·
            refine ⟨14400681885245486853659573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600454590163657902439715 14400681885245486853659573)
            ·
              refine ⟨1350063926741764392530585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14400681885245486853659573 1350063926741764392530585)
              ·
                refine ⟨1012547945056323294397939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350063926741764392530585 1012547945056323294397939)
                ·
                  refine ⟨1518821917584484941596909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012547945056323294397939 1518821917584484941596909)
                  ·
                    refine ⟨569558219094181853098841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1518821917584484941596909 569558219094181853098841)
                    ·
                      refine ⟨427168664320636389824131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569558219094181853098841 427168664320636389824131)
                      ·
                        rfl

theorem cell23_831908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_831908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831908 prefixEnd_831908 := by exact prefixLift 831908
  have htrace : WordTrace (prefixWord ++ tailWord_831908) baseStart_831908 baseEnd_831908 := by
    simpa [prefixWord, tailWord_831908, baseEnd_831908] using wordTrace_append hprefix tailTrace_831908
  have hstable : (prefixWord ++ tailWord_831908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831908).length < 2 ^ (prefixWord ++ tailWord_831908).sum := by decide
  have hdescent : baseEnd_831908 < baseStart_831908 := by decide
  rcases family_descends (prefixWord ++ tailWord_831908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831921 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 3, 4, 2]
def baseStart_831921 : Nat := 118140960795 + 831921 * 2 ^ 59
def prefixEnd_831921 : Nat := 4983230072969 + 3 ^ 40 * 831921 * 2
def baseEnd_831921 : Nat := 427175339569144838961571

theorem tailTrace_831921 : CollatzResearch.WordTrace tailWord_831921 prefixEnd_831921 427175339569144838961571 := by
  unfold tailWord_831921
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342651619099772640279617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20228434412733181760186411 30342651619099772640279617)
  ·
    refine ⟨22756988714324829480209713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30342651619099772640279617 22756988714324829480209713)
    ·
      refine ⟨17067741535743622110157285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22756988714324829480209713 17067741535743622110157285)
      ·
        refine ⟨3200201537951929145654491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17067741535743622110157285 3200201537951929145654491)
        ·
          refine ⟨4800302306927893718481737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200201537951929145654491 4800302306927893718481737)
          ·
            refine ⟨3600226730195920288861303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4800302306927893718481737 3600226730195920288861303)
            ·
              refine ⟨5400340095293880433291955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600226730195920288861303 5400340095293880433291955)
              ·
                refine ⟨8100510142940820649937933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400340095293880433291955 8100510142940820649937933)
                ·
                  refine ⟨3037691303602807743726725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8100510142940820649937933 3037691303602807743726725)
                  ·
                    refine ⟨569567119425526451948761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037691303602807743726725 569567119425526451948761)
                    ·
                      refine ⟨427175339569144838961571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569567119425526451948761 427175339569144838961571)
                      ·
                        rfl

theorem cell23_831921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_831921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831921 prefixEnd_831921 := by exact prefixLift 831921
  have htrace : WordTrace (prefixWord ++ tailWord_831921) baseStart_831921 baseEnd_831921 := by
    simpa [prefixWord, tailWord_831921, baseEnd_831921] using wordTrace_append hprefix tailTrace_831921
  have hstable : (prefixWord ++ tailWord_831921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831921).length < 2 ^ (prefixWord ++ tailWord_831921).sum := by decide
  have hdescent : baseEnd_831921 < baseStart_831921 := by decide
  rcases family_descends (prefixWord ++ tailWord_831921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831947 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_831947 : Nat := 118140960795 + 831947 * 2 ^ 59
def prefixEnd_831947 : Nat := 4983230072969 + 3 ^ 40 * 831947 * 2
def baseEnd_831947 : Nat := 427188690066161737236451

theorem tailTrace_831947 : CollatzResearch.WordTrace tailWord_831947 prefixEnd_831947 427188690066161737236451 := by
  unfold tailWord_831947
  simp only [CollatzResearch.WordTrace]
  refine ⟨30343599917005579080726095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20229066611337052720484063 30343599917005579080726095)
  ·
    refine ⟨45515399875508368621089143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30343599917005579080726095 45515399875508368621089143)
    ·
      refine ⟨68273099813262552931633715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45515399875508368621089143 68273099813262552931633715)
      ·
        refine ⟨102409649719893829397450573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68273099813262552931633715 102409649719893829397450573)
        ·
          refine ⟨38403618644960186024043965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102409649719893829397450573 38403618644960186024043965)
          ·
            refine ⟨14401356991860069759016487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38403618644960186024043965 14401356991860069759016487)
            ·
              refine ⟨21602035487790104638524731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14401356991860069759016487 21602035487790104638524731)
              ·
                refine ⟨32403053231685156957787097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21602035487790104638524731 32403053231685156957787097)
                ·
                  refine ⟨24302289923763867718340323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32403053231685156957787097 24302289923763867718340323)
                  ·
                    refine ⟨36453434885645801577510485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24302289923763867718340323 36453434885645801577510485)
                    ·
                      refine ⟨427188690066161737236451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36453434885645801577510485 427188690066161737236451)
                      ·
                        rfl

theorem cell23_831947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_831947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831947 prefixEnd_831947 := by exact prefixLift 831947
  have htrace : WordTrace (prefixWord ++ tailWord_831947) baseStart_831947 baseEnd_831947 := by
    simpa [prefixWord, tailWord_831947, baseEnd_831947] using wordTrace_append hprefix tailTrace_831947
  have hstable : (prefixWord ++ tailWord_831947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831947).length < 2 ^ (prefixWord ++ tailWord_831947).sum := by decide
  have hdescent : baseEnd_831947 < baseStart_831947 := by decide
  rcases family_descends (prefixWord ++ tailWord_831947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831978 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_831978 : Nat := 118140960795 + 831978 * 2 ^ 59
def prefixEnd_831978 : Nat := 4983230072969 + 3 ^ 40 * 831978 * 2
def baseEnd_831978 : Nat := 47467178662939012883201

theorem tailTrace_831978 : CollatzResearch.WordTrace tailWord_831978 prefixEnd_831978 47467178662939012883201 := by
  unfold tailWord_831978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586182644973317843776147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20229820386595514250069725 7586182644973317843776147)
  ·
    refine ⟨11379273967459976765664221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7586182644973317843776147 11379273967459976765664221)
    ·
      refine ⟨4267227737797491287124083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11379273967459976765664221 4267227737797491287124083)
      ·
        refine ⟨6400841606696236930686125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267227737797491287124083 6400841606696236930686125)
        ·
          refine ⟨2400315602511088849007297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6400841606696236930686125 2400315602511088849007297)
          ·
            refine ⟨1800236701883316636755473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400315602511088849007297 1800236701883316636755473)
            ·
              refine ⟨1350177526412487477566605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800236701883316636755473 1350177526412487477566605)
              ·
                refine ⟨506316572404682804087477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350177526412487477566605 506316572404682804087477)
                ·
                  refine ⟨47467178662939012883201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 506316572404682804087477 47467178662939012883201)
                  ·
                    rfl

theorem cell23_831978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_831978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831978 prefixEnd_831978 := by exact prefixLift 831978
  have htrace : WordTrace (prefixWord ++ tailWord_831978) baseStart_831978 baseEnd_831978 := by
    simpa [prefixWord, tailWord_831978, baseEnd_831978] using wordTrace_append hprefix tailTrace_831978
  have hstable : (prefixWord ++ tailWord_831978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831978).length < 2 ^ (prefixWord ++ tailWord_831978).sum := by decide
  have hdescent : baseEnd_831978 < baseStart_831978 := by decide
  rcases family_descends (prefixWord ++ tailWord_831978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831989 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_831989 : Nat := 118140960795 + 831989 * 2 ^ 59
def prefixEnd_831989 : Nat := 4983230072969 + 3 ^ 40 * 831989 * 2
def baseEnd_831989 : Nat := 427210256253650572911259

theorem tailTrace_831989 : CollatzResearch.WordTrace tailWord_831989 prefixEnd_831989 427210256253650572911259 := by
  unfold tailWord_831989
  simp only [CollatzResearch.WordTrace]
  refine ⟨30345131782853420253755021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20230087855235613502503347 30345131782853420253755021)
  ·
    refine ⟨11379424418570032595158133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30345131782853420253755021 11379424418570032595158133)
    ·
      refine ⟨1066821039240940555796075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11379424418570032595158133 1066821039240940555796075)
      ·
        refine ⟨1600231558861410833694113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066821039240940555796075 1600231558861410833694113)
        ·
          refine ⟨1200173669146058125270585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1600231558861410833694113 1200173669146058125270585)
          ·
            refine ⟨900130251859543593952939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200173669146058125270585 900130251859543593952939)
            ·
              refine ⟨1350195377789315390929409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900130251859543593952939 1350195377789315390929409)
              ·
                refine ⟨1012646533341986543197057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350195377789315390929409 1012646533341986543197057)
                ·
                  refine ⟨759484900006489907397793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012646533341986543197057 759484900006489907397793)
                  ·
                    refine ⟨569613675004867430548345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759484900006489907397793 569613675004867430548345)
                    ·
                      refine ⟨427210256253650572911259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569613675004867430548345 427210256253650572911259)
                      ·
                        rfl

theorem cell23_831989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_831989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_831989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_831989 prefixEnd_831989 := by exact prefixLift 831989
  have htrace : WordTrace (prefixWord ++ tailWord_831989) baseStart_831989 baseEnd_831989 := by
    simpa [prefixWord, tailWord_831989, baseEnd_831989] using wordTrace_append hprefix tailTrace_831989
  have hstable : (prefixWord ++ tailWord_831989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831989).length < 2 ^ (prefixWord ++ tailWord_831989).sum := by decide
  have hdescent : baseEnd_831989 < baseStart_831989 := by decide
  rcases family_descends (prefixWord ++ tailWord_831989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832021 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_832021 : Nat := 118140960795 + 832021 * 2 ^ 59
def prefixEnd_832021 : Nat := 4983230072969 + 3 ^ 40 * 832021 * 2
def baseEnd_832021 : Nat := 142408895878198149237037

theorem tailTrace_832021 : CollatzResearch.WordTrace tailWord_832021 prefixEnd_832021 142408895878198149237037 := by
  unfold tailWord_832021
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346298918737489718919917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20230865945824993145946611 30346298918737489718919917)
  ·
    refine ⟨11379862094526558644594969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30346298918737489718919917 11379862094526558644594969)
    ·
      refine ⟨8534896570894918983446227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11379862094526558644594969 8534896570894918983446227)
      ·
        refine ⟨12802344856342378475169341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534896570894918983446227 12802344856342378475169341)
        ·
          refine ⟨4800879321128391928188503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12802344856342378475169341 4800879321128391928188503)
          ·
            refine ⟨7201318981692587892282755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800879321128391928188503 7201318981692587892282755)
            ·
              refine ⟨10801978472538881838424133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201318981692587892282755 10801978472538881838424133)
              ·
                refine ⟨2025370963601040344704525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10801978472538881838424133 2025370963601040344704525)
                ·
                  refine ⟨759514111350390129264197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2025370963601040344704525 759514111350390129264197)
                  ·
                    refine ⟨142408895878198149237037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759514111350390129264197 142408895878198149237037)
                    ·
                      rfl

theorem cell23_832021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_832021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832021 prefixEnd_832021 := by exact prefixLift 832021
  have htrace : WordTrace (prefixWord ++ tailWord_832021) baseStart_832021 baseEnd_832021 := by
    simpa [prefixWord, tailWord_832021, baseEnd_832021] using wordTrace_append hprefix tailTrace_832021
  have hstable : (prefixWord ++ tailWord_832021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832021).length < 2 ^ (prefixWord ++ tailWord_832021).sum := by decide
  have hdescent : baseEnd_832021 < baseStart_832021 := by decide
  rcases family_descends (prefixWord ++ tailWord_832021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832031 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_832031 : Nat := 118140960795 + 832031 * 2 ^ 59
def prefixEnd_832031 : Nat := 4983230072969 + 3 ^ 40 * 832031 * 2
def baseEnd_832031 : Nat := 427231822441139408586065

theorem tailTrace_832031 : CollatzResearch.WordTrace tailWord_832031 prefixEnd_832031 427231822441139408586065 := by
  unfold tailWord_832031
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346663648701261426783947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20231109099134174284522631 30346663648701261426783947)
  ·
    refine ⟨45519995473051892140175921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30346663648701261426783947 45519995473051892140175921)
    ·
      refine ⟨34139996604788919105131941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45519995473051892140175921 34139996604788919105131941)
      ·
        refine ⟨6401249363397922332212239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34139996604788919105131941 6401249363397922332212239)
        ·
          refine ⟨9601874045096883498318359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401249363397922332212239 9601874045096883498318359)
          ·
            refine ⟨14402811067645325247477539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9601874045096883498318359 14402811067645325247477539)
            ·
              refine ⟨21604216601467987871216309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14402811067645325247477539 21604216601467987871216309)
              ·
                refine ⟨2025395306387623862926529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21604216601467987871216309 2025395306387623862926529)
                ·
                  refine ⟨1519046479790717897194897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2025395306387623862926529 1519046479790717897194897)
                  ·
                    refine ⟨1139284859843038422896173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1519046479790717897194897 1139284859843038422896173)
                    ·
                      refine ⟨427231822441139408586065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139284859843038422896173 427231822441139408586065)
                      ·
                        rfl

theorem cell23_832031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_832031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832031 prefixEnd_832031 := by exact prefixLift 832031
  have htrace : WordTrace (prefixWord ++ tailWord_832031) baseStart_832031 baseEnd_832031 := by
    simpa [prefixWord, tailWord_832031, baseEnd_832031] using wordTrace_append hprefix tailTrace_832031
  have hstable : (prefixWord ++ tailWord_832031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832031).length < 2 ^ (prefixWord ++ tailWord_832031).sum := by decide
  have hdescent : baseEnd_832031 < baseStart_832031 := by decide
  rcases family_descends (prefixWord ++ tailWord_832031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832055 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 1, 4]
def baseStart_832055 : Nat := 118140960795 + 832055 * 2 ^ 59
def prefixEnd_832055 : Nat := 4983230072969 + 3 ^ 40 * 832055 * 2
def baseEnd_832055 : Nat := 142414715325615771561985

theorem tailTrace_832055 : CollatzResearch.WordTrace tailWord_832055 prefixEnd_832055 142414715325615771561985 := by
  unfold tailWord_832055
  simp only [CollatzResearch.WordTrace]
  refine ⟨30347539000614313525657619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20231692667076209017105079 30347539000614313525657619)
  ·
    refine ⟨45521308500921470288486429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30347539000614313525657619 45521308500921470288486429)
    ·
      refine ⟨17070490687845551358182411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45521308500921470288486429 17070490687845551358182411)
      ·
        refine ⟨25605736031768327037273617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070490687845551358182411 25605736031768327037273617)
        ·
          refine ⟨19204302023826245277955213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25605736031768327037273617 19204302023826245277955213)
          ·
            refine ⟨7201613258934841979233205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19204302023826245277955213 7201613258934841979233205)
            ·
              refine ⟨675151243025141435553113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7201613258934841979233205 675151243025141435553113)
              ·
                refine ⟨506363432268856076664835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675151243025141435553113 506363432268856076664835)
                ·
                  refine ⟨759545148403284114997253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506363432268856076664835 759545148403284114997253)
                  ·
                    refine ⟨142414715325615771561985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759545148403284114997253 142414715325615771561985)
                    ·
                      rfl

theorem cell23_832055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_832055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832055 prefixEnd_832055 := by exact prefixLift 832055
  have htrace : WordTrace (prefixWord ++ tailWord_832055) baseStart_832055 baseEnd_832055 := by
    simpa [prefixWord, tailWord_832055, baseEnd_832055] using wordTrace_append hprefix tailTrace_832055
  have hstable : (prefixWord ++ tailWord_832055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832055).length < 2 ^ (prefixWord ++ tailWord_832055).sum := by decide
  have hdescent : baseEnd_832055 < baseStart_832055 := by decide
  rcases family_descends (prefixWord ++ tailWord_832055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832078 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_832078 : Nat := 118140960795 + 832078 * 2 ^ 59
def prefixEnd_832078 : Nat := 4983230072969 + 3 ^ 40 * 832078 * 2
def baseEnd_832078 : Nat := 427255956031900724698349

theorem tailTrace_832078 : CollatzResearch.WordTrace tailWord_832078 prefixEnd_832078 427255956031900724698349 := by
  unfold tailWord_832078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3793547234941373556718111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20232251919687325635829925 3793547234941373556718111)
  ·
    refine ⟨5690320852412060335077167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3793547234941373556718111 5690320852412060335077167)
    ·
      refine ⟨8535481278618090502615751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5690320852412060335077167 8535481278618090502615751)
      ·
        refine ⟨12803221917927135753923627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8535481278618090502615751 12803221917927135753923627)
        ·
          refine ⟨19204832876890703630885441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12803221917927135753923627 19204832876890703630885441)
          ·
            refine ⟨14403624657668027723164081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19204832876890703630885441 14403624657668027723164081)
            ·
              refine ⟨10802718493251020792373061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14403624657668027723164081 10802718493251020792373061)
              ·
                refine ⟨2025509717484566398569949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10802718493251020792373061 2025509717484566398569949)
                ·
                  refine ⟨759566144056712399463731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2025509717484566398569949 759566144056712399463731)
                  ·
                    refine ⟨1139349216085068599195597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 759566144056712399463731 1139349216085068599195597)
                    ·
                      refine ⟨427255956031900724698349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139349216085068599195597 427255956031900724698349)
                      ·
                        rfl

theorem cell23_832078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_832078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832078 prefixEnd_832078 := by exact prefixLift 832078
  have htrace : WordTrace (prefixWord ++ tailWord_832078) baseStart_832078 baseEnd_832078 := by
    simpa [prefixWord, tailWord_832078, baseEnd_832078] using wordTrace_append hprefix tailTrace_832078
  have hstable : (prefixWord ++ tailWord_832078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832078).length < 2 ^ (prefixWord ++ tailWord_832078).sum := by decide
  have hdescent : baseEnd_832078 < baseStart_832078 := by decide
  rcases family_descends (prefixWord ++ tailWord_832078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832081 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_832081 : Nat := 118140960795 + 832081 * 2 ^ 59
def prefixEnd_832081 : Nat := 4983230072969 + 3 ^ 40 * 832081 * 2
def baseEnd_832081 : Nat := 142419165491288070986945

theorem tailTrace_832081 : CollatzResearch.WordTrace tailWord_832081 prefixEnd_832081 142419165491288070986945 := by
  unfold tailWord_832081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30348487298520119966104097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20232324865680079977402731 30348487298520119966104097)
  ·
    refine ⟨22761365473890089974578073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30348487298520119966104097 22761365473890089974578073)
    ·
      refine ⟨17071024105417567480933555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22761365473890089974578073 17071024105417567480933555)
      ·
        refine ⟨25606536158126351221400333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17071024105417567480933555 25606536158126351221400333)
        ·
          refine ⟨9602451059297381708025125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25606536158126351221400333 9602451059297381708025125)
          ·
            refine ⟨1800459573618259070254711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9602451059297381708025125 1800459573618259070254711)
            ·
              refine ⟨2700689360427388605382067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800459573618259070254711 2700689360427388605382067)
              ·
                refine ⟨4051034040641082908073101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700689360427388605382067 4051034040641082908073101)
                ·
                  refine ⟨1519137765240406090527413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4051034040641082908073101 1519137765240406090527413)
                  ·
                    refine ⟨142419165491288070986945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1519137765240406090527413 142419165491288070986945)
                    ·
                      rfl

theorem cell23_832081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_832081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832081 prefixEnd_832081 := by exact prefixLift 832081
  have htrace : WordTrace (prefixWord ++ tailWord_832081) baseStart_832081 baseEnd_832081 := by
    simpa [prefixWord, tailWord_832081, baseEnd_832081] using wordTrace_append hprefix tailTrace_832081
  have hstable : (prefixWord ++ tailWord_832081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832081).length < 2 ^ (prefixWord ++ tailWord_832081).sum := by decide
  have hdescent : baseEnd_832081 < baseStart_832081 := by decide
  rcases family_descends (prefixWord ++ tailWord_832081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832088 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 2, 3, 2]
def baseStart_832088 : Nat := 118140960795 + 832088 * 2 ^ 59
def prefixEnd_832088 : Nat := 4983230072969 + 3 ^ 40 * 832088 * 2
def baseEnd_832088 : Nat := 427261090838445685573303

theorem tailTrace_832088 : CollatzResearch.WordTrace tailWord_832088 prefixEnd_832088 427261090838445685573303 := by
  unfold tailWord_832088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174371304747380080804459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20232495072996506774405945 15174371304747380080804459)
  ·
    refine ⟨22761556957121070121206689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15174371304747380080804459 22761556957121070121206689)
    ·
      refine ⟨17071167717840802590905017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22761556957121070121206689 17071167717840802590905017)
      ·
        refine ⟨12803375788380601943178763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17071167717840802590905017 12803375788380601943178763)
        ·
          refine ⟨19205063682570902914768145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12803375788380601943178763 19205063682570902914768145)
          ·
            refine ⟨14403797761928177186076109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19205063682570902914768145 14403797761928177186076109)
            ·
              refine ⟨5401424160723066444778541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14403797761928177186076109 5401424160723066444778541)
              ·
                refine ⟨2025534060271149916791953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5401424160723066444778541 2025534060271149916791953)
                ·
                  refine ⟨1519150545203362437593965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2025534060271149916791953 1519150545203362437593965)
                  ·
                    refine ⟨569681454451260914097737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519150545203362437593965 569681454451260914097737)
                    ·
                      refine ⟨427261090838445685573303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569681454451260914097737 427261090838445685573303)
                      ·
                        rfl

theorem cell23_832088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_832088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832088 prefixEnd_832088 := by exact prefixLift 832088
  have htrace : WordTrace (prefixWord ++ tailWord_832088) baseStart_832088 baseEnd_832088 := by
    simpa [prefixWord, tailWord_832088, baseEnd_832088] using wordTrace_append hprefix tailTrace_832088
  have hstable : (prefixWord ++ tailWord_832088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832088).length < 2 ^ (prefixWord ++ tailWord_832088).sum := by decide
  have hdescent : baseEnd_832088 < baseStart_832088 := by decide
  rcases family_descends (prefixWord ++ tailWord_832088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832111 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 4, 4]
def baseStart_832111 : Nat := 118140960795 + 832111 * 2 ^ 59
def prefixEnd_832111 : Nat := 4983230072969 + 3 ^ 40 * 832111 * 2
def baseEnd_832111 : Nat := 142424300297833031861899

theorem tailTrace_832111 : CollatzResearch.WordTrace tailWord_832111 prefixEnd_832111 142424300297833031861899 := by
  unfold tailWord_832111
  simp only [CollatzResearch.WordTrace]
  refine ⟨30349581488411435089696187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20233054325607623393130791 30349581488411435089696187)
  ·
    refine ⟨45524372232617152634544281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30349581488411435089696187 45524372232617152634544281)
    ·
      refine ⟨34143279174462864475908211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45524372232617152634544281 34143279174462864475908211)
      ·
        refine ⟨51214918761694296713862317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34143279174462864475908211 51214918761694296713862317)
        ·
          refine ⟨19205594535635361267698369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51214918761694296713862317 19205594535635361267698369)
          ·
            refine ⟨14404195901726520950773777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19205594535635361267698369 14404195901726520950773777)
            ·
              refine ⟨10803146926294890713080333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14404195901726520950773777 10803146926294890713080333)
              ·
                refine ⟨4051180097360584017405125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10803146926294890713080333 4051180097360584017405125)
                ·
                  refine ⟨759596268255109503263461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4051180097360584017405125 759596268255109503263461)
                  ·
                    refine ⟨142424300297833031861899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759596268255109503263461 142424300297833031861899)
                    ·
                      rfl

theorem cell23_832111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_832111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832111 prefixEnd_832111 := by exact prefixLift 832111
  have htrace : WordTrace (prefixWord ++ tailWord_832111) baseStart_832111 baseEnd_832111 := by
    simpa [prefixWord, tailWord_832111, baseEnd_832111] using wordTrace_append hprefix tailTrace_832111
  have hstable : (prefixWord ++ tailWord_832111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832111).length < 2 ^ (prefixWord ++ tailWord_832111).sum := by decide
  have hdescent : baseEnd_832111 < baseStart_832111 := by decide
  rcases family_descends (prefixWord ++ tailWord_832111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832112 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 1, 1, 3]
def baseStart_832112 : Nat := 118140960795 + 832112 * 2 ^ 59
def prefixEnd_832112 : Nat := 4983230072969 + 3 ^ 40 * 832112 * 2
def baseEnd_832112 : Nat := 427273414374153591673193

theorem tailTrace_832112 : CollatzResearch.WordTrace tailWord_832112 prefixEnd_832112 427273414374153591673193 := by
  unfold tailWord_832112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174808980703906130241295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20233078640938541506988393 15174808980703906130241295)
  ·
    refine ⟨22762213471055859195361943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15174808980703906130241295 22762213471055859195361943)
    ·
      refine ⟨34143320206583788793042915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22762213471055859195361943 34143320206583788793042915)
      ·
        refine ⟨51214980309875683189564373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34143320206583788793042915 51214980309875683189564373)
        ·
          refine ⟨1200351101012711324755415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51214980309875683189564373 1200351101012711324755415)
          ·
            refine ⟨1800526651519066987133123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200351101012711324755415 1800526651519066987133123)
            ·
              refine ⟨2700789977278600480699685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800526651519066987133123 2700789977278600480699685)
              ·
                refine ⟨506398120739737590131191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2700789977278600480699685 506398120739737590131191)
                ·
                  refine ⟨759597181109606385196787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506398120739737590131191 759597181109606385196787)
                  ·
                    refine ⟨1139395771664409577795181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 759597181109606385196787 1139395771664409577795181)
                    ·
                      refine ⟨427273414374153591673193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139395771664409577795181 427273414374153591673193)
                      ·
                        rfl

theorem cell23_832112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 1, 3].length) (baseStart_832112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832112 prefixEnd_832112 := by exact prefixLift 832112
  have htrace : WordTrace (prefixWord ++ tailWord_832112) baseStart_832112 baseEnd_832112 := by
    simpa [prefixWord, tailWord_832112, baseEnd_832112] using wordTrace_append hprefix tailTrace_832112
  have hstable : (prefixWord ++ tailWord_832112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832112).length < 2 ^ (prefixWord ++ tailWord_832112).sum := by decide
  have hdescent : baseEnd_832112 < baseStart_832112 := by decide
  rcases family_descends (prefixWord ++ tailWord_832112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832128 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 2, 4]
def baseStart_832128 : Nat := 118140960795 + 832128 * 2 ^ 59
def prefixEnd_832128 : Nat := 4983230072969 + 3 ^ 40 * 832128 * 2
def baseEnd_832128 : Nat := 142427210021541843024373

theorem tailTrace_832128 : CollatzResearch.WordTrace tailWord_832128 prefixEnd_832128 142427210021541843024373 := by
  unfold tailWord_832128
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175100764674923496532519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20233467686233231328710025 15175100764674923496532519)
  ·
    refine ⟨22762651147012385244798779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15175100764674923496532519 22762651147012385244798779)
    ·
      refine ⟨34143976720518577867198169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22762651147012385244798779 34143976720518577867198169)
      ·
        refine ⟨25607982540388933400398627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34143976720518577867198169 25607982540388933400398627)
        ·
          refine ⟨38411973810583400100597941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25607982540388933400398627 38411973810583400100597941)
          ·
            refine ⟨3601122544742193759431057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38411973810583400100597941 3601122544742193759431057)
            ·
              refine ⟨2700841908556645319573293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601122544742193759431057 2700841908556645319573293)
              ·
                refine ⟨1012815715708741994839985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700841908556645319573293 1012815715708741994839985)
                ·
                  refine ⟨759611786781556496129989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012815715708741994839985 759611786781556496129989)
                  ·
                    refine ⟨142427210021541843024373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759611786781556496129989 142427210021541843024373)
                    ·
                      rfl

theorem cell23_832128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_832128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832128 prefixEnd_832128 := by exact prefixLift 832128
  have htrace : WordTrace (prefixWord ++ tailWord_832128) baseStart_832128 baseEnd_832128 := by
    simpa [prefixWord, tailWord_832128, baseEnd_832128] using wordTrace_append hprefix tailTrace_832128
  have hstable : (prefixWord ++ tailWord_832128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832128).length < 2 ^ (prefixWord ++ tailWord_832128).sum := by decide
  have hdescent : baseEnd_832128 < baseStart_832128 := by decide
  rcases family_descends (prefixWord ++ tailWord_832128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832131 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4]
def baseStart_832131 : Nat := 118140960795 + 832131 * 2 ^ 59
def prefixEnd_832131 : Nat := 4983230072969 + 3 ^ 40 * 832131 * 2
def baseEnd_832131 : Nat := 427283170506589017335605

theorem tailTrace_832131 : CollatzResearch.WordTrace tailWord_832131 prefixEnd_832131 427283170506589017335605 := by
  unfold tailWord_832131
  simp only [CollatzResearch.WordTrace]
  refine ⟨30350310948338978505424247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20233540632225985670282831 30350310948338978505424247)
  ·
    refine ⟨45525466422508467758136371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30350310948338978505424247 45525466422508467758136371)
    ·
      refine ⟨68288199633762701637204557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45525466422508467758136371 68288199633762701637204557)
      ·
        refine ⟨25608074862661013113951709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68288199633762701637204557 25608074862661013113951709)
        ·
          refine ⟨9603028073497879917731891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25608074862661013113951709 9603028073497879917731891)
          ·
            refine ⟨14404542110246819876597837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9603028073497879917731891 14404542110246819876597837)
            ·
              refine ⟨5401703291342557453724189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14404542110246819876597837 5401703291342557453724189)
              ·
                refine ⟨2025638734253459045146571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5401703291342557453724189 2025638734253459045146571)
                ·
                  refine ⟨3038458101380188567719857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025638734253459045146571 3038458101380188567719857)
                  ·
                    refine ⟨2278843576035141425789893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3038458101380188567719857 2278843576035141425789893)
                    ·
                      refine ⟨427283170506589017335605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2278843576035141425789893 427283170506589017335605)
                      ·
                        rfl

theorem cell23_832131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_832131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832131 prefixEnd_832131 := by exact prefixLift 832131
  have htrace : WordTrace (prefixWord ++ tailWord_832131) baseStart_832131 baseEnd_832131 := by
    simpa [prefixWord, tailWord_832131, baseEnd_832131] using wordTrace_append hprefix tailTrace_832131
  have hstable : (prefixWord ++ tailWord_832131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832131).length < 2 ^ (prefixWord ++ tailWord_832131).sum := by decide
  have hdescent : baseEnd_832131 < baseStart_832131 := by decide
  rcases family_descends (prefixWord ++ tailWord_832131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832135 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_832135 : Nat := 118140960795 + 832135 * 2 ^ 59
def prefixEnd_832135 : Nat := 4983230072969 + 3 ^ 40 * 832135 * 2
def baseEnd_832135 : Nat := 427285224429207001685587

theorem tailTrace_832135 : CollatzResearch.WordTrace tailWord_832135 prefixEnd_832135 427285224429207001685587 := by
  unfold tailWord_832135
  simp only [CollatzResearch.WordTrace]
  refine ⟨30350456840324487188569859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20233637893549658125713239 30350456840324487188569859)
  ·
    refine ⟨45525685260486730782854789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30350456840324487188569859 45525685260486730782854789)
    ·
      refine ⟨8536065986341262021785273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45525685260486730782854789 8536065986341262021785273)
      ·
        refine ⟨6402049489755946516338955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8536065986341262021785273 6402049489755946516338955)
        ·
          refine ⟨9603074234633919774508433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6402049489755946516338955 9603074234633919774508433)
          ·
            refine ⟨7202305675975439830881325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9603074234633919774508433 7202305675975439830881325)
            ·
              refine ⟨2700864628490789936580497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7202305675975439830881325 2700864628490789936580497)
              ·
                refine ⟨2025648471368092452435373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700864628490789936580497 2025648471368092452435373)
                ·
                  refine ⟨759618176763034669663265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2025648471368092452435373 759618176763034669663265)
                  ·
                    refine ⟨569713632572276002247449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759618176763034669663265 569713632572276002247449)
                    ·
                      refine ⟨427285224429207001685587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569713632572276002247449 427285224429207001685587)
                      ·
                        rfl

theorem cell23_832135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_832135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832135 prefixEnd_832135 := by exact prefixLift 832135
  have htrace : WordTrace (prefixWord ++ tailWord_832135) baseStart_832135 baseEnd_832135 := by
    simpa [prefixWord, tailWord_832135, baseEnd_832135] using wordTrace_append hprefix tailTrace_832135
  have hstable : (prefixWord ++ tailWord_832135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832135).length < 2 ^ (prefixWord ++ tailWord_832135).sum := by decide
  have hdescent : baseEnd_832135 < baseStart_832135 := by decide
  rcases family_descends (prefixWord ++ tailWord_832135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832261 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_832261 : Nat := 118140960795 + 832261 * 2 ^ 59
def prefixEnd_832261 : Nat := 4983230072969 + 3 ^ 40 * 832261 * 2
def baseEnd_832261 : Nat := 142449974330557836236669

theorem tailTrace_832261 : CollatzResearch.WordTrace tailWord_832261 prefixEnd_832261 142449974330557836236669 := by
  unfold tailWord_832261
  simp only [CollatzResearch.WordTrace]
  refine ⟨30355052437868010707656637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20236701625245340471771091 30355052437868010707656637)
  ·
    refine ⟨11383144664200504015371239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30355052437868010707656637 11383144664200504015371239)
    ·
      refine ⟨17074716996300756023056859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11383144664200504015371239 17074716996300756023056859)
      ·
        refine ⟨25612075494451134034585289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17074716996300756023056859 25612075494451134034585289)
        ·
          refine ⟨19209056620838350525938967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25612075494451134034585289 19209056620838350525938967)
          ·
            refine ⟨28813584931257525788908451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19209056620838350525938967 28813584931257525788908451)
            ·
              refine ⟨43220377396886288683362677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28813584931257525788908451 43220377396886288683362677)
              ·
                refine ⟨4051910380958089564065251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43220377396886288683362677 4051910380958089564065251)
                ·
                  refine ⟨6077865571437134346097877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051910380958089564065251 6077865571437134346097877)
                  ·
                    refine ⟨142449974330557836236669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6077865571437134346097877 142449974330557836236669)
                    ·
                      rfl

theorem cell23_832261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_832261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832261 prefixEnd_832261 := by exact prefixLift 832261
  have htrace : WordTrace (prefixWord ++ tailWord_832261) baseStart_832261 baseEnd_832261 := by
    simpa [prefixWord, tailWord_832261, baseEnd_832261] using wordTrace_append hprefix tailTrace_832261
  have hstable : (prefixWord ++ tailWord_832261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832261).length < 2 ^ (prefixWord ++ tailWord_832261).sum := by decide
  have hdescent : baseEnd_832261 < baseStart_832261 := by decide
  rcases family_descends (prefixWord ++ tailWord_832261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832271 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_832271 : Nat := 118140960795 + 832271 * 2 ^ 59
def prefixEnd_832271 : Nat := 4983230072969 + 3 ^ 40 * 832271 * 2
def baseEnd_832271 : Nat := 427355057798218469584961

theorem tailTrace_832271 : CollatzResearch.WordTrace tailWord_832271 prefixEnd_832271 427355057798218469584961 := by
  unfold tailWord_832271
  simp only [CollatzResearch.WordTrace]
  refine ⟨30355417167831782415520667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20236944778554521610347111 30355417167831782415520667)
  ·
    refine ⟨45533125751747673623281001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30355417167831782415520667 45533125751747673623281001)
    ·
      refine ⟨34149844313810755217460751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45533125751747673623281001 34149844313810755217460751)
      ·
        refine ⟨51224766470716132826191127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34149844313810755217460751 51224766470716132826191127)
        ·
          refine ⟨76837149706074199239286691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51224766470716132826191127 76837149706074199239286691)
          ·
            refine ⟨115255724559111298858930037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76837149706074199239286691 115255724559111298858930037)
            ·
              refine ⟨10805224177416684268024691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115255724559111298858930037 10805224177416684268024691)
              ·
                refine ⟨16207836266125026402037037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10805224177416684268024691 16207836266125026402037037)
                ·
                  refine ⟨6077938599796884900763889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16207836266125026402037037 6077938599796884900763889)
                  ·
                    refine ⟨4558453949847663675572917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6077938599796884900763889 4558453949847663675572917)
                    ·
                      refine ⟨427355057798218469584961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4558453949847663675572917 427355057798218469584961)
                      ·
                        rfl

theorem cell23_832271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_832271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832271 prefixEnd_832271 := by exact prefixLift 832271
  have htrace : WordTrace (prefixWord ++ tailWord_832271) baseStart_832271 baseEnd_832271 := by
    simpa [prefixWord, tailWord_832271, baseEnd_832271] using wordTrace_append hprefix tailTrace_832271
  have hstable : (prefixWord ++ tailWord_832271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832271).length < 2 ^ (prefixWord ++ tailWord_832271).sum := by decide
  have hdescent : baseEnd_832271 < baseStart_832271 := by decide
  rcases family_descends (prefixWord ++ tailWord_832271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832288 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_832288 : Nat := 118140960795 + 832288 * 2 ^ 59
def prefixEnd_832288 : Nat := 4983230072969 + 3 ^ 40 * 832288 * 2
def baseEnd_832288 : Nat := 427363786969344903072383

theorem tailTrace_832288 : CollatzResearch.WordTrace tailWord_832288 prefixEnd_832288 427363786969344903072383 := by
  unfold tailWord_832288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15178018604385097159444759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20237358139180129545926345 15178018604385097159444759)
  ·
    refine ⟨22767027906577645739167139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15178018604385097159444759 22767027906577645739167139)
    ·
      refine ⟨34150541859866468608750709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22767027906577645739167139 34150541859866468608750709)
      ·
        refine ⟨3201613299362481432070379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34150541859866468608750709 3201613299362481432070379)
        ·
          refine ⟨4802419949043722148105569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201613299362481432070379 4802419949043722148105569)
          ·
            refine ⟨3601814961782791611079177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4802419949043722148105569 3601814961782791611079177)
            ·
              refine ⟨2701361221337093708309383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601814961782791611079177 2701361221337093708309383)
              ·
                refine ⟨4052041832005640562464075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701361221337093708309383 4052041832005640562464075)
                ·
                  refine ⟨6078062748008460843696113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052041832005640562464075 6078062748008460843696113)
                  ·
                    refine ⟨4558547061006345632772085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078062748008460843696113 4558547061006345632772085)
                    ·
                      refine ⟨427363786969344903072383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4558547061006345632772085 427363786969344903072383)
                      ·
                        rfl

theorem cell23_832288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_832288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832288 prefixEnd_832288 := by exact prefixLift 832288
  have htrace : WordTrace (prefixWord ++ tailWord_832288) baseStart_832288 baseEnd_832288 := by
    simpa [prefixWord, tailWord_832288, baseEnd_832288] using wordTrace_append hprefix tailTrace_832288
  have hstable : (prefixWord ++ tailWord_832288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832288).length < 2 ^ (prefixWord ++ tailWord_832288).sum := by decide
  have hdescent : baseEnd_832288 < baseStart_832288 := by decide
  rcases family_descends (prefixWord ++ tailWord_832288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832291 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 8]
def baseStart_832291 : Nat := 118140960795 + 832291 * 2 ^ 59
def prefixEnd_832291 : Nat := 4983230072969 + 3 ^ 40 * 832291 * 2
def baseEnd_832291 : Nat := 142455109137102797111623

theorem tailTrace_832291 : CollatzResearch.WordTrace tailWord_832291 prefixEnd_832291 142455109137102797111623 := by
  unfold tailWord_832291
  simp only [CollatzResearch.WordTrace]
  refine ⟨30356146627759325831248727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20237431085172883887499151 30356146627759325831248727)
  ·
    refine ⟨45534219941638988746873091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30356146627759325831248727 45534219941638988746873091)
    ·
      refine ⟨68301329912458483120309637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45534219941638988746873091 68301329912458483120309637)
      ·
        refine ⟨12806499358585965585058057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68301329912458483120309637 12806499358585965585058057)
        ·
          refine ⟨9604874518939474188793543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12806499358585965585058057 9604874518939474188793543)
          ·
            refine ⟨14407311778409211283190315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9604874518939474188793543 14407311778409211283190315)
            ·
              refine ⟨21610967667613816924785473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14407311778409211283190315 21610967667613816924785473)
              ·
                refine ⟨16208225750710362693589105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21610967667613816924785473 16208225750710362693589105)
                ·
                  refine ⟨12156169313032772020191829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16208225750710362693589105 12156169313032772020191829)
                  ·
                    refine ⟨142455109137102797111623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12156169313032772020191829 142455109137102797111623)
                    ·
                      rfl

theorem cell23_832291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_832291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832291 prefixEnd_832291 := by exact prefixLift 832291
  have htrace : WordTrace (prefixWord ++ tailWord_832291) baseStart_832291 baseEnd_832291 := by
    simpa [prefixWord, tailWord_832291, baseEnd_832291] using wordTrace_append hprefix tailTrace_832291
  have hstable : (prefixWord ++ tailWord_832291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832291).length < 2 ^ (prefixWord ++ tailWord_832291).sum := by decide
  have hdescent : baseEnd_832291 < baseStart_832291 := by decide
  rcases family_descends (prefixWord ++ tailWord_832291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832331 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_832331 : Nat := 118140960795 + 832331 * 2 ^ 59
def prefixEnd_832331 : Nat := 4983230072969 + 3 ^ 40 * 832331 * 2
def baseEnd_832331 : Nat := 427385866637488234834685

theorem tailTrace_832331 : CollatzResearch.WordTrace tailWord_832331 prefixEnd_832331 427385866637488234834685 := by
  unfold tailWord_832331
  simp only [CollatzResearch.WordTrace]
  refine ⟨30357605547614412662704847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20238403698409608441803231 30357605547614412662704847)
  ·
    refine ⟨45536408321421618994057271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30357605547614412662704847 45536408321421618994057271)
    ·
      refine ⟨68304612482132428491085907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45536408321421618994057271 68304612482132428491085907)
      ·
        refine ⟨102456918723198642736628861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68304612482132428491085907 102456918723198642736628861)
        ·
          refine ⟨38421344521199491026235823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102456918723198642736628861 38421344521199491026235823)
          ·
            refine ⟨57632016781799236539353735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38421344521199491026235823 57632016781799236539353735)
            ·
              refine ⟨86448025172698854809030603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57632016781799236539353735 86448025172698854809030603)
              ·
                refine ⟨129672037759048282213545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86448025172698854809030603 129672037759048282213545905)
                ·
                  refine ⟨97254028319286211660159429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129672037759048282213545905 97254028319286211660159429)
                  ·
                    refine ⟨18235130309866164686279893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97254028319286211660159429 18235130309866164686279893)
                    ·
                      refine ⟨427385866637488234834685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18235130309866164686279893 427385866637488234834685)
                      ·
                        rfl

theorem cell23_832331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_832331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832331 prefixEnd_832331 := by exact prefixLift 832331
  have htrace : WordTrace (prefixWord ++ tailWord_832331) baseStart_832331 baseEnd_832331 := by
    simpa [prefixWord, tailWord_832331, baseEnd_832331] using wordTrace_append hprefix tailTrace_832331
  have hstable : (prefixWord ++ tailWord_832331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832331).length < 2 ^ (prefixWord ++ tailWord_832331).sum := by decide
  have hdescent : baseEnd_832331 < baseStart_832331 := by decide
  rcases family_descends (prefixWord ++ tailWord_832331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832338 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_832338 : Nat := 118140960795 + 832338 * 2 ^ 59
def prefixEnd_832338 : Nat := 4983230072969 + 3 ^ 40 * 832338 * 2
def baseEnd_832338 : Nat := 47487717889118856383017

theorem tailTrace_832338 : CollatzResearch.WordTrace tailWord_832338 prefixEnd_832338 47487717889118856383017 := by
  unfold tailWord_832338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589465214647263214552417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20238573905726035238806445 7589465214647263214552417)
  ·
    refine ⟨5692098910985447410914313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7589465214647263214552417 5692098910985447410914313)
    ·
      refine ⟨4269074183239085558185735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5692098910985447410914313 4269074183239085558185735)
      ·
        refine ⟨6403611274858628337278603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4269074183239085558185735 6403611274858628337278603)
        ·
          refine ⟨9605416912287942505917905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403611274858628337278603 9605416912287942505917905)
          ·
            refine ⟨7204062684215956879438429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605416912287942505917905 7204062684215956879438429)
            ·
              refine ⟨2701523506580983829789411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7204062684215956879438429 2701523506580983829789411)
              ·
                refine ⟨4052285259871475744684117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701523506580983829789411 4052285259871475744684117)
                ·
                  refine ⟨47487717889118856383017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4052285259871475744684117 47487717889118856383017)
                  ·
                    rfl

theorem cell23_832338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_832338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832338 prefixEnd_832338 := by exact prefixLift 832338
  have htrace : WordTrace (prefixWord ++ tailWord_832338) baseStart_832338 baseEnd_832338 := by
    simpa [prefixWord, tailWord_832338, baseEnd_832338] using wordTrace_append hprefix tailTrace_832338
  have hstable : (prefixWord ++ tailWord_832338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832338).length < 2 ^ (prefixWord ++ tailWord_832338).sum := by decide
  have hdescent : baseEnd_832338 < baseStart_832338 := by decide
  rcases family_descends (prefixWord ++ tailWord_832338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832368 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_832368 : Nat := 118140960795 + 832368 * 2 ^ 59
def prefixEnd_832368 : Nat := 4983230072969 + 3 ^ 40 * 832368 * 2
def baseEnd_832368 : Nat := 142468288473901530024005

theorem tailTrace_832368 : CollatzResearch.WordTrace tailWord_832368 prefixEnd_832368 142468288473901530024005 := by
  unfold tailWord_832368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179477524240183990900879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20239303365653578654534505 15179477524240183990900879)
  ·
    refine ⟨22769216286360275986351319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15179477524240183990900879 22769216286360275986351319)
    ·
      refine ⟨34153824429540413979526979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22769216286360275986351319 34153824429540413979526979)
      ·
        refine ⟨51230736644310620969290469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34153824429540413979526979 51230736644310620969290469)
        ·
          refine ⟨9605763120808241431741963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51230736644310620969290469 9605763120808241431741963)
          ·
            refine ⟨14408644681212362147612945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605763120808241431741963 14408644681212362147612945)
            ·
              refine ⟨10806483510909271610709709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14408644681212362147612945 10806483510909271610709709)
              ·
                refine ⟨4052431316590976854016141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10806483510909271610709709 4052431316590976854016141)
                ·
                  refine ⟨1519661743721616320256053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4052431316590976854016141 1519661743721616320256053)
                  ·
                    refine ⟨142468288473901530024005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1519661743721616320256053 142468288473901530024005)
                    ·
                      rfl

theorem cell23_832368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_832368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832368 prefixEnd_832368 := by exact prefixLift 832368
  have htrace : WordTrace (prefixWord ++ tailWord_832368) baseStart_832368 baseEnd_832368 := by
    simpa [prefixWord, tailWord_832368, baseEnd_832368] using wordTrace_append hprefix tailTrace_832368
  have hstable : (prefixWord ++ tailWord_832368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832368).length < 2 ^ (prefixWord ++ tailWord_832368).sum := by decide
  have hdescent : baseEnd_832368 < baseStart_832368 := by decide
  rcases family_descends (prefixWord ++ tailWord_832368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832375 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 6, 3, 2]
def baseStart_832375 : Nat := 118140960795 + 832375 * 2 ^ 59
def prefixEnd_832375 : Nat := 4983230072969 + 3 ^ 40 * 832375 * 2
def baseEnd_832375 : Nat := 427408459786286062684483

theorem tailTrace_832375 : CollatzResearch.WordTrace tailWord_832375 prefixEnd_832375 427408459786286062684483 := by
  unfold tailWord_832375
  simp only [CollatzResearch.WordTrace]
  refine ⟨30359210359455008177306579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20239473572970005451537719 30359210359455008177306579)
  ·
    refine ⟨45538815539182512265959869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30359210359455008177306579 45538815539182512265959869)
    ·
      refine ⟨17077055827193442099734951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45538815539182512265959869 17077055827193442099734951)
      ·
        refine ⟨25615583740790163149602427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17077055827193442099734951 25615583740790163149602427)
        ·
          refine ⟨38423375611185244724403641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25615583740790163149602427 38423375611185244724403641)
          ·
            refine ⟨28817531708388933543302731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38423375611185244724403641 28817531708388933543302731)
            ·
              refine ⟨43226297562583400314954097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28817531708388933543302731 43226297562583400314954097)
              ·
                refine ⟨32419723171937550236215573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43226297562583400314954097 32419723171937550236215573)
                ·
                  refine ⟨1519674523684572667322605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32419723171937550236215573 1519674523684572667322605)
                  ·
                    refine ⟨569877946381714750245977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519674523684572667322605 569877946381714750245977)
                    ·
                      refine ⟨427408459786286062684483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569877946381714750245977 427408459786286062684483)
                      ·
                        rfl

theorem cell23_832375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_832375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832375 prefixEnd_832375 := by exact prefixLift 832375
  have htrace : WordTrace (prefixWord ++ tailWord_832375) baseStart_832375 baseEnd_832375 := by
    simpa [prefixWord, tailWord_832375, baseEnd_832375] using wordTrace_append hprefix tailTrace_832375
  have hstable : (prefixWord ++ tailWord_832375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832375).length < 2 ^ (prefixWord ++ tailWord_832375).sum := by decide
  have hdescent : baseEnd_832375 < baseStart_832375 := by decide
  rcases family_descends (prefixWord ++ tailWord_832375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832386 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_832386 : Nat := 118140960795 + 832386 * 2 ^ 59
def prefixEnd_832386 : Nat := 4983230072969 + 3 ^ 40 * 832386 * 2
def baseEnd_832386 : Nat := 427414108073485519646933

theorem tailTrace_832386 : CollatzResearch.WordTrace tailWord_832386 prefixEnd_832386 427414108073485519646933 := by
  unfold tailWord_832386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589902890603789263989253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20239741041610104703971341 7589902890603789263989253)
  ·
    refine ⟨1423106791988210486997985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7589902890603789263989253 1423106791988210486997985)
    ·
      refine ⟨1067330093991157865248489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423106791988210486997985 1067330093991157865248489)
      ·
        refine ⟨800497570493368398936367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1067330093991157865248489 800497570493368398936367)
        ·
          refine ⟨1200746355740052598404551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800497570493368398936367 1200746355740052598404551)
          ·
            refine ⟨1801119533610078897606827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200746355740052598404551 1801119533610078897606827)
            ·
              refine ⟨2701679300415118346410241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801119533610078897606827 2701679300415118346410241)
              ·
                refine ⟨2026259475311338759807681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701679300415118346410241 2026259475311338759807681)
                ·
                  refine ⟨1519694606483504069855761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026259475311338759807681 1519694606483504069855761)
                  ·
                    refine ⟨1139770954862628052391821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1519694606483504069855761 1139770954862628052391821)
                    ·
                      refine ⟨427414108073485519646933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139770954862628052391821 427414108073485519646933)
                      ·
                        rfl

theorem cell23_832386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_832386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832386 prefixEnd_832386 := by exact prefixLift 832386
  have htrace : WordTrace (prefixWord ++ tailWord_832386) baseStart_832386 baseEnd_832386 := by
    simpa [prefixWord, tailWord_832386, baseEnd_832386] using wordTrace_append hprefix tailTrace_832386
  have hstable : (prefixWord ++ tailWord_832386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832386).length < 2 ^ (prefixWord ++ tailWord_832386).sum := by decide
  have hdescent : baseEnd_832386 < baseStart_832386 := by decide
  rcases family_descends (prefixWord ++ tailWord_832386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832392 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_832392 : Nat := 118140960795 + 832392 * 2 ^ 59
def prefixEnd_832392 : Nat := 4983230072969 + 3 ^ 40 * 832392 * 2
def baseEnd_832392 : Nat := 427417188957412496171905

theorem tailTrace_832392 : CollatzResearch.WordTrace tailWord_832392 prefixEnd_832392 427417188957412496171905 := by
  unfold tailWord_832392
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179915200196710040337715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20239886933595613387116953 15179915200196710040337715)
  ·
    refine ⟨22769872800295065060506573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15179915200196710040337715 22769872800295065060506573)
    ·
      refine ⟨8538702300110649397689965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22769872800295065060506573 8538702300110649397689965)
      ·
        refine ⟨3202013362541493524133737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8538702300110649397689965 3202013362541493524133737)
        ·
          refine ⟨2401510021906120143100303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202013362541493524133737 2401510021906120143100303)
          ·
            refine ⟨3602265032859180214650455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401510021906120143100303 3602265032859180214650455)
            ·
              refine ⟨5403397549288770321975683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602265032859180214650455 5403397549288770321975683)
              ·
                refine ⟨8105096323933155482963525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403397549288770321975683 8105096323933155482963525)
                ·
                  refine ⟨1519705560737466653055661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8105096323933155482963525 1519705560737466653055661)
                  ·
                    refine ⟨569889585276549994895873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519705560737466653055661 569889585276549994895873)
                    ·
                      refine ⟨427417188957412496171905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569889585276549994895873 427417188957412496171905)
                      ·
                        rfl

theorem cell23_832392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_832392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832392 prefixEnd_832392 := by exact prefixLift 832392
  have htrace : WordTrace (prefixWord ++ tailWord_832392) baseStart_832392 baseEnd_832392 := by
    simpa [prefixWord, tailWord_832392, baseEnd_832392] using wordTrace_append hprefix tailTrace_832392
  have hstable : (prefixWord ++ tailWord_832392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832392).length < 2 ^ (prefixWord ++ tailWord_832392).sum := by decide
  have hdescent : baseEnd_832392 < baseStart_832392 := by decide
  rcases family_descends (prefixWord ++ tailWord_832392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832406 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_832406 : Nat := 118140960795 + 832406 * 2 ^ 59
def prefixEnd_832406 : Nat := 4983230072969 + 3 ^ 40 * 832406 * 2
def baseEnd_832406 : Nat := 47491597520730604599649

theorem tailTrace_832406 : CollatzResearch.WordTrace tailWord_832406 prefixEnd_832406 47491597520730604599649 := by
  unfold tailWord_832406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897521313896418779480317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20240227348228466981123381 1897521313896418779480317)
  ·
    refine ⟨711570492711157042305119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1897521313896418779480317 711570492711157042305119)
    ·
      refine ⟨1067355739066735563457679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711570492711157042305119 1067355739066735563457679)
      ·
        refine ⟨1601033608600103345186519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067355739066735563457679 1601033608600103345186519)
        ·
          refine ⟨2401550412900155017779779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601033608600103345186519 2401550412900155017779779)
          ·
            refine ⟨3602325619350232526669669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401550412900155017779779 3602325619350232526669669)
            ·
              refine ⟨675436053628168598750563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3602325619350232526669669 675436053628168598750563)
              ·
                refine ⟨1013154080442252898125845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675436053628168598750563 1013154080442252898125845)
                ·
                  refine ⟨47491597520730604599649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1013154080442252898125845 47491597520730604599649)
                  ·
                    rfl

theorem cell23_832406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_832406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832406 prefixEnd_832406 := by exact prefixLift 832406
  have htrace : WordTrace (prefixWord ++ tailWord_832406) baseStart_832406 baseEnd_832406 := by
    simpa [prefixWord, tailWord_832406, baseEnd_832406] using wordTrace_append hprefix tailTrace_832406
  have hstable : (prefixWord ++ tailWord_832406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832406).length < 2 ^ (prefixWord ++ tailWord_832406).sum := by decide
  have hdescent : baseEnd_832406 < baseStart_832406 := by decide
  rcases family_descends (prefixWord ++ tailWord_832406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832425 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_832425 : Nat := 118140960795 + 832425 * 2 ^ 59
def prefixEnd_832425 : Nat := 4983230072969 + 3 ^ 40 * 832425 * 2
def baseEnd_832425 : Nat := 427434133819010867059253

theorem tailTrace_832425 : CollatzResearch.WordTrace tailWord_832425 prefixEnd_832425 427434133819010867059253 := by
  unfold tailWord_832425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361034009273866716626729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20240689339515911144417819 30361034009273866716626729)
  ·
    refine ⟨22770775506955400037470047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30361034009273866716626729 22770775506955400037470047)
    ·
      refine ⟨34156163260433100056205071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22770775506955400037470047 34156163260433100056205071)
      ·
        refine ⟨51234244890649650084307607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34156163260433100056205071 51234244890649650084307607)
        ·
          refine ⟨76851367335974475126461411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51234244890649650084307607 76851367335974475126461411)
          ·
            refine ⟨115277051003961712689692117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76851367335974475126461411 115277051003961712689692117)
            ·
              refine ⟨2701805882905352641164659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 115277051003961712689692117 2701805882905352641164659)
              ·
                refine ⟨4052708824358028961746989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701805882905352641164659 4052708824358028961746989)
                ·
                  refine ⟨1519765809134260860655121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4052708824358028961746989 1519765809134260860655121)
                  ·
                    refine ⟨1139824356850695645491341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1519765809134260860655121 1139824356850695645491341)
                    ·
                      refine ⟨427434133819010867059253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139824356850695645491341 427434133819010867059253)
                      ·
                        rfl

theorem cell23_832425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_832425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832425 prefixEnd_832425 := by exact prefixLift 832425
  have htrace : WordTrace (prefixWord ++ tailWord_832425) baseStart_832425 baseEnd_832425 := by
    simpa [prefixWord, tailWord_832425, baseEnd_832425] using wordTrace_append hprefix tailTrace_832425
  have hstable : (prefixWord ++ tailWord_832425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832425).length < 2 ^ (prefixWord ++ tailWord_832425).sum := by decide
  have hdescent : baseEnd_832425 < baseStart_832425 := by decide
  rcases family_descends (prefixWord ++ tailWord_832425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832436 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_832436 : Nat := 118140960795 + 832436 * 2 ^ 59
def prefixEnd_832436 : Nat := 4983230072969 + 3 ^ 40 * 832436 * 2
def baseEnd_832436 : Nat := 142479927368736774673901

theorem tailTrace_832436 : CollatzResearch.WordTrace tailWord_832436 prefixEnd_832436 142479927368736774673901 := by
  unfold tailWord_832436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15180717606117007797638581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20240956808156010396851441 15180717606117007797638581)
  ·
    refine ⟨1423192275573469481028617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15180717606117007797638581 1423192275573469481028617)
    ·
      refine ⟨1067394206680102110771463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423192275573469481028617 1067394206680102110771463)
      ·
        refine ⟨1601091310020153166157195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067394206680102110771463 1601091310020153166157195)
        ·
          refine ⟨2401636965030229749235793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601091310020153166157195 2401636965030229749235793)
          ·
            refine ⟨1801227723772672311926845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401636965030229749235793 1801227723772672311926845)
            ·
              refine ⟨675460396414752116972567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1801227723772672311926845 675460396414752116972567)
              ·
                refine ⟨1013190594622128175458851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675460396414752116972567 1013190594622128175458851)
                ·
                  refine ⟨1519785891933192263188277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013190594622128175458851 1519785891933192263188277)
                  ·
                    refine ⟨142479927368736774673901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1519785891933192263188277 142479927368736774673901)
                    ·
                      rfl

theorem cell23_832436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_832436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832436 prefixEnd_832436 := by exact prefixLift 832436
  have htrace : WordTrace (prefixWord ++ tailWord_832436) baseStart_832436 baseEnd_832436 := by
    simpa [prefixWord, tailWord_832436, baseEnd_832436] using wordTrace_append hprefix tailTrace_832436
  have hstable : (prefixWord ++ tailWord_832436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832436).length < 2 ^ (prefixWord ++ tailWord_832436).sum := by decide
  have hdescent : baseEnd_832436 < baseStart_832436 := by decide
  rcases family_descends (prefixWord ++ tailWord_832436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832445 : List Nat := [1, 4, 1, 2, 5, 10]
def baseStart_832445 : Nat := 118140960795 + 832445 * 2 ^ 59
def prefixEnd_832445 : Nat := 4983230072969 + 3 ^ 40 * 832445 * 2
def baseEnd_832445 : Nat := 1759030466798768678227

theorem tailTrace_832445 : CollatzResearch.WordTrace tailWord_832445 prefixEnd_832445 1759030466798768678227 := by
  unfold tailWord_832445
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361763469201410132354789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20241175646134273421569859 30361763469201410132354789)
  ·
    refine ⟨5692830650475264399816523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30361763469201410132354789 5692830650475264399816523)
    ·
      refine ⟨8539245975712896599724785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692830650475264399816523 8539245975712896599724785)
      ·
        refine ⟨6404434481784672449793589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8539245975712896599724785 6404434481784672449793589)
        ·
          refine ⟨600415732667313042168149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6404434481784672449793589 600415732667313042168149)
          ·
            refine ⟨1759030466798768678227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 600415732667313042168149 1759030466798768678227)
            ·
              rfl

theorem cell23_832445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 10].length) (baseStart_832445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832445 prefixEnd_832445 := by exact prefixLift 832445
  have htrace : WordTrace (prefixWord ++ tailWord_832445) baseStart_832445 baseEnd_832445 := by
    simpa [prefixWord, tailWord_832445, baseEnd_832445] using wordTrace_append hprefix tailTrace_832445
  have hstable : (prefixWord ++ tailWord_832445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832445).length < 2 ^ (prefixWord ++ tailWord_832445).sum := by decide
  have hdescent : baseEnd_832445 < baseStart_832445 := by decide
  rcases family_descends (prefixWord ++ tailWord_832445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832472 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_832472 : Nat := 118140960795 + 832472 * 2 ^ 59
def prefixEnd_832472 : Nat := 4983230072969 + 3 ^ 40 * 832472 * 2
def baseEnd_832472 : Nat := 427458267409772183171537

theorem tailTrace_832472 : CollatzResearch.WordTrace tailWord_832472 prefixEnd_832472 427458267409772183171537 := by
  unfold tailWord_832472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15181374120051796871793835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20241832160069062495725113 15181374120051796871793835)
  ·
    refine ⟨22772061180077695307690753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15181374120051796871793835 22772061180077695307690753)
    ·
      refine ⟨17079045885058271480768065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22772061180077695307690753 17079045885058271480768065)
      ·
        refine ⟨12809284413793703610576049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17079045885058271480768065 12809284413793703610576049)
        ·
          refine ⟨9606963310345277707932037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12809284413793703610576049 9606963310345277707932037)
          ·
            refine ⟨1801305620689739570237257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9606963310345277707932037 1801305620689739570237257)
            ·
              refine ⟨1350979215517304677677943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801305620689739570237257 1350979215517304677677943)
              ·
                refine ⟨2026468823275957016516915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350979215517304677677943 2026468823275957016516915)
                ·
                  refine ⟨3039703234913935524775373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026468823275957016516915 3039703234913935524775373)
                  ·
                    refine ⟨1139888713092725821790765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039703234913935524775373 1139888713092725821790765)
                    ·
                      refine ⟨427458267409772183171537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1139888713092725821790765 427458267409772183171537)
                      ·
                        rfl

theorem cell23_832472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_832472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832472 prefixEnd_832472 := by exact prefixLift 832472
  have htrace : WordTrace (prefixWord ++ tailWord_832472) baseStart_832472 baseEnd_832472 := by
    simpa [prefixWord, tailWord_832472, baseEnd_832472] using wordTrace_append hprefix tailTrace_832472
  have hstable : (prefixWord ++ tailWord_832472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832472).length < 2 ^ (prefixWord ++ tailWord_832472).sum := by decide
  have hdescent : baseEnd_832472 < baseStart_832472 := by decide
  rcases family_descends (prefixWord ++ tailWord_832472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832529 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 2, 2, 2]
def baseStart_832529 : Nat := 118140960795 + 832529 * 2 ^ 59
def prefixEnd_832529 : Nat := 4983230072969 + 3 ^ 40 * 832529 * 2
def baseEnd_832529 : Nat := 427487535807078460158775

theorem tailTrace_832529 : CollatzResearch.WordTrace tailWord_832529 prefixEnd_832529 427487535807078460158775 := by
  unfold tailWord_832529
  simp only [CollatzResearch.WordTrace]
  refine ⟨30364827200897092478412641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20243218133931394985608427 30364827200897092478412641)
  ·
    refine ⟨22773620400672819358809481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30364827200897092478412641 22773620400672819358809481)
    ·
      refine ⟨17080215300504614519107111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22773620400672819358809481 17080215300504614519107111)
      ·
        refine ⟨25620322950756921778660667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17080215300504614519107111 25620322950756921778660667)
        ·
          refine ⟨38430484426135382667991001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25620322950756921778660667 38430484426135382667991001)
          ·
            refine ⟨28822863319601537000993251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38430484426135382667991001 28822863319601537000993251)
            ·
              refine ⟨43234294979402305501489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28822863319601537000993251 43234294979402305501489877)
              ·
                refine ⟨1013303788579741535191169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43234294979402305501489877 1013303788579741535191169)
                ·
                  refine ⟨759977841434806151393377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013303788579741535191169 759977841434806151393377)
                  ·
                    refine ⟨569983381076104613545033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759977841434806151393377 569983381076104613545033)
                    ·
                      refine ⟨427487535807078460158775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 569983381076104613545033 427487535807078460158775)
                      ·
                        rfl

theorem cell23_832529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_832529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832529 prefixEnd_832529 := by exact prefixLift 832529
  have htrace : WordTrace (prefixWord ++ tailWord_832529) baseStart_832529 baseEnd_832529 := by
    simpa [prefixWord, tailWord_832529, baseEnd_832529] using wordTrace_append hprefix tailTrace_832529
  have hstable : (prefixWord ++ tailWord_832529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832529).length < 2 ^ (prefixWord ++ tailWord_832529).sum := by decide
  have hdescent : baseEnd_832529 < baseStart_832529 := by decide
  rcases family_descends (prefixWord ++ tailWord_832529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832585 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_832585 : Nat := 118140960795 + 832585 * 2 ^ 59
def prefixEnd_832585 : Nat := 4983230072969 + 3 ^ 40 * 832585 * 2
def baseEnd_832585 : Nat := 427516290723730241058517

theorem tailTrace_832585 : CollatzResearch.WordTrace tailWord_832585 prefixEnd_832585 427516290723730241058517 := by
  unfold tailWord_832585
  simp only [CollatzResearch.WordTrace]
  refine ⟨30366869688694214042451209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20244579792462809361634139 30366869688694214042451209)
  ·
    refine ⟨22775152266520660531838407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30366869688694214042451209 22775152266520660531838407)
    ·
      refine ⟨34162728399780990797757611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22775152266520660531838407 34162728399780990797757611)
      ·
        refine ⟨51244092599671486196636417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34162728399780990797757611 51244092599671486196636417)
        ·
          refine ⟨38433069449753614647477313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51244092599671486196636417 38433069449753614647477313)
          ·
            refine ⟨28824802087315210985607985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38433069449753614647477313 28824802087315210985607985)
            ·
              refine ⟨21618601565486408239205989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28824802087315210985607985 21618601565486408239205989)
              ·
                refine ⟨4053487793528701544851123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21618601565486408239205989 4053487793528701544851123)
                ·
                  refine ⟨6080231690293052317276685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053487793528701544851123 6080231690293052317276685)
                  ·
                    refine ⟨2280086883859894618978757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6080231690293052317276685 2280086883859894618978757)
                    ·
                      refine ⟨427516290723730241058517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2280086883859894618978757 427516290723730241058517)
                      ·
                        rfl

theorem cell23_832585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_832585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832585 prefixEnd_832585 := by exact prefixLift 832585
  have htrace : WordTrace (prefixWord ++ tailWord_832585) baseStart_832585 baseEnd_832585 := by
    simpa [prefixWord, tailWord_832585, baseEnd_832585] using wordTrace_append hprefix tailTrace_832585
  have hstable : (prefixWord ++ tailWord_832585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832585).length < 2 ^ (prefixWord ++ tailWord_832585).sum := by decide
  have hdescent : baseEnd_832585 < baseStart_832585 := by decide
  rcases family_descends (prefixWord ++ tailWord_832585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832602 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2]
def baseStart_832602 : Nat := 118140960795 + 832602 * 2 ^ 59
def prefixEnd_832602 : Nat := 4983230072969 + 3 ^ 40 * 832602 * 2
def baseEnd_832602 : Nat := 427525019894856674545939

theorem tailTrace_832602 : CollatzResearch.WordTrace tailWord_832602 prefixEnd_832602 427525019894856674545939 := by
  unfold tailWord_832602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7591872432408156486455015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20244993153088417297213373 7591872432408156486455015)
  ·
    refine ⟨11387808648612234729682523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7591872432408156486455015 11387808648612234729682523)
    ·
      refine ⟨17081712972918352094523785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11387808648612234729682523 17081712972918352094523785)
      ·
        refine ⟨12811284729688764070892839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17081712972918352094523785 12811284729688764070892839)
        ·
          refine ⟨19216927094533146106339259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12811284729688764070892839 19216927094533146106339259)
          ·
            refine ⟨28825390641799719159508889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19216927094533146106339259 28825390641799719159508889)
            ·
              refine ⟨21619042981349789369631667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28825390641799719159508889 21619042981349789369631667)
              ·
                refine ⟨32428564472024684054447501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21619042981349789369631667 32428564472024684054447501)
                ·
                  refine ⟨12160711677009256520417813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32428564472024684054447501 12160711677009256520417813)
                  ·
                    refine ⟨570033359859808899394585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12160711677009256520417813 570033359859808899394585)
                    ·
                      refine ⟨427525019894856674545939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570033359859808899394585 427525019894856674545939)
                      ·
                        rfl

theorem cell23_832602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_832602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832602 prefixEnd_832602 := by exact prefixLift 832602
  have htrace : WordTrace (prefixWord ++ tailWord_832602) baseStart_832602 baseEnd_832602 := by
    simpa [prefixWord, tailWord_832602, baseEnd_832602] using wordTrace_append hprefix tailTrace_832602
  have hstable : (prefixWord ++ tailWord_832602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832602).length < 2 ^ (prefixWord ++ tailWord_832602).sum := by decide
  have hdescent : baseEnd_832602 < baseStart_832602 := by decide
  rcases family_descends (prefixWord ++ tailWord_832602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832665 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_832665 : Nat := 118140960795 + 832665 * 2 ^ 59
def prefixEnd_832665 : Nat := 4983230072969 + 3 ^ 40 * 832665 * 2
def baseEnd_832665 : Nat := 427557369176089928058149

theorem tailTrace_832665 : CollatzResearch.WordTrace tailWord_832665 prefixEnd_832665 427557369176089928058149 := by
  unfold tailWord_832665
  simp only [CollatzResearch.WordTrace]
  refine ⟨30369787528404387705363449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20246525018936258470242299 30369787528404387705363449)
  ·
    refine ⟨22777340646303290779022587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30369787528404387705363449 22777340646303290779022587)
    ·
      refine ⟨34166010969454936168533881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22777340646303290779022587 34166010969454936168533881)
      ·
        refine ⟨25624508227091202126400411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34166010969454936168533881 25624508227091202126400411)
        ·
          refine ⟨38436762340636803189600617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25624508227091202126400411 38436762340636803189600617)
          ·
            refine ⟨28827571755477602392200463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38436762340636803189600617 28827571755477602392200463)
            ·
              refine ⟨43241357633216403588300695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28827571755477602392200463 43241357633216403588300695)
              ·
                refine ⟨64862036449824605382451043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43241357633216403588300695 64862036449824605382451043)
                ·
                  refine ⟨97293054674736908073676565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64862036449824605382451043 97293054674736908073676565)
                  ·
                    refine ⟨4560611937878292565953589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97293054674736908073676565 4560611937878292565953589)
                    ·
                      refine ⟨427557369176089928058149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4560611937878292565953589 427557369176089928058149)
                      ·
                        rfl

theorem cell23_832665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_832665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832665 prefixEnd_832665 := by exact prefixLift 832665
  have htrace : WordTrace (prefixWord ++ tailWord_832665) baseStart_832665 baseEnd_832665 := by
    simpa [prefixWord, tailWord_832665, baseEnd_832665] using wordTrace_append hprefix tailTrace_832665
  have hstable : (prefixWord ++ tailWord_832665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832665).length < 2 ^ (prefixWord ++ tailWord_832665).sum := by decide
  have hdescent : baseEnd_832665 < baseStart_832665 := by decide
  rcases family_descends (prefixWord ++ tailWord_832665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832669 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_832669 : Nat := 118140960795 + 832669 * 2 ^ 59
def prefixEnd_832669 : Nat := 4983230072969 + 3 ^ 40 * 832669 * 2
def baseEnd_832669 : Nat := 427559423098707912408131

theorem tailTrace_832669 : CollatzResearch.WordTrace tailWord_832669 prefixEnd_832669 427559423098707912408131 := by
  unfold tailWord_832669
  simp only [CollatzResearch.WordTrace]
  refine ⟨30369933420389896388509061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20246622280259930925672707 30369933420389896388509061)
  ·
    refine ⟨5694362516323105572845449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30369933420389896388509061 5694362516323105572845449)
    ·
      refine ⟨4270771887242329179634087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5694362516323105572845449 4270771887242329179634087)
      ·
        refine ⟨6406157830863493769451131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270771887242329179634087 6406157830863493769451131)
        ·
          refine ⟨9609236746295240654176697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6406157830863493769451131 9609236746295240654176697)
          ·
            refine ⟨7206927559721430490632523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9609236746295240654176697 7206927559721430490632523)
            ·
              refine ⟨10810391339582145735948785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206927559721430490632523 10810391339582145735948785)
              ·
                refine ⟨8107793504686609301961589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10810391339582145735948785 8107793504686609301961589)
                ·
                  refine ⟨760105641064369622058899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8107793504686609301961589 760105641064369622058899)
                  ·
                    refine ⟨1140158461596554433088349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 760105641064369622058899 1140158461596554433088349)
                    ·
                      refine ⟨427559423098707912408131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1140158461596554433088349 427559423098707912408131)
                      ·
                        rfl

theorem cell23_832669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_832669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832669 prefixEnd_832669 := by exact prefixLift 832669
  have htrace : WordTrace (prefixWord ++ tailWord_832669) baseStart_832669 baseEnd_832669 := by
    simpa [prefixWord, tailWord_832669, baseEnd_832669] using wordTrace_append hprefix tailTrace_832669
  have hstable : (prefixWord ++ tailWord_832669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832669).length < 2 ^ (prefixWord ++ tailWord_832669).sum := by decide
  have hdescent : baseEnd_832669 < baseStart_832669 := by decide
  rcases family_descends (prefixWord ++ tailWord_832669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832749 : List Nat := [1, 5, 1, 2, 2, 2, 2, 8]
def baseStart_832749 : Nat := 118140960795 + 832749 * 2 ^ 59
def prefixEnd_832749 : Nat := 4983230072969 + 3 ^ 40 * 832749 * 2
def baseEnd_832749 : Nat := 15837055613002503681769

theorem tailTrace_832749 : CollatzResearch.WordTrace tailWord_832749 prefixEnd_832749 15837055613002503681769 := by
  unfold tailWord_832749
  simp only [CollatzResearch.WordTrace]
  refine ⟨30372851260100070051421301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20248567506733380034280867 30372851260100070051421301)
  ·
    refine ⟨2847454805634381567320747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30372851260100070051421301 2847454805634381567320747)
    ·
      refine ⟨4271182208451572350981121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847454805634381567320747 4271182208451572350981121)
      ·
        refine ⟨3203386656338679263235841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4271182208451572350981121 3203386656338679263235841)
        ·
          refine ⟨2402539992254009447426881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3203386656338679263235841 2402539992254009447426881)
          ·
            refine ⟨1801904994190507085570161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402539992254009447426881 1801904994190507085570161)
            ·
              refine ⟨1351428745642880314177621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801904994190507085570161 1351428745642880314177621)
              ·
                refine ⟨15837055613002503681769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1351428745642880314177621 15837055613002503681769)
                ·
                  rfl

theorem cell23_832749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 8].length) (baseStart_832749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832749 prefixEnd_832749 := by exact prefixLift 832749
  have htrace : WordTrace (prefixWord ++ tailWord_832749) baseStart_832749 baseEnd_832749 := by
    simpa [prefixWord, tailWord_832749, baseEnd_832749] using wordTrace_append hprefix tailTrace_832749
  have hstable : (prefixWord ++ tailWord_832749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832749).length < 2 ^ (prefixWord ++ tailWord_832749).sum := by decide
  have hdescent : baseEnd_832749 < baseStart_832749 := by decide
  rcases family_descends (prefixWord ++ tailWord_832749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832776 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_832776 : Nat := 118140960795 + 832776 * 2 ^ 59
def prefixEnd_832776 : Nat := 4983230072969 + 3 ^ 40 * 832776 * 2
def baseEnd_832776 : Nat := 427614365528738993770139

theorem tailTrace_832776 : CollatzResearch.WordTrace tailWord_832776 prefixEnd_832776 427614365528738993770139 := by
  unfold tailWord_832776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186918015501126831327091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20249224020668169108436121 15186918015501126831327091)
  ·
    refine ⟨22780377023251690246990637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15186918015501126831327091 22780377023251690246990637)
    ·
      refine ⟨8542641383719383842621489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22780377023251690246990637 8542641383719383842621489)
      ·
        refine ⟨6406981037789537881966117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8542641383719383842621489 6406981037789537881966117)
        ·
          refine ⟨1201308944585538352868647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6406981037789537881966117 1201308944585538352868647)
          ·
            refine ⟨1801963416878307529302971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201308944585538352868647 1801963416878307529302971)
            ·
              refine ⟨2702945125317461293954457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801963416878307529302971 2702945125317461293954457)
              ·
                refine ⟨2027208843988095970465843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702945125317461293954457 2027208843988095970465843)
                ·
                  refine ⟨3040813265982143955698765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027208843988095970465843 3040813265982143955698765)
                  ·
                    refine ⟨1140304974743303983387037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040813265982143955698765 1140304974743303983387037)
                    ·
                      refine ⟨427614365528738993770139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1140304974743303983387037 427614365528738993770139)
                      ·
                        rfl

theorem cell23_832776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_832776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832776 prefixEnd_832776 := by exact prefixLift 832776
  have htrace : WordTrace (prefixWord ++ tailWord_832776) baseStart_832776 baseEnd_832776 := by
    simpa [prefixWord, tailWord_832776, baseEnd_832776] using wordTrace_append hprefix tailTrace_832776
  have hstable : (prefixWord ++ tailWord_832776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832776).length < 2 ^ (prefixWord ++ tailWord_832776).sum := by decide
  have hdescent : baseEnd_832776 < baseStart_832776 := by decide
  rcases family_descends (prefixWord ++ tailWord_832776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832816 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 1, 4, 2]
def baseStart_832816 : Nat := 118140960795 + 832816 * 2 ^ 59
def prefixEnd_832816 : Nat := 4983230072969 + 3 ^ 40 * 832816 * 2
def baseEnd_832816 : Nat := 427634904754918837269955

theorem tailTrace_832816 : CollatzResearch.WordTrace tailWord_832816 prefixEnd_832816 427634904754918837269955 := by
  unfold tailWord_832816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15187647475428670247055151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20250196633904893662740201 15187647475428670247055151)
  ·
    refine ⟨22781471213143005370582727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15187647475428670247055151 22781471213143005370582727)
    ·
      refine ⟨34172206819714508055874091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22781471213143005370582727 34172206819714508055874091)
      ·
        refine ⟨51258310229571762083811137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34172206819714508055874091 51258310229571762083811137)
        ·
          refine ⟨38443732672178821562858353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51258310229571762083811137 38443732672178821562858353)
          ·
            refine ⟨28832799504134116172143765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38443732672178821562858353 28832799504134116172143765)
            ·
              refine ⟨1351537476756286695569239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28832799504134116172143765 1351537476756286695569239)
              ·
                refine ⟨2027306215134430043353859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351537476756286695569239 2027306215134430043353859)
                ·
                  refine ⟨3040959322701645065030789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027306215134430043353859 3040959322701645065030789)
                  ·
                    refine ⟨570179873006558449693273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3040959322701645065030789 570179873006558449693273)
                    ·
                      refine ⟨427634904754918837269955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570179873006558449693273 427634904754918837269955)
                      ·
                        rfl

theorem cell23_832816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 4, 2].length) (baseStart_832816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832816 prefixEnd_832816 := by exact prefixLift 832816
  have htrace : WordTrace (prefixWord ++ tailWord_832816) baseStart_832816 baseEnd_832816 := by
    simpa [prefixWord, tailWord_832816, baseEnd_832816] using wordTrace_append hprefix tailTrace_832816
  have hstable : (prefixWord ++ tailWord_832816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832816).length < 2 ^ (prefixWord ++ tailWord_832816).sum := by decide
  have hdescent : baseEnd_832816 < baseStart_832816 := by decide
  rcases family_descends (prefixWord ++ tailWord_832816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832833 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_832833 : Nat := 118140960795 + 832833 * 2 ^ 59
def prefixEnd_832833 : Nat := 4983230072969 + 3 ^ 40 * 832833 * 2
def baseEnd_832833 : Nat := 427643633926045270757377

theorem tailTrace_832833 : CollatzResearch.WordTrace tailWord_832833 prefixEnd_832833 427643633926045270757377 := by
  unfold tailWord_832833
  simp only [CollatzResearch.WordTrace]
  refine ⟨30375914991795752397479153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20250609994530501598319435 30375914991795752397479153)
  ·
    refine ⟨22781936243846814298109365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30375914991795752397479153 22781936243846814298109365)
    ·
      refine ⟨2135806522860638840447753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22781936243846814298109365 2135806522860638840447753)
      ·
        refine ⟨1601854892145479130335815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2135806522860638840447753 1601854892145479130335815)
        ·
          refine ⟨2402782338218218695503723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601854892145479130335815 2402782338218218695503723)
          ·
            refine ⟨3604173507327328043255585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402782338218218695503723 3604173507327328043255585)
            ·
              refine ⟨2703130130495496032441689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604173507327328043255585 2703130130495496032441689)
              ·
                refine ⟨2027347597871622024331267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703130130495496032441689 2027347597871622024331267)
                ·
                  refine ⟨3041021396807433036496901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027347597871622024331267 3041021396807433036496901)
                  ·
                    refine ⟨570191511901393694343169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3041021396807433036496901 570191511901393694343169)
                    ·
                      refine ⟨427643633926045270757377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570191511901393694343169 427643633926045270757377)
                      ·
                        rfl

theorem cell23_832833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_832833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832833 prefixEnd_832833 := by exact prefixLift 832833
  have htrace : WordTrace (prefixWord ++ tailWord_832833) baseStart_832833 baseEnd_832833 := by
    simpa [prefixWord, tailWord_832833, baseEnd_832833] using wordTrace_append hprefix tailTrace_832833
  have hstable : (prefixWord ++ tailWord_832833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832833).length < 2 ^ (prefixWord ++ tailWord_832833).sum := by decide
  have hdescent : baseEnd_832833 < baseStart_832833 := by decide
  rcases family_descends (prefixWord ++ tailWord_832833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832849 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_832849 : Nat := 118140960795 + 832849 * 2 ^ 59
def prefixEnd_832849 : Nat := 4983230072969 + 3 ^ 40 * 832849 * 2
def baseEnd_832849 : Nat := 427651849616517208157303

theorem tailTrace_832849 : CollatzResearch.WordTrace tailWord_832849 prefixEnd_832849 427651849616517208157303 := by
  unfold tailWord_832849
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376498559737787130061601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20250999039825191420041067 30376498559737787130061601)
  ·
    refine ⟨22782373919803340347546201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30376498559737787130061601 22782373919803340347546201)
    ·
      refine ⟨17086780439852505260659651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22782373919803340347546201 17086780439852505260659651)
      ·
        refine ⟨25630170659778757890989477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17086780439852505260659651 25630170659778757890989477)
        ·
          refine ⟨4805656998708517104560527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25630170659778757890989477 4805656998708517104560527)
          ·
            refine ⟨7208485498062775656840791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805656998708517104560527 7208485498062775656840791)
            ·
              refine ⟨10812728247094163485261187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208485498062775656840791 10812728247094163485261187)
              ·
                refine ⟨16219092370641245227891781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812728247094163485261187 16219092370641245227891781)
                ·
                  refine ⟨3041079819495233480229709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16219092370641245227891781 3041079819495233480229709)
                  ·
                    refine ⟨1140404932310712555086141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041079819495233480229709 1140404932310712555086141)
                    ·
                      refine ⟨427651849616517208157303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1140404932310712555086141 427651849616517208157303)
                      ·
                        rfl

theorem cell23_832849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_832849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832849 prefixEnd_832849 := by exact prefixLift 832849
  have htrace : WordTrace (prefixWord ++ tailWord_832849) baseStart_832849 baseEnd_832849 := by
    simpa [prefixWord, tailWord_832849, baseEnd_832849] using wordTrace_append hprefix tailTrace_832849
  have hstable : (prefixWord ++ tailWord_832849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832849).length < 2 ^ (prefixWord ++ tailWord_832849).sum := by decide
  have hdescent : baseEnd_832849 < baseStart_832849 := by decide
  rcases family_descends (prefixWord ++ tailWord_832849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832866 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_832866 : Nat := 118140960795 + 832866 * 2 ^ 59
def prefixEnd_832866 : Nat := 4983230072969 + 3 ^ 40 * 832866 * 2
def baseEnd_832866 : Nat := 427660578787643641644725

theorem tailTrace_832866 : CollatzResearch.WordTrace tailWord_832866 prefixEnd_832866 427660578787643641644725 := by
  unfold tailWord_832866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7594279650169049758357613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20251412400450799355620301 7594279650169049758357613)
  ·
    refine ⟨2847854868813393659384105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7594279650169049758357613 2847854868813393659384105)
    ·
      refine ⟨2135891151610045244538079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2847854868813393659384105 2135891151610045244538079)
      ·
        refine ⟨3203836727415067866807119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135891151610045244538079 3203836727415067866807119)
        ·
          refine ⟨4805755091122601800210679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203836727415067866807119 4805755091122601800210679)
          ·
            refine ⟨7208632636683902700316019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805755091122601800210679 7208632636683902700316019)
            ·
              refine ⟨10812948955025854050474029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208632636683902700316019 10812948955025854050474029)
              ·
                refine ⟨4054855858134695268927761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10812948955025854050474029 4054855858134695268927761)
                ·
                  refine ⟨3041141893601021451695821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054855858134695268927761 3041141893601021451695821)
                  ·
                    refine ⟨1140428210100383044385933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041141893601021451695821 1140428210100383044385933)
                    ·
                      refine ⟨427660578787643641644725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1140428210100383044385933 427660578787643641644725)
                      ·
                        rfl

theorem cell23_832866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_832866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832866 prefixEnd_832866 := by exact prefixLift 832866
  have htrace : WordTrace (prefixWord ++ tailWord_832866) baseStart_832866 baseEnd_832866 := by
    simpa [prefixWord, tailWord_832866, baseEnd_832866] using wordTrace_append hprefix tailTrace_832866
  have hstable : (prefixWord ++ tailWord_832866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832866).length < 2 ^ (prefixWord ++ tailWord_832866).sum := by decide
  have hdescent : baseEnd_832866 < baseStart_832866 := by decide
  rcases family_descends (prefixWord ++ tailWord_832866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832889 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_832889 : Nat := 118140960795 + 832889 * 2 ^ 59
def prefixEnd_832889 : Nat := 4983230072969 + 3 ^ 40 * 832889 * 2
def baseEnd_832889 : Nat := 427672388842697051657119

theorem tailTrace_832889 : CollatzResearch.WordTrace tailWord_832889 prefixEnd_832889 427672388842697051657119 := by
  unfold tailWord_832889
  simp only [CollatzResearch.WordTrace]
  refine ⟨30377957479592873961517721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20251971653061915974345147 30377957479592873961517721)
  ·
    refine ⟨22783468109694655471138291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30377957479592873961517721 22783468109694655471138291)
    ·
      refine ⟨34175202164541983206707437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22783468109694655471138291 34175202164541983206707437)
      ·
        refine ⟨12815700811703243702515289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34175202164541983206707437 12815700811703243702515289)
        ·
          refine ⟨9611775608777432776886467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12815700811703243702515289 9611775608777432776886467)
          ·
            refine ⟨14417663413166149165329701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611775608777432776886467 14417663413166149165329701)
            ·
              refine ⟨2703311889968652968499319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14417663413166149165329701 2703311889968652968499319)
              ·
                refine ⟨4054967834952979452748979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703311889968652968499319 4054967834952979452748979)
                ·
                  refine ⟨6082451752429469179123469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054967834952979452748979 6082451752429469179123469)
                  ·
                    refine ⟨2280919407161050942171301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6082451752429469179123469 2280919407161050942171301)
                    ·
                      refine ⟨427672388842697051657119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2280919407161050942171301 427672388842697051657119)
                      ·
                        rfl

theorem cell23_832889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_832889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_832889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_832889 prefixEnd_832889 := by exact prefixLift 832889
  have htrace : WordTrace (prefixWord ++ tailWord_832889) baseStart_832889 baseEnd_832889 := by
    simpa [prefixWord, tailWord_832889, baseEnd_832889] using wordTrace_append hprefix tailTrace_832889
  have hstable : (prefixWord ++ tailWord_832889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832889).length < 2 ^ (prefixWord ++ tailWord_832889).sum := by decide
  have hdescent : baseEnd_832889 < baseStart_832889 := by decide
  rcases family_descends (prefixWord ++ tailWord_832889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833006 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_833006 : Nat := 118140960795 + 833006 * 2 ^ 59
def prefixEnd_833006 : Nat := 4983230072969 + 3 ^ 40 * 833006 * 2
def baseEnd_833006 : Nat := 142577488693091031298027

theorem tailTrace_833006 : CollatzResearch.WordTrace tailWord_833006 prefixEnd_833006 142577488693091031298027 := by
  unfold tailWord_833006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797778102521125367940859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20254816546779335295684581 3797778102521125367940859)
  ·
    refine ⟨5696667153781688051911289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3797778102521125367940859 5696667153781688051911289)
    ·
      refine ⟨4272500365336266038933467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5696667153781688051911289 4272500365336266038933467)
      ·
        refine ⟨6408750548004399058400201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272500365336266038933467 6408750548004399058400201)
        ·
          refine ⟨4806562911003299293800151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6408750548004399058400201 4806562911003299293800151)
          ·
            refine ⟨7209844366504948940700227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806562911003299293800151 7209844366504948940700227)
            ·
              refine ⟨10814766549757423411050341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209844366504948940700227 10814766549757423411050341)
              ·
                refine ⟨2027768728079516889571939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10814766549757423411050341 2027768728079516889571939)
                ·
                  refine ⟨3041653092119275334357909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027768728079516889571939 3041653092119275334357909)
                  ·
                    refine ⟨142577488693091031298027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3041653092119275334357909 142577488693091031298027)
                    ·
                      rfl

theorem cell23_833006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_833006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833006 prefixEnd_833006 := by exact prefixLift 833006
  have htrace : WordTrace (prefixWord ++ tailWord_833006) baseStart_833006 baseEnd_833006 := by
    simpa [prefixWord, tailWord_833006, baseEnd_833006] using wordTrace_append hprefix tailTrace_833006
  have hstable : (prefixWord ++ tailWord_833006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833006).length < 2 ^ (prefixWord ++ tailWord_833006).sum := by decide
  have hdescent : baseEnd_833006 < baseStart_833006 := by decide
  rcases family_descends (prefixWord ++ tailWord_833006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833010 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_833010 : Nat := 118140960795 + 833010 * 2 ^ 59
def prefixEnd_833010 : Nat := 4983230072969 + 3 ^ 40 * 833010 * 2
def baseEnd_833010 : Nat := 142578173333963692748021

theorem tailTrace_833010 : CollatzResearch.WordTrace tailWord_833010 prefixEnd_833010 142578173333963692748021 := by
  unfold tailWord_833010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595592678038627906668121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20254913808103007751114989 7595592678038627906668121)
  ·
    refine ⟨5696694508528970930001091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7595592678038627906668121 5696694508528970930001091)
    ·
      refine ⟨8545041762793456395001637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5696694508528970930001091 8545041762793456395001637)
      ·
        refine ⟨1602195330523773074062807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8545041762793456395001637 1602195330523773074062807)
        ·
          refine ⟨2403292995785659611094211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602195330523773074062807 2403292995785659611094211)
          ·
            refine ⟨3604939493678489416641317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403292995785659611094211 3604939493678489416641317)
            ·
              refine ⟨675926155064716765620247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3604939493678489416641317 675926155064716765620247)
              ·
                refine ⟨1013889232597075148430371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675926155064716765620247 1013889232597075148430371)
                ·
                  refine ⟨1520833848895612722645557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013889232597075148430371 1520833848895612722645557)
                  ·
                    refine ⟨142578173333963692748021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1520833848895612722645557 142578173333963692748021)
                    ·
                      rfl

theorem cell23_833010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_833010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833010 prefixEnd_833010 := by exact prefixLift 833010
  have htrace : WordTrace (prefixWord ++ tailWord_833010) baseStart_833010 baseEnd_833010 := by
    simpa [prefixWord, tailWord_833010, baseEnd_833010] using wordTrace_append hprefix tailTrace_833010
  have hstable : (prefixWord ++ tailWord_833010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833010).length < 2 ^ (prefixWord ++ tailWord_833010).sum := by decide
  have hdescent : baseEnd_833010 < baseStart_833010 := by decide
  rcases family_descends (prefixWord ++ tailWord_833010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833029 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_833029 : Nat := 118140960795 + 833029 * 2 ^ 59
def prefixEnd_833029 : Nat := 4983230072969 + 3 ^ 40 * 833029 * 2
def baseEnd_833029 : Nat := 427744276134326503906475

theorem tailTrace_833029 : CollatzResearch.WordTrace tailWord_833029 prefixEnd_833029 427744276134326503906475 := by
  unfold tailWord_833029
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383063699085677871614141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20255375799390451914409427 30383063699085677871614141)
  ·
    refine ⟨11393648887157129201855303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30383063699085677871614141 11393648887157129201855303)
    ·
      refine ⟨17090473330735693802782955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11393648887157129201855303 17090473330735693802782955)
      ·
        refine ⟨25635709996103540704174433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17090473330735693802782955 25635709996103540704174433)
        ·
          refine ⟨19226782497077655528130825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25635709996103540704174433 19226782497077655528130825)
          ·
            refine ⟨14420086872808241646098119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19226782497077655528130825 14420086872808241646098119)
            ·
              refine ⟨21630130309212362469147179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420086872808241646098119 21630130309212362469147179)
              ·
                refine ⟨32445195463818543703720769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21630130309212362469147179 32445195463818543703720769)
                ·
                  refine ⟨24333896597863907777790577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32445195463818543703720769 24333896597863907777790577)
                  ·
                    refine ⟨18250422448397930833342933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24333896597863907777790577 18250422448397930833342933)
                    ·
                      refine ⟨427744276134326503906475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18250422448397930833342933 427744276134326503906475)
                      ·
                        rfl

theorem cell23_833029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_833029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833029 prefixEnd_833029 := by exact prefixLift 833029
  have htrace : WordTrace (prefixWord ++ tailWord_833029) baseStart_833029 baseEnd_833029 := by
    simpa [prefixWord, tailWord_833029, baseEnd_833029] using wordTrace_append hprefix tailTrace_833029
  have hstable : (prefixWord ++ tailWord_833029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833029).length < 2 ^ (prefixWord ++ tailWord_833029).sum := by decide
  have hdescent : baseEnd_833029 < baseStart_833029 := by decide
  rcases family_descends (prefixWord ++ tailWord_833029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833043 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 4]
def baseStart_833043 : Nat := 118140960795 + 833043 * 2 ^ 59
def prefixEnd_833043 : Nat := 4983230072969 + 3 ^ 40 * 833043 * 2
def baseEnd_833043 : Nat := 427751464863489449131411

theorem tailTrace_833043 : CollatzResearch.WordTrace tailWord_833043 prefixEnd_833043 427751464863489449131411 := by
  unfold tailWord_833043
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383574321034958262623783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20255716214023305508415855 30383574321034958262623783)
  ·
    refine ⟨45575361481552437393935675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30383574321034958262623783 45575361481552437393935675)
    ·
      refine ⟨68363042222328656090903513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45575361481552437393935675 68363042222328656090903513)
      ·
        refine ⟨51272281666746492068177635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68363042222328656090903513 51272281666746492068177635)
        ·
          refine ⟨76908422500119738102266453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51272281666746492068177635 76908422500119738102266453)
          ·
            refine ⟨901270576173278180885935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 76908422500119738102266453 901270576173278180885935)
            ·
              refine ⟨1351905864259917271328903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901270576173278180885935 1351905864259917271328903)
              ·
                refine ⟨2027858796389875906993355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351905864259917271328903 2027858796389875906993355)
                ·
                  refine ⟨3041788194584813860490033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027858796389875906993355 3041788194584813860490033)
                  ·
                    refine ⟨2281341145938610395367525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3041788194584813860490033 2281341145938610395367525)
                    ·
                      refine ⟨427751464863489449131411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2281341145938610395367525 427751464863489449131411)
                      ·
                        rfl

theorem cell23_833043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_833043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833043 prefixEnd_833043 := by exact prefixLift 833043
  have htrace : WordTrace (prefixWord ++ tailWord_833043) baseStart_833043 baseEnd_833043 := by
    simpa [prefixWord, tailWord_833043, baseEnd_833043] using wordTrace_append hprefix tailTrace_833043
  have hstable : (prefixWord ++ tailWord_833043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833043).length < 2 ^ (prefixWord ++ tailWord_833043).sum := by decide
  have hdescent : baseEnd_833043 < baseStart_833043 := by decide
  rcases family_descends (prefixWord ++ tailWord_833043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833073 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 5, 3, 2]
def baseStart_833073 : Nat := 118140960795 + 833073 * 2 ^ 59
def prefixEnd_833073 : Nat := 4983230072969 + 3 ^ 40 * 833073 * 2
def baseEnd_833073 : Nat := 427766869283124331756273

theorem tailTrace_833073 : CollatzResearch.WordTrace tailWord_833073 prefixEnd_833073 427766869283124331756273 := by
  unfold tailWord_833073
  simp only [CollatzResearch.WordTrace]
  refine ⟨30384668510926273386215873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20256445673950848924143915 30384668510926273386215873)
  ·
    refine ⟨22788501383194705039661905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30384668510926273386215873 22788501383194705039661905)
    ·
      refine ⟨17091376037396028779746429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22788501383194705039661905 17091376037396028779746429)
      ·
        refine ⟨6409266014023510792404911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17091376037396028779746429 6409266014023510792404911)
        ·
          refine ⟨9613899021035266188607367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409266014023510792404911 9613899021035266188607367)
          ·
            refine ⟨14420848531552899282911051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613899021035266188607367 14420848531552899282911051)
            ·
              refine ⟨21631272797329348924366577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420848531552899282911051 21631272797329348924366577)
              ·
                refine ⟨16223454597997011693274933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21631272797329348924366577 16223454597997011693274933)
                ·
                  refine ⟨1520948868562219846244525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16223454597997011693274933 1520948868562219846244525)
                  ·
                    refine ⟨570355825710832442341697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520948868562219846244525 570355825710832442341697)
                    ·
                      refine ⟨427766869283124331756273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570355825710832442341697 427766869283124331756273)
                      ·
                        rfl

theorem cell23_833073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_833073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833073 prefixEnd_833073 := by exact prefixLift 833073
  have htrace : WordTrace (prefixWord ++ tailWord_833073) baseStart_833073 baseEnd_833073 := by
    simpa [prefixWord, tailWord_833073, baseEnd_833073] using wordTrace_append hprefix tailTrace_833073
  have hstable : (prefixWord ++ tailWord_833073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833073).length < 2 ^ (prefixWord ++ tailWord_833073).sum := by decide
  have hdescent : baseEnd_833073 < baseStart_833073 := by decide
  rcases family_descends (prefixWord ++ tailWord_833073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833103 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 1, 4, 2]
def baseStart_833103 : Nat := 118140960795 + 833103 * 2 ^ 59
def prefixEnd_833103 : Nat := 4983230072969 + 3 ^ 40 * 833103 * 2
def baseEnd_833103 : Nat := 427782273702759214381135

theorem tailTrace_833103 : CollatzResearch.WordTrace tailWord_833103 prefixEnd_833103 427782273702759214381135 := by
  unfold tailWord_833103
  simp only [CollatzResearch.WordTrace]
  refine ⟨30385762700817588509807963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20257175133878392339871975 30385762700817588509807963)
  ·
    refine ⟨45578644051226382764711945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30385762700817588509807963 45578644051226382764711945)
    ·
      refine ⟨34183983038419787073533959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45578644051226382764711945 34183983038419787073533959)
      ·
        refine ⟨51275974557629680610300939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34183983038419787073533959 51275974557629680610300939)
        ·
          refine ⟨76913961836444520915451409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51275974557629680610300939 76913961836444520915451409)
          ·
            refine ⟨57685471377333390686588557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76913961836444520915451409 57685471377333390686588557)
            ·
              refine ⟨21632051766500021507470709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57685471377333390686588557 21632051766500021507470709)
              ·
                refine ⟨2028004853109377016325379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21632051766500021507470709 2028004853109377016325379)
                ·
                  refine ⟨3042007279664065524488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028004853109377016325379 3042007279664065524488069)
                  ·
                    refine ⟨570376364937012285841513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042007279664065524488069 570376364937012285841513)
                    ·
                      refine ⟨427782273702759214381135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570376364937012285841513 427782273702759214381135)
                      ·
                        rfl

theorem cell23_833103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4, 2].length) (baseStart_833103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833103 prefixEnd_833103 := by exact prefixLift 833103
  have htrace : WordTrace (prefixWord ++ tailWord_833103) baseStart_833103 baseEnd_833103 := by
    simpa [prefixWord, tailWord_833103, baseEnd_833103] using wordTrace_append hprefix tailTrace_833103
  have hstable : (prefixWord ++ tailWord_833103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833103).length < 2 ^ (prefixWord ++ tailWord_833103).sum := by decide
  have hdescent : baseEnd_833103 < baseStart_833103 := by decide
  rcases family_descends (prefixWord ++ tailWord_833103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833153 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_833153 : Nat := 118140960795 + 833153 * 2 ^ 59
def prefixEnd_833153 : Nat := 4983230072969 + 3 ^ 40 * 833153 * 2
def baseEnd_833153 : Nat := 427807947735484018755905

theorem tailTrace_833153 : CollatzResearch.WordTrace tailWord_833153 prefixEnd_833153 427807947735484018755905 := by
  unfold tailWord_833153
  simp only [CollatzResearch.WordTrace]
  refine ⟨30387586350636447049128113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20258390900424298032752075 30387586350636447049128113)
  ·
    refine ⟨22790689762977335286846085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30387586350636447049128113 22790689762977335286846085)
    ·
      refine ⟨4273254330558250366283641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22790689762977335286846085 4273254330558250366283641)
      ·
        refine ⟨3204940747918687774712731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273254330558250366283641 3204940747918687774712731)
        ·
          refine ⟨4807411121878031662069097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204940747918687774712731 4807411121878031662069097)
          ·
            refine ⟨3605558341408523746551823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807411121878031662069097 3605558341408523746551823)
            ·
              refine ⟨5408337512112785619827735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605558341408523746551823 5408337512112785619827735)
              ·
                refine ⟨8112506268169178429741603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408337512112785619827735 8112506268169178429741603)
                ·
                  refine ⟨12168759402253767644612405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8112506268169178429741603 12168759402253767644612405)
                  ·
                    refine ⟨1140821193961290716682413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12168759402253767644612405 1140821193961290716682413)
                    ·
                      refine ⟨427807947735484018755905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1140821193961290716682413 427807947735484018755905)
                      ·
                        rfl

theorem cell23_833153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_833153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833153 prefixEnd_833153 := by exact prefixLift 833153
  have htrace : WordTrace (prefixWord ++ tailWord_833153) baseStart_833153 baseEnd_833153 := by
    simpa [prefixWord, tailWord_833153, baseEnd_833153] using wordTrace_append hprefix tailTrace_833153
  have hstable : (prefixWord ++ tailWord_833153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833153).length < 2 ^ (prefixWord ++ tailWord_833153).sum := by decide
  have hdescent : baseEnd_833153 < baseStart_833153 := by decide
  rcases family_descends (prefixWord ++ tailWord_833153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833160 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 7]
def baseStart_833160 : Nat := 118140960795 + 833160 * 2 ^ 59
def prefixEnd_833160 : Nat := 4983230072969 + 3 ^ 40 * 833160 * 2
def baseEnd_833160 : Nat := 47534615788896165707597

theorem tailTrace_833160 : CollatzResearch.WordTrace tailWord_833160 prefixEnd_833160 47534615788896165707597 := by
  unfold tailWord_833160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193920830805543622316467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20258561107740724829755289 15193920830805543622316467)
  ·
    refine ⟨22790881246208315433474701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15193920830805543622316467 22790881246208315433474701)
    ·
      refine ⟨8546580467328118287553013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22790881246208315433474701 8546580467328118287553013)
      ·
        refine ⟨801241918812011089458095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8546580467328118287553013 801241918812011089458095)
        ·
          refine ⟨1201862878218016634187143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801241918812011089458095 1201862878218016634187143)
          ·
            refine ⟨1802794317327024951280715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201862878218016634187143 1802794317327024951280715)
            ·
              refine ⟨2704191475990537426921073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802794317327024951280715 2704191475990537426921073)
              ·
                refine ⟨2028143606992903070190805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704191475990537426921073 2028143606992903070190805)
                ·
                  refine ⟨47534615788896165707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2028143606992903070190805 47534615788896165707597)
                  ·
                    rfl

theorem cell23_833160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 7].length) (baseStart_833160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833160 prefixEnd_833160 := by exact prefixLift 833160
  have htrace : WordTrace (prefixWord ++ tailWord_833160) baseStart_833160 baseEnd_833160 := by
    simpa [prefixWord, tailWord_833160, baseEnd_833160] using wordTrace_append hprefix tailTrace_833160
  have hstable : (prefixWord ++ tailWord_833160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833160).length < 2 ^ (prefixWord ++ tailWord_833160).sum := by decide
  have hdescent : baseEnd_833160 < baseStart_833160 := by decide
  rcases family_descends (prefixWord ++ tailWord_833160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833163 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 2, 5, 2]
def baseStart_833163 : Nat := 118140960795 + 833163 * 2 ^ 59
def prefixEnd_833163 : Nat := 4983230072969 + 3 ^ 40 * 833163 * 2
def baseEnd_833163 : Nat := 427813082542028979630859

theorem tailTrace_833163 : CollatzResearch.WordTrace tailWord_833163 prefixEnd_833163 427813082542028979630859 := by
  unfold tailWord_833163
  simp only [CollatzResearch.WordTrace]
  refine ⟨30387951080600218756992143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20258634053733479171328095 30387951080600218756992143)
  ·
    refine ⟨45581926620900328135488215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30387951080600218756992143 45581926620900328135488215)
    ·
      refine ⟨68372889931350492203232323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45581926620900328135488215 68372889931350492203232323)
      ·
        refine ⟨102559334897025738304848485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68372889931350492203232323 102559334897025738304848485)
        ·
          refine ⟨19229875293192325932159091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102559334897025738304848485 19229875293192325932159091)
          ·
            refine ⟨28844812939788488898238637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19229875293192325932159091 28844812939788488898238637)
            ·
              refine ⟨10816804852420683336839489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28844812939788488898238637 10816804852420683336839489)
              ·
                refine ⟨8112603639315512502629617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10816804852420683336839489 8112603639315512502629617)
                ·
                  refine ⟨6084452729486634376972213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8112603639315512502629617 6084452729486634376972213)
                  ·
                    refine ⟨570417443389371972841145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6084452729486634376972213 570417443389371972841145)
                    ·
                      refine ⟨427813082542028979630859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570417443389371972841145 427813082542028979630859)
                      ·
                        rfl

theorem cell23_833163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5, 2].length) (baseStart_833163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833163 prefixEnd_833163 := by exact prefixLift 833163
  have htrace : WordTrace (prefixWord ++ tailWord_833163) baseStart_833163 baseEnd_833163 := by
    simpa [prefixWord, tailWord_833163, baseEnd_833163] using wordTrace_append hprefix tailTrace_833163
  have hstable : (prefixWord ++ tailWord_833163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833163).length < 2 ^ (prefixWord ++ tailWord_833163).sum := by decide
  have hdescent : baseEnd_833163 < baseStart_833163 := by decide
  rcases family_descends (prefixWord ++ tailWord_833163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833210 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2]
def baseStart_833210 : Nat := 118140960795 + 833210 * 2 ^ 59
def prefixEnd_833210 : Nat := 4983230072969 + 3 ^ 40 * 833210 * 2
def baseEnd_833210 : Nat := 427837216132790295743143

theorem tailTrace_833210 : CollatzResearch.WordTrace tailWord_833210 prefixEnd_833210 427837216132790295743143 := by
  unfold tailWord_833210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597416327857486445988271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20259776874286630522635389 7597416327857486445988271)
  ·
    refine ⟨11396124491786229668982407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7597416327857486445988271 11396124491786229668982407)
    ·
      refine ⟨17094186737679344503473611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11396124491786229668982407 17094186737679344503473611)
      ·
        refine ⟨25641280106519016755210417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17094186737679344503473611 25641280106519016755210417)
        ·
          refine ⟨19230960079889262566407813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25641280106519016755210417 19230960079889262566407813)
          ·
            refine ⟨3605805014979236731201465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19230960079889262566407813 3605805014979236731201465)
            ·
              refine ⟨2704353761234427548401099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605805014979236731201465 2704353761234427548401099)
              ·
                refine ⟨4056530641851641322601649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704353761234427548401099 4056530641851641322601649)
                ·
                  refine ⟨3042397981388730991951237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056530641851641322601649 3042397981388730991951237)
                  ·
                    refine ⟨570449621510387060990857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042397981388730991951237 570449621510387060990857)
                    ·
                      refine ⟨427837216132790295743143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570449621510387060990857 427837216132790295743143)
                      ·
                        rfl

theorem cell23_833210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_833210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833210 prefixEnd_833210 := by exact prefixLift 833210
  have htrace : WordTrace (prefixWord ++ tailWord_833210) baseStart_833210 baseEnd_833210 := by
    simpa [prefixWord, tailWord_833210, baseEnd_833210] using wordTrace_append hprefix tailTrace_833210
  have hstable : (prefixWord ++ tailWord_833210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833210).length < 2 ^ (prefixWord ++ tailWord_833210).sum := by decide
  have hdescent : baseEnd_833210 < baseStart_833210 := by decide
  rcases family_descends (prefixWord ++ tailWord_833210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833213 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_833213 : Nat := 118140960795 + 833213 * 2 ^ 59
def prefixEnd_833213 : Nat := 4983230072969 + 3 ^ 40 * 833213 * 2
def baseEnd_833213 : Nat := 427838756574753784005629

theorem tailTrace_833213 : CollatzResearch.WordTrace tailWord_833213 prefixEnd_833213 427838756574753784005629 := by
  unfold tailWord_833213
  simp only [CollatzResearch.WordTrace]
  refine ⟨30389774730419077296312293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20259849820279384864208195 30389774730419077296312293)
  ·
    refine ⟨5698082761953576993058555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30389774730419077296312293 5698082761953576993058555)
    ·
      refine ⟨8547124142930365489587833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698082761953576993058555 8547124142930365489587833)
      ·
        refine ⟨6410343107197774117190875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8547124142930365489587833 6410343107197774117190875)
        ·
          refine ⟨9615514660796661175786313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410343107197774117190875 9615514660796661175786313)
          ·
            refine ⟨7211635995597495881839735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9615514660796661175786313 7211635995597495881839735)
            ·
              refine ⟨10817453993396243822759603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211635995597495881839735 10817453993396243822759603)
              ·
                refine ⟨16226180990094365734139405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817453993396243822759603 16226180990094365734139405)
                ·
                  refine ⟨6084817871285387150302277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16226180990094365734139405 6084817871285387150302277)
                  ·
                    refine ⟨1140903350866010090681677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084817871285387150302277 1140903350866010090681677)
                    ·
                      refine ⟨427838756574753784005629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1140903350866010090681677 427838756574753784005629)
                      ·
                        rfl

theorem cell23_833213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_833213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833213 prefixEnd_833213 := by exact prefixLift 833213
  have htrace : WordTrace (prefixWord ++ tailWord_833213) baseStart_833213 baseEnd_833213 := by
    simpa [prefixWord, tailWord_833213, baseEnd_833213] using wordTrace_append hprefix tailTrace_833213
  have hstable : (prefixWord ++ tailWord_833213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833213).length < 2 ^ (prefixWord ++ tailWord_833213).sum := by decide
  have hdescent : baseEnd_833213 < baseStart_833213 := by decide
  rcases family_descends (prefixWord ++ tailWord_833213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833220 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_833220 : Nat := 118140960795 + 833220 * 2 ^ 59
def prefixEnd_833220 : Nat := 4983230072969 + 3 ^ 40 * 833220 * 2
def baseEnd_833220 : Nat := 142614116979778418872699

theorem tailTrace_833220 : CollatzResearch.WordTrace tailWord_833220 prefixEnd_833220 142614116979778418872699 := by
  unfold tailWord_833220
  simp only [CollatzResearch.WordTrace]
  refine ⟨15195015020696858745908557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20260020027595811661211409 15195015020696858745908557)
  ·
    refine ⟨5698130632761322029715709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15195015020696858745908557 5698130632761322029715709)
    ·
      refine ⟨2136798987285495761143391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5698130632761322029715709 2136798987285495761143391)
      ·
        refine ⟨3205198480928243641715087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136798987285495761143391 3205198480928243641715087)
        ·
          refine ⟨4807797721392365462572631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205198480928243641715087 4807797721392365462572631)
          ·
            refine ⟨7211696582088548193858947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807797721392365462572631 7211696582088548193858947)
            ·
              refine ⟨10817544873132822290788421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211696582088548193858947 10817544873132822290788421)
              ·
                refine ⟨2028289663712404179522829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10817544873132822290788421 2028289663712404179522829)
                ·
                  refine ⟨760608623892151567321061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2028289663712404179522829 760608623892151567321061)
                  ·
                    refine ⟨142614116979778418872699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760608623892151567321061 142614116979778418872699)
                    ·
                      rfl

theorem cell23_833220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_833220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833220 prefixEnd_833220 := by exact prefixLift 833220
  have htrace : WordTrace (prefixWord ++ tailWord_833220) baseStart_833220 baseEnd_833220 := by
    simpa [prefixWord, tailWord_833220, baseEnd_833220] using wordTrace_append hprefix tailTrace_833220
  have hstable : (prefixWord ++ tailWord_833220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833220).length < 2 ^ (prefixWord ++ tailWord_833220).sum := by decide
  have hdescent : baseEnd_833220 < baseStart_833220 := by decide
  rcases family_descends (prefixWord ++ tailWord_833220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833230 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_833230 : Nat := 118140960795 + 833230 * 2 ^ 59
def prefixEnd_833230 : Nat := 4983230072969 + 3 ^ 40 * 833230 * 2
def baseEnd_833230 : Nat := 427847485745880217493051

theorem tailTrace_833230 : CollatzResearch.WordTrace tailWord_833230 prefixEnd_833230 427847485745880217493051 := by
  unfold tailWord_833230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798799346419686149960143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20260263180904992799787429 3798799346419686149960143)
  ·
    refine ⟨5698199019629529224940215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3798799346419686149960143 5698199019629529224940215)
    ·
      refine ⟨8547298529444293837410323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698199019629529224940215 8547298529444293837410323)
      ·
        refine ⟨12820947794166440756115485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547298529444293837410323 12820947794166440756115485)
        ·
          refine ⟨4807855422812415283543307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12820947794166440756115485 4807855422812415283543307)
          ·
            refine ⟨7211783134218622925314961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807855422812415283543307 7211783134218622925314961)
            ·
              refine ⟨5408837350663967193986221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211783134218622925314961 5408837350663967193986221)
              ·
                refine ⟨2028314006498987697744833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5408837350663967193986221 2028314006498987697744833)
                ·
                  refine ⟨1521235504874240773308625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028314006498987697744833 1521235504874240773308625)
                  ·
                    refine ⟨1140926628655680579981469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1521235504874240773308625 1140926628655680579981469)
                    ·
                      refine ⟨427847485745880217493051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1140926628655680579981469 427847485745880217493051)
                      ·
                        rfl

theorem cell23_833230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_833230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833230 prefixEnd_833230 := by exact prefixLift 833230
  have htrace : WordTrace (prefixWord ++ tailWord_833230) baseStart_833230 baseEnd_833230 := by
    simpa [prefixWord, tailWord_833230, baseEnd_833230] using wordTrace_append hprefix tailTrace_833230
  have hstable : (prefixWord ++ tailWord_833230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833230).length < 2 ^ (prefixWord ++ tailWord_833230).sum := by decide
  have hdescent : baseEnd_833230 < baseStart_833230 := by decide
  rcases family_descends (prefixWord ++ tailWord_833230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833263 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 3, 5]
def baseStart_833263 : Nat := 118140960795 + 833263 * 2 ^ 59
def prefixEnd_833263 : Nat := 4983230072969 + 3 ^ 40 * 833263 * 2
def baseEnd_833263 : Nat := 142621476869159529460133

theorem tailTrace_833263 : CollatzResearch.WordTrace tailWord_833263 prefixEnd_833263 142621476869159529460133 := by
  unfold tailWord_833263
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391598380237935835632443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20261065586825290557088295 30391598380237935835632443)
  ·
    refine ⟨45587397570356903753448665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30391598380237935835632443 45587397570356903753448665)
    ·
      refine ⟨34190548177767677815086499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45587397570356903753448665 34190548177767677815086499)
      ·
        refine ⟨51285822266651516722629749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34190548177767677815086499 51285822266651516722629749)
        ·
          refine ⟨4808045837498579692746539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51285822266651516722629749 4808045837498579692746539)
          ·
            refine ⟨7212068756247869539119809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808045837498579692746539 7212068756247869539119809)
            ·
              refine ⟨5409051567185902154339857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7212068756247869539119809 5409051567185902154339857)
              ·
                refine ⟨4056788675389426615754893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409051567185902154339857 4056788675389426615754893)
                ·
                  refine ⟨1521295753271034980908085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4056788675389426615754893 1521295753271034980908085)
                  ·
                    refine ⟨142621476869159529460133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1521295753271034980908085 142621476869159529460133)
                    ·
                      rfl

theorem cell23_833263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_833263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833263 prefixEnd_833263 := by exact prefixLift 833263
  have htrace : WordTrace (prefixWord ++ tailWord_833263) baseStart_833263 baseEnd_833263 := by
    simpa [prefixWord, tailWord_833263, baseEnd_833263] using wordTrace_append hprefix tailTrace_833263
  have hstable : (prefixWord ++ tailWord_833263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833263).length < 2 ^ (prefixWord ++ tailWord_833263).sum := by decide
  have hdescent : baseEnd_833263 < baseStart_833263 := by decide
  rcases family_descends (prefixWord ++ tailWord_833263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833330 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_833330 : Nat := 118140960795 + 833330 * 2 ^ 59
def prefixEnd_833330 : Nat := 4983230072969 + 3 ^ 40 * 833330 * 2
def baseEnd_833330 : Nat := 427898833811329826242591

theorem tailTrace_833330 : CollatzResearch.WordTrace tailWord_833330 prefixEnd_833330 427898833811329826242591 := by
  unfold tailWord_833330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7598510517748801569580361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20262694713996804185547629 7598510517748801569580361)
  ·
    refine ⟨5698882888311601177185271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7598510517748801569580361 5698882888311601177185271)
    ·
      refine ⟨8548324332467401765777907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698882888311601177185271 8548324332467401765777907)
      ·
        refine ⟨12822486498701102648666861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8548324332467401765777907 12822486498701102648666861)
        ·
          refine ⟨4808432437012913493250073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12822486498701102648666861 4808432437012913493250073)
          ·
            refine ⟨3606324327759685119937555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808432437012913493250073 3606324327759685119937555)
            ·
              refine ⟨5409486491639527679906333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606324327759685119937555 5409486491639527679906333)
              ·
                refine ⟨2028557434364822879964875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5409486491639527679906333 2028557434364822879964875)
                ·
                  refine ⟨3042836151547234319947313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028557434364822879964875 3042836151547234319947313)
                  ·
                    refine ⟨2282127113660425739960485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3042836151547234319947313 2282127113660425739960485)
                    ·
                      refine ⟨427898833811329826242591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2282127113660425739960485 427898833811329826242591)
                      ·
                        rfl

theorem cell23_833330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_833330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833330 prefixEnd_833330 := by exact prefixLift 833330
  have htrace : WordTrace (prefixWord ++ tailWord_833330) baseStart_833330 baseEnd_833330 := by
    simpa [prefixWord, tailWord_833330, baseEnd_833330] using wordTrace_append hprefix tailTrace_833330
  have hstable : (prefixWord ++ tailWord_833330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833330).length < 2 ^ (prefixWord ++ tailWord_833330).sum := by decide
  have hdescent : baseEnd_833330 < baseStart_833330 := by decide
  rcases family_descends (prefixWord ++ tailWord_833330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833440 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_833440 : Nat := 118140960795 + 833440 * 2 ^ 59
def prefixEnd_833440 : Nat := 4983230072969 + 3 ^ 40 * 833440 * 2
def baseEnd_833440 : Nat := 427955316683324395867085

theorem tailTrace_833440 : CollatzResearch.WordTrace tailWord_833440 prefixEnd_833440 427955316683324395867085 := by
  unfold tailWord_833440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15199027050298347532412887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20265369400397796709883849 15199027050298347532412887)
  ·
    refine ⟨22798540575447521298619331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15199027050298347532412887 22798540575447521298619331)
    ·
      refine ⟨34197810863171281947928997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22798540575447521298619331 34197810863171281947928997)
      ·
        refine ⟨6412089536844615365236687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34197810863171281947928997 6412089536844615365236687)
        ·
          refine ⟨9618134305266923047855031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6412089536844615365236687 9618134305266923047855031)
          ·
            refine ⟨14427201457900384571782547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618134305266923047855031 14427201457900384571782547)
            ·
              refine ⟨21640802186850576857673821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14427201457900384571782547 21640802186850576857673821)
              ·
                refine ⟨8115300820068966321627683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21640802186850576857673821 8115300820068966321627683)
                ·
                  refine ⟨12172951230103449482441525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8115300820068966321627683 12172951230103449482441525)
                  ·
                    refine ⟨1141214177822198388978893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12172951230103449482441525 1141214177822198388978893)
                    ·
                      refine ⟨427955316683324395867085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1141214177822198388978893 427955316683324395867085)
                      ·
                        rfl

theorem cell23_833440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_833440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833440 prefixEnd_833440 := by exact prefixLift 833440
  have htrace : WordTrace (prefixWord ++ tailWord_833440) baseStart_833440 baseEnd_833440 := by
    simpa [prefixWord, tailWord_833440, baseEnd_833440] using wordTrace_append hprefix tailTrace_833440
  have hstable : (prefixWord ++ tailWord_833440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833440).length < 2 ^ (prefixWord ++ tailWord_833440).sum := by decide
  have hdescent : baseEnd_833440 < baseStart_833440 := by decide
  rcases family_descends (prefixWord ++ tailWord_833440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833507 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 5, 4]
def baseStart_833507 : Nat := 118140960795 + 833507 * 2 ^ 59
def prefixEnd_833507 : Nat := 4983230072969 + 3 ^ 40 * 833507 * 2
def baseEnd_833507 : Nat := 142663239962391877909759

theorem tailTrace_833507 : CollatzResearch.WordTrace tailWord_833507 prefixEnd_833507 142663239962391877909759 := by
  unfold tailWord_833507
  simp only [CollatzResearch.WordTrace]
  refine ⟨30400497791353965507514775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20266998527569310338343183 30400497791353965507514775)
  ·
    refine ⟨45600746687030948261272163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30400497791353965507514775 45600746687030948261272163)
    ·
      refine ⟨68401120030546422391908245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45600746687030948261272163 68401120030546422391908245)
      ·
        refine ⟨3206302501431863549620699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68401120030546422391908245 3206302501431863549620699)
        ·
          refine ⟨4809453752147795324431049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206302501431863549620699 4809453752147795324431049)
          ·
            refine ⟨3607090314110846493323287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809453752147795324431049 3607090314110846493323287)
            ·
              refine ⟨5410635471166269739984931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607090314110846493323287 5410635471166269739984931)
              ·
                refine ⟨8115953206749404609977397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410635471166269739984931 8115953206749404609977397)
                ·
                  refine ⟨760870613132756682185381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8115953206749404609977397 760870613132756682185381)
                  ·
                    refine ⟨142663239962391877909759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760870613132756682185381 142663239962391877909759)
                    ·
                      rfl

theorem cell23_833507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 4].length) (baseStart_833507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833507 prefixEnd_833507 := by exact prefixLift 833507
  have htrace : WordTrace (prefixWord ++ tailWord_833507) baseStart_833507 baseEnd_833507 := by
    simpa [prefixWord, tailWord_833507, baseEnd_833507] using wordTrace_append hprefix tailTrace_833507
  have hstable : (prefixWord ++ tailWord_833507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833507).length < 2 ^ (prefixWord ++ tailWord_833507).sum := by decide
  have hdescent : baseEnd_833507 < baseStart_833507 := by decide
  rcases family_descends (prefixWord ++ tailWord_833507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833511 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 2, 5]
def baseStart_833511 : Nat := 118140960795 + 833511 * 2 ^ 59
def prefixEnd_833511 : Nat := 4983230072969 + 3 ^ 40 * 833511 * 2
def baseEnd_833511 : Nat := 142663924603264539359753

theorem tailTrace_833511 : CollatzResearch.WordTrace tailWord_833511 prefixEnd_833511 142663924603264539359753 := by
  unfold tailWord_833511
  simp only [CollatzResearch.WordTrace]
  refine ⟨30400643683339474190660387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20267095788892982793773591 30400643683339474190660387)
  ·
    refine ⟨45600965525009211285990581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30400643683339474190660387 45600965525009211285990581)
    ·
      refine ⟨4275090517969613558061617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45600965525009211285990581 4275090517969613558061617)
      ·
        refine ⟨3206317888477210168546213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4275090517969613558061617 3206317888477210168546213)
        ·
          refine ⟨601184604089476906602415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3206317888477210168546213 601184604089476906602415)
          ·
            refine ⟨901776906134215359903623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601184604089476906602415 901776906134215359903623)
            ·
              refine ⟨1352665359201323039855435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901776906134215359903623 1352665359201323039855435)
              ·
                refine ⟨2028998038801984559783153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352665359201323039855435 2028998038801984559783153)
                ·
                  refine ⟨1521748529101488419837365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028998038801984559783153 1521748529101488419837365)
                  ·
                    refine ⟨142663924603264539359753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1521748529101488419837365 142663924603264539359753)
                    ·
                      rfl

theorem cell23_833511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_833511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833511 prefixEnd_833511 := by exact prefixLift 833511
  have htrace : WordTrace (prefixWord ++ tailWord_833511) baseStart_833511 baseEnd_833511 := by
    simpa [prefixWord, tailWord_833511, baseEnd_833511] using wordTrace_append hprefix tailTrace_833511
  have hstable : (prefixWord ++ tailWord_833511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833511).length < 2 ^ (prefixWord ++ tailWord_833511).sum := by decide
  have hdescent : baseEnd_833511 < baseStart_833511 := by decide
  rcases family_descends (prefixWord ++ tailWord_833511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833575 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 1, 4]
def baseStart_833575 : Nat := 118140960795 + 833575 * 2 ^ 59
def prefixEnd_833575 : Nat := 4983230072969 + 3 ^ 40 * 833575 * 2
def baseEnd_833575 : Nat := 142674878857227122559655

theorem tailTrace_833575 : CollatzResearch.WordTrace tailWord_833575 prefixEnd_833575 142674878857227122559655 := by
  unfold tailWord_833575
  simp only [CollatzResearch.WordTrace]
  refine ⟨30402977955107613120990179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20268651970071742080660119 30402977955107613120990179)
  ·
    refine ⟨45604466932661419681485269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30402977955107613120990179 45604466932661419681485269)
    ·
      refine ⟨1068854693734252023784811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45604466932661419681485269 1068854693734252023784811)
      ·
        refine ⟨1603282040601378035677217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068854693734252023784811 1603282040601378035677217)
        ·
          refine ⟨1202461530451033526757913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603282040601378035677217 1202461530451033526757913)
          ·
            refine ⟨901846147838275145068435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202461530451033526757913 901846147838275145068435)
            ·
              refine ⟨1352769221757412717602653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901846147838275145068435 1352769221757412717602653)
              ·
                refine ⟨507288458159029769100995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352769221757412717602653 507288458159029769100995)
                ·
                  refine ⟨760932687238544653651493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507288458159029769100995 760932687238544653651493)
                  ·
                    refine ⟨142674878857227122559655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760932687238544653651493 142674878857227122559655)
                    ·
                      rfl

theorem cell23_833575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_833575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833575 prefixEnd_833575 := by exact prefixLift 833575
  have htrace : WordTrace (prefixWord ++ tailWord_833575) baseStart_833575 baseEnd_833575 := by
    simpa [prefixWord, tailWord_833575, baseEnd_833575] using wordTrace_append hprefix tailTrace_833575
  have hstable : (prefixWord ++ tailWord_833575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833575).length < 2 ^ (prefixWord ++ tailWord_833575).sum := by decide
  have hdescent : baseEnd_833575 < baseStart_833575 := by decide
  rcases family_descends (prefixWord ++ tailWord_833575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833607 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_833607 : Nat := 118140960795 + 833607 * 2 ^ 59
def prefixEnd_833607 : Nat := 4983230072969 + 3 ^ 40 * 833607 * 2
def baseEnd_833607 : Nat := 428041067952625242478817

theorem tailTrace_833607 : CollatzResearch.WordTrace tailWord_833607 prefixEnd_833607 428041067952625242478817 := by
  unfold tailWord_833607
  simp only [CollatzResearch.WordTrace]
  refine ⟨30404145090991682586155075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20269430060661121724103383 30404145090991682586155075)
  ·
    refine ⟨45606217636487523879232613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30404145090991682586155075 45606217636487523879232613)
    ·
      refine ⟨8551165806841410727356115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45606217636487523879232613 8551165806841410727356115)
      ·
        refine ⟨12826748710262116091034173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551165806841410727356115 12826748710262116091034173)
        ·
          refine ⟨4810030766348293534137815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12826748710262116091034173 4810030766348293534137815)
          ·
            refine ⟨7215046149522440301206723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810030766348293534137815 7215046149522440301206723)
            ·
              refine ⟨10822569224283660451810085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215046149522440301206723 10822569224283660451810085)
              ·
                refine ⟨2029231729553186334714391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10822569224283660451810085 2029231729553186334714391)
                ·
                  refine ⟨3043847594329779502071587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029231729553186334714391 3043847594329779502071587)
                  ·
                    refine ⟨4565771391494669253107381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043847594329779502071587 4565771391494669253107381)
                    ·
                      refine ⟨428041067952625242478817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4565771391494669253107381 428041067952625242478817)
                      ·
                        rfl

theorem cell23_833607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_833607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833607 prefixEnd_833607 := by exact prefixLift 833607
  have htrace : WordTrace (prefixWord ++ tailWord_833607) baseStart_833607 baseEnd_833607 := by
    simpa [prefixWord, tailWord_833607, baseEnd_833607] using wordTrace_append hprefix tailTrace_833607
  have hstable : (prefixWord ++ tailWord_833607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833607).length < 2 ^ (prefixWord ++ tailWord_833607).sum := by decide
  have hdescent : baseEnd_833607 < baseStart_833607 := by decide
  rcases family_descends (prefixWord ++ tailWord_833607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833617 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_833617 : Nat := 118140960795 + 833617 * 2 ^ 59
def prefixEnd_833617 : Nat := 4983230072969 + 3 ^ 40 * 833617 * 2
def baseEnd_833617 : Nat := 428046202759170203353771

theorem tailTrace_833617 : CollatzResearch.WordTrace tailWord_833617 prefixEnd_833617 428046202759170203353771 := by
  unfold tailWord_833617
  simp only [CollatzResearch.WordTrace]
  refine ⟨30404509820955454294019105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20269673213970302862679403 30404509820955454294019105)
  ·
    refine ⟨22803382365716590720514329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30404509820955454294019105 22803382365716590720514329)
    ·
      refine ⟨17102536774287443040385747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22803382365716590720514329 17102536774287443040385747)
      ·
        refine ⟨25653805161431164560578621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17102536774287443040385747 25653805161431164560578621)
        ·
          refine ⟨9620176935536686710216983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25653805161431164560578621 9620176935536686710216983)
          ·
            refine ⟨14430265403305030065325475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620176935536686710216983 14430265403305030065325475)
            ·
              refine ⟨21645398104957545097988213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14430265403305030065325475 21645398104957545097988213)
              ·
                refine ⟨2029256072339769852936395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21645398104957545097988213 2029256072339769852936395)
                ·
                  refine ⟨3043884108509654779404593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029256072339769852936395 3043884108509654779404593)
                  ·
                    refine ⟨2282913081382241084553445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043884108509654779404593 2282913081382241084553445)
                    ·
                      refine ⟨428046202759170203353771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2282913081382241084553445 428046202759170203353771)
                      ·
                        rfl

theorem cell23_833617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_833617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833617 prefixEnd_833617 := by exact prefixLift 833617
  have htrace : WordTrace (prefixWord ++ tailWord_833617) baseStart_833617 baseEnd_833617 := by
    simpa [prefixWord, tailWord_833617, baseEnd_833617] using wordTrace_append hprefix tailTrace_833617
  have hstable : (prefixWord ++ tailWord_833617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833617).length < 2 ^ (prefixWord ++ tailWord_833617).sum := by decide
  have hdescent : baseEnd_833617 < baseStart_833617 := by decide
  rcases family_descends (prefixWord ++ tailWord_833617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833618 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_833618 : Nat := 118140960795 + 833618 * 2 ^ 59
def prefixEnd_833618 : Nat := 4983230072969 + 3 ^ 40 * 833618 * 2
def baseEnd_833618 : Nat := 142682238746608233147089

theorem tailTrace_833618 : CollatzResearch.WordTrace tailWord_833618 prefixEnd_833618 142682238746608233147089 := by
  unfold tailWord_833618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601136573487957866201377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20269697529301220976537005 7601136573487957866201377)
  ·
    refine ⟨5700852430115968399651033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7601136573487957866201377 5700852430115968399651033)
    ·
      refine ⟨4275639322586976299738275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700852430115968399651033 4275639322586976299738275)
      ·
        refine ⟨6413458983880464449607413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275639322586976299738275 6413458983880464449607413)
        ·
          refine ⟨601261779738793542150695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6413458983880464449607413 601261779738793542150695)
          ·
            refine ⟨901892669608190313226043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601261779738793542150695 901892669608190313226043)
            ·
              refine ⟨1352839004412285469839065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901892669608190313226043 1352839004412285469839065)
              ·
                refine ⟨1014629253309214102379299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352839004412285469839065 1014629253309214102379299)
                ·
                  refine ⟨1521943879963821153568949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014629253309214102379299 1521943879963821153568949)
                  ·
                    refine ⟨142682238746608233147089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1521943879963821153568949 142682238746608233147089)
                    ·
                      rfl

theorem cell23_833618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_833618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833618 prefixEnd_833618 := by exact prefixLift 833618
  have htrace : WordTrace (prefixWord ++ tailWord_833618) baseStart_833618 baseEnd_833618 := by
    simpa [prefixWord, tailWord_833618, baseEnd_833618] using wordTrace_append hprefix tailTrace_833618
  have hstable : (prefixWord ++ tailWord_833618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833618).length < 2 ^ (prefixWord ++ tailWord_833618).sum := by decide
  have hdescent : baseEnd_833618 < baseStart_833618 := by decide
  rcases family_descends (prefixWord ++ tailWord_833618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833621 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_833621 : Nat := 118140960795 + 833621 * 2 ^ 59
def prefixEnd_833621 : Nat := 4983230072969 + 3 ^ 40 * 833621 * 2
def baseEnd_833621 : Nat := 428048256681788187703753

theorem tailTrace_833621 : CollatzResearch.WordTrace tailWord_833621 prefixEnd_833621 428048256681788187703753 := by
  unfold tailWord_833621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30404655712940962977164717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20269770475293975318109811 30404655712940962977164717)
  ·
    refine ⟨11401745892352861116436769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30404655712940962977164717 11401745892352861116436769)
    ·
      refine ⟨8551309419264645837327577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11401745892352861116436769 8551309419264645837327577)
      ·
        refine ⟨6413482064448484377995683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8551309419264645837327577 6413482064448484377995683)
        ·
          refine ⟨9620223096672726566993525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413482064448484377995683 9620223096672726566993525)
          ·
            refine ⟨901895915313068115655643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9620223096672726566993525 901895915313068115655643)
            ·
              refine ⟨1352843872969602173483465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901895915313068115655643 1352843872969602173483465)
              ·
                refine ⟨1014632904727201630112599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352843872969602173483465 1014632904727201630112599)
                ·
                  refine ⟨1521949357090802445168899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014632904727201630112599 1521949357090802445168899)
                  ·
                    refine ⟨2282924035636203667753349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1521949357090802445168899 2282924035636203667753349)
                    ·
                      refine ⟨428048256681788187703753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2282924035636203667753349 428048256681788187703753)
                      ·
                        rfl

theorem cell23_833621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_833621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833621 prefixEnd_833621 := by exact prefixLift 833621
  have htrace : WordTrace (prefixWord ++ tailWord_833621) baseStart_833621 baseEnd_833621 := by
    simpa [prefixWord, tailWord_833621, baseEnd_833621] using wordTrace_append hprefix tailTrace_833621
  have hstable : (prefixWord ++ tailWord_833621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833621).length < 2 ^ (prefixWord ++ tailWord_833621).sum := by decide
  have hdescent : baseEnd_833621 < baseStart_833621 := by decide
  rcases family_descends (prefixWord ++ tailWord_833621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833624 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_833624 : Nat := 118140960795 + 833624 * 2 ^ 59
def prefixEnd_833624 : Nat := 4983230072969 + 3 ^ 40 * 833624 * 2
def baseEnd_833624 : Nat := 428049797123751675966239

theorem tailTrace_833624 : CollatzResearch.WordTrace tailWord_833624 prefixEnd_833624 428049797123751675966239 := by
  unfold tailWord_833624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202382565965047244761963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20269843421286729659682617 15202382565965047244761963)
  ·
    refine ⟨22803573848947570867142945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15202382565965047244761963 22803573848947570867142945)
    ·
      refine ⟨17102680386710678150357209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22803573848947570867142945 17102680386710678150357209)
      ·
        refine ⟨12827010290033008612767907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17102680386710678150357209 12827010290033008612767907)
        ·
          refine ⟨19240515435049512919151861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827010290033008612767907 19240515435049512919151861)
          ·
            refine ⟨1803798322035891836170487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19240515435049512919151861 1803798322035891836170487)
            ·
              refine ⟨2705697483053837754255731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803798322035891836170487 2705697483053837754255731)
              ·
                refine ⟨4058546224580756631383597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705697483053837754255731 4058546224580756631383597)
                ·
                  refine ⟨1521954834217783736768849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4058546224580756631383597 1521954834217783736768849)
                  ·
                    refine ⟨1141466125663337802576637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1521954834217783736768849 1141466125663337802576637)
                    ·
                      refine ⟨428049797123751675966239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1141466125663337802576637 428049797123751675966239)
                      ·
                        rfl

theorem cell23_833624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_833624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833624 prefixEnd_833624 := by exact prefixLift 833624
  have htrace : WordTrace (prefixWord ++ tailWord_833624) baseStart_833624 baseEnd_833624 := by
    simpa [prefixWord, tailWord_833624, baseEnd_833624] using wordTrace_append hprefix tailTrace_833624
  have hstable : (prefixWord ++ tailWord_833624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833624).length < 2 ^ (prefixWord ++ tailWord_833624).sum := by decide
  have hdescent : baseEnd_833624 < baseStart_833624 := by decide
  rcases family_descends (prefixWord ++ tailWord_833624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833641 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 1, 2, 3]
def baseStart_833641 : Nat := 118140960795 + 833641 * 2 ^ 59
def prefixEnd_833641 : Nat := 4983230072969 + 3 ^ 40 * 833641 * 2
def baseEnd_833641 : Nat := 428058526294878109453661

theorem tailTrace_833641 : CollatzResearch.WordTrace tailWord_833641 prefixEnd_833641 428058526294878109453661 := by
  unfold tailWord_833641
  simp only [CollatzResearch.WordTrace]
  refine ⟨30405385172868506392892777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20270256781912337595261851 30405385172868506392892777)
  ·
    refine ⟨22804038879651379794669583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30405385172868506392892777 22804038879651379794669583)
    ·
      refine ⟨34206058319477069692004375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22804038879651379794669583 34206058319477069692004375)
      ·
        refine ⟨51309087479215604538006563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34206058319477069692004375 51309087479215604538006563)
        ·
          refine ⟨76963631218823406807009845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51309087479215604538006563 76963631218823406807009845)
          ·
            refine ⟨7215340426764694388157173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76963631218823406807009845 7215340426764694388157173)
            ·
              refine ⟨676438165009190098889735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7215340426764694388157173 676438165009190098889735)
              ·
                refine ⟨1014657247513785148334603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676438165009190098889735 1014657247513785148334603)
                ·
                  refine ⟨1521985871270677722501905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014657247513785148334603 1521985871270677722501905)
                  ·
                    refine ⟨1141489403453008291876429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1521985871270677722501905 1141489403453008291876429)
                    ·
                      refine ⟨428058526294878109453661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1141489403453008291876429 428058526294878109453661)
                      ·
                        rfl

theorem cell23_833641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 2, 3].length) (baseStart_833641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833641 prefixEnd_833641 := by exact prefixLift 833641
  have htrace : WordTrace (prefixWord ++ tailWord_833641) baseStart_833641 baseEnd_833641 := by
    simpa [prefixWord, tailWord_833641, baseEnd_833641] using wordTrace_append hprefix tailTrace_833641
  have hstable : (prefixWord ++ tailWord_833641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833641).length < 2 ^ (prefixWord ++ tailWord_833641).sum := by decide
  have hdescent : baseEnd_833641 < baseStart_833641 := by decide
  rcases family_descends (prefixWord ++ tailWord_833641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833655 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 1, 2, 2]
def baseStart_833655 : Nat := 118140960795 + 833655 * 2 ^ 59
def prefixEnd_833655 : Nat := 4983230072969 + 3 ^ 40 * 833655 * 2
def baseEnd_833655 : Nat := 428065715024041054678597

theorem tailTrace_833655 : CollatzResearch.WordTrace tailWord_833655 prefixEnd_833655 428065715024041054678597 := by
  unfold tailWord_833655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30405895794817786783902419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20270597196545191189268279 30405895794817786783902419)
  ·
    refine ⟨45608843692226680175853629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30405895794817786783902419 45608843692226680175853629)
    ·
      refine ⟨17103316384585005065945111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45608843692226680175853629 17103316384585005065945111)
      ·
        refine ⟨25654974576877507598917667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17103316384585005065945111 25654974576877507598917667)
        ·
          refine ⟨38482461865316261398376501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25654974576877507598917667 38482461865316261398376501)
          ·
            refine ⟨3607730799873399506097797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38482461865316261398376501 3607730799873399506097797)
            ·
              refine ⟨676449524976262407393337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3607730799873399506097797 676449524976262407393337)
              ·
                refine ⟨507337143732196805545003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676449524976262407393337 507337143732196805545003)
                ·
                  refine ⟨761005715598295208317505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507337143732196805545003 761005715598295208317505)
                  ·
                    refine ⟨570754286698721406238129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761005715598295208317505 570754286698721406238129)
                    ·
                      refine ⟨428065715024041054678597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570754286698721406238129 428065715024041054678597)
                      ·
                        rfl

theorem cell23_833655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_833655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833655 prefixEnd_833655 := by exact prefixLift 833655
  have htrace : WordTrace (prefixWord ++ tailWord_833655) baseStart_833655 baseEnd_833655 := by
    simpa [prefixWord, tailWord_833655, baseEnd_833655] using wordTrace_append hprefix tailTrace_833655
  have hstable : (prefixWord ++ tailWord_833655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833655).length < 2 ^ (prefixWord ++ tailWord_833655).sum := by decide
  have hdescent : baseEnd_833655 < baseStart_833655 := by decide
  rcases family_descends (prefixWord ++ tailWord_833655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833657 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_833657 : Nat := 118140960795 + 833657 * 2 ^ 59
def prefixEnd_833657 : Nat := 4983230072969 + 3 ^ 40 * 833657 * 2
def baseEnd_833657 : Nat := 142688913995116682284529

theorem tailTrace_833657 : CollatzResearch.WordTrace tailWord_833657 prefixEnd_833657 142688913995116682284529 := by
  unfold tailWord_833657
  simp only [CollatzResearch.WordTrace]
  refine ⟨30405968740810541125475225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20270645827207027416983483 30405968740810541125475225)
  ·
    refine ⟨22804476555607905844106419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30405968740810541125475225 22804476555607905844106419)
    ·
      refine ⟨34206714833411858766159629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22804476555607905844106419 34206714833411858766159629)
      ·
        refine ⟨12827518062529447037309861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34206714833411858766159629 12827518062529447037309861)
        ·
          refine ⟨2405159636724271319495599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12827518062529447037309861 2405159636724271319495599)
          ·
            refine ⟨3607739455086406979243399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405159636724271319495599 3607739455086406979243399)
            ·
              refine ⟨5411609182629610468865099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607739455086406979243399 5411609182629610468865099)
              ·
                refine ⟨8117413773944415703297649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411609182629610468865099 8117413773944415703297649)
                ·
                  refine ⟨6088060330458311777473237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8117413773944415703297649 6088060330458311777473237)
                  ·
                    refine ⟨142688913995116682284529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6088060330458311777473237 142688913995116682284529)
                    ·
                      rfl

theorem cell23_833657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_833657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833657 prefixEnd_833657 := by exact prefixLift 833657
  have htrace : WordTrace (prefixWord ++ tailWord_833657) baseStart_833657 baseEnd_833657 := by
    simpa [prefixWord, tailWord_833657, baseEnd_833657] using wordTrace_append hprefix tailTrace_833657
  have hstable : (prefixWord ++ tailWord_833657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833657).length < 2 ^ (prefixWord ++ tailWord_833657).sum := by decide
  have hdescent : baseEnd_833657 < baseStart_833657 := by decide
  rcases family_descends (prefixWord ++ tailWord_833657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833671 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_833671 : Nat := 118140960795 + 833671 * 2 ^ 59
def prefixEnd_833671 : Nat := 4983230072969 + 3 ^ 40 * 833671 * 2
def baseEnd_833671 : Nat := 428073930714512992078523

theorem tailTrace_833671 : CollatzResearch.WordTrace tailWord_833671 prefixEnd_833671 428073930714512992078523 := by
  unfold tailWord_833671
  simp only [CollatzResearch.WordTrace]
  refine ⟨30406479362759821516484867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20270986241839881010989911 30406479362759821516484867)
  ·
    refine ⟨45609719044139732274727301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30406479362759821516484867 45609719044139732274727301)
    ·
      refine ⟨8551822320776199801511369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45609719044139732274727301 8551822320776199801511369)
      ·
        refine ⟨6413866740582149851133527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8551822320776199801511369 6413866740582149851133527)
        ·
          refine ⟨9620800110873224776700291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413866740582149851133527 9620800110873224776700291)
          ·
            refine ⟨14431200166309837165050437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620800110873224776700291 14431200166309837165050437)
            ·
              refine ⟨2705850031183094468446957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14431200166309837165050437 2705850031183094468446957)
              ·
                refine ⟨1014693761693660425667609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2705850031183094468446957 1014693761693660425667609)
                ·
                  refine ⟨761020321270245319250707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1014693761693660425667609 761020321270245319250707)
                  ·
                    refine ⟨1141530481905367978876061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 761020321270245319250707 1141530481905367978876061)
                    ·
                      refine ⟨428073930714512992078523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1141530481905367978876061 428073930714512992078523)
                      ·
                        rfl

theorem cell23_833671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_833671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833671 prefixEnd_833671 := by exact prefixLift 833671
  have htrace : WordTrace (prefixWord ++ tailWord_833671) baseStart_833671 baseEnd_833671 := by
    simpa [prefixWord, tailWord_833671, baseEnd_833671] using wordTrace_append hprefix tailTrace_833671
  have hstable : (prefixWord ++ tailWord_833671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833671).length < 2 ^ (prefixWord ++ tailWord_833671).sum := by decide
  have hdescent : baseEnd_833671 < baseStart_833671 := by decide
  rcases family_descends (prefixWord ++ tailWord_833671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833686 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_833686 : Nat := 118140960795 + 833686 * 2 ^ 59
def prefixEnd_833686 : Nat := 4983230072969 + 3 ^ 40 * 833686 * 2
def baseEnd_833686 : Nat := 142693877641443477796985

theorem tailTrace_833686 : CollatzResearch.WordTrace tailWord_833686 prefixEnd_833686 142693877641443477796985 := by
  unfold tailWord_833686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900439153606592442392557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20271350971803652718853941 1900439153606592442392557)
  ·
    refine ⟨712664682602472165897209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1900439153606592442392557 712664682602472165897209)
    ·
      refine ⟨534498511951854124422907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 712664682602472165897209 534498511951854124422907)
      ·
        refine ⟨801747767927781186634361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534498511951854124422907 801747767927781186634361)
        ·
          refine ⟨601310825945835889975771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 801747767927781186634361 601310825945835889975771)
          ·
            refine ⟨901966238918753834963657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601310825945835889975771 901966238918753834963657)
            ·
              refine ⟨676474679189065376222743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901966238918753834963657 676474679189065376222743)
              ·
                refine ⟨1014712018783598064334115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676474679189065376222743 1014712018783598064334115)
                ·
                  refine ⟨1522068028175397096501173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014712018783598064334115 1522068028175397096501173)
                  ·
                    refine ⟨142693877641443477796985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1522068028175397096501173 142693877641443477796985)
                    ·
                      rfl

theorem cell23_833686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_833686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833686 prefixEnd_833686 := by exact prefixLift 833686
  have htrace : WordTrace (prefixWord ++ tailWord_833686) baseStart_833686 baseEnd_833686 := by
    simpa [prefixWord, tailWord_833686, baseEnd_833686] using wordTrace_append hprefix tailTrace_833686
  have hstable : (prefixWord ++ tailWord_833686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833686).length < 2 ^ (prefixWord ++ tailWord_833686).sum := by decide
  have hdescent : baseEnd_833686 < baseStart_833686 := by decide
  rcases family_descends (prefixWord ++ tailWord_833686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833728 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 1, 4, 2]
def baseStart_833728 : Nat := 118140960795 + 833728 * 2 ^ 59
def prefixEnd_833728 : Nat := 4983230072969 + 3 ^ 40 * 833728 * 2
def baseEnd_833728 : Nat := 428103199111819269065761

theorem tailTrace_833728 : CollatzResearch.WordTrace tailWord_833728 prefixEnd_833728 428103199111819269065761 := by
  unfold tailWord_833728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15204279161776660125654919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20272372215702213500873225 15204279161776660125654919)
  ·
    refine ⟨22806418742664990188482379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15204279161776660125654919 22806418742664990188482379)
    ·
      refine ⟨34209628113997485282723569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22806418742664990188482379 34209628113997485282723569)
      ·
        refine ⟨25657221085498113962042677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34209628113997485282723569 25657221085498113962042677)
        ·
          refine ⟨2405364476765448183941501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25657221085498113962042677 2405364476765448183941501)
          ·
            refine ⟨902011678787043068978063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2405364476765448183941501 902011678787043068978063)
            ·
              refine ⟨1353017518180564603467095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902011678787043068978063 1353017518180564603467095)
              ·
                refine ⟨2029526277270846905200643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353017518180564603467095 2029526277270846905200643)
                ·
                  refine ⟨3044289415906270357800965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029526277270846905200643 3044289415906270357800965)
                  ·
                    refine ⟨570804265482425692087681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3044289415906270357800965 570804265482425692087681)
                    ·
                      refine ⟨428103199111819269065761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570804265482425692087681 428103199111819269065761)
                      ·
                        rfl

theorem cell23_833728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_833728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833728 prefixEnd_833728 := by exact prefixLift 833728
  have htrace : WordTrace (prefixWord ++ tailWord_833728) baseStart_833728 baseEnd_833728 := by
    simpa [prefixWord, tailWord_833728, baseEnd_833728] using wordTrace_append hprefix tailTrace_833728
  have hstable : (prefixWord ++ tailWord_833728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833728).length < 2 ^ (prefixWord ++ tailWord_833728).sum := by decide
  have hdescent : baseEnd_833728 < baseStart_833728 := by decide
  rcases family_descends (prefixWord ++ tailWord_833728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833768 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 5]
def baseStart_833768 : Nat := 118140960795 + 833768 * 2 ^ 59
def prefixEnd_833768 : Nat := 4983230072969 + 3 ^ 40 * 833768 * 2
def baseEnd_833768 : Nat := 47569304259777679173953

theorem tailTrace_833768 : CollatzResearch.WordTrace tailWord_833768 prefixEnd_833768 47569304259777679173953 := by
  unfold tailWord_833768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205008621704203541382979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20273344828938938055177305 15205008621704203541382979)
  ·
    refine ⟨22807512932556305312074469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15205008621704203541382979 22807512932556305312074469)
    ·
      refine ⟨4276408674854307246013963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22807512932556305312074469 4276408674854307246013963)
      ·
        refine ⟨6414613012281460869020945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276408674854307246013963 6414613012281460869020945)
        ·
          refine ⟨4810959759211095651765709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6414613012281460869020945 4810959759211095651765709)
          ·
            refine ⟨1804109909704160869412141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4810959759211095651765709 1804109909704160869412141)
            ·
              refine ⟨676541216139060326029553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804109909704160869412141 676541216139060326029553)
              ·
                refine ⟨507405912104295244522165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676541216139060326029553 507405912104295244522165)
                ·
                  refine ⟨47569304259777679173953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 507405912104295244522165 47569304259777679173953)
                  ·
                    rfl

theorem cell23_833768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 5].length) (baseStart_833768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833768 prefixEnd_833768 := by exact prefixLift 833768
  have htrace : WordTrace (prefixWord ++ tailWord_833768) baseStart_833768 baseEnd_833768 := by
    simpa [prefixWord, tailWord_833768, baseEnd_833768] using wordTrace_append hprefix tailTrace_833768
  have hstable : (prefixWord ++ tailWord_833768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833768).length < 2 ^ (prefixWord ++ tailWord_833768).sum := by decide
  have hdescent : baseEnd_833768 < baseStart_833768 := by decide
  rcases family_descends (prefixWord ++ tailWord_833768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833787 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_833787 : Nat := 118140960795 + 833787 * 2 ^ 59
def prefixEnd_833787 : Nat := 4983230072969 + 3 ^ 40 * 833787 * 2
def baseEnd_833787 : Nat := 428133494470434538227989

theorem tailTrace_833787 : CollatzResearch.WordTrace tailWord_833787 prefixEnd_833787 428133494470434538227989 := by
  unfold tailWord_833787
  simp only [CollatzResearch.WordTrace]
  refine ⟨30410710230339573327707615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20273806820226382218471743 30410710230339573327707615)
  ·
    refine ⟨45616065345509359991561423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30410710230339573327707615 45616065345509359991561423)
    ·
      refine ⟨68424098018264039987342135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45616065345509359991561423 68424098018264039987342135)
      ·
        refine ⟨102636147027396059981013203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68424098018264039987342135 102636147027396059981013203)
        ·
          refine ⟨153954220541094089971519805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102636147027396059981013203 153954220541094089971519805)
          ·
            refine ⟨57732832702910283739319927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153954220541094089971519805 57732832702910283739319927)
            ·
              refine ⟨86599249054365425608979891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57732832702910283739319927 86599249054365425608979891)
              ·
                refine ⟨129898873581548138413469837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86599249054365425608979891 129898873581548138413469837)
                ·
                  refine ⟨48712077593080551905051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129898873581548138413469837 48712077593080551905051189)
                  ·
                    refine ⟨4566757274351301741098549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48712077593080551905051189 4566757274351301741098549)
                    ·
                      refine ⟨428133494470434538227989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4566757274351301741098549 428133494470434538227989)
                      ·
                        rfl

theorem cell23_833787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_833787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833787 prefixEnd_833787 := by exact prefixLift 833787
  have htrace : WordTrace (prefixWord ++ tailWord_833787) baseStart_833787 baseEnd_833787 := by
    simpa [prefixWord, tailWord_833787, baseEnd_833787] using wordTrace_append hprefix tailTrace_833787
  have hstable : (prefixWord ++ tailWord_833787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833787).length < 2 ^ (prefixWord ++ tailWord_833787).sum := by decide
  have hdescent : baseEnd_833787 < baseStart_833787 := by decide
  rcases family_descends (prefixWord ++ tailWord_833787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833801 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_833801 : Nat := 118140960795 + 833801 * 2 ^ 59
def prefixEnd_833801 : Nat := 4983230072969 + 3 ^ 40 * 833801 * 2
def baseEnd_833801 : Nat := 428140683199597483452925

theorem tailTrace_833801 : CollatzResearch.WordTrace tailWord_833801 prefixEnd_833801 428140683199597483452925 := by
  unfold tailWord_833801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30411220852288853718717257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20274147234859235812478171 30411220852288853718717257)
  ·
    refine ⟨22808415639216640289037943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30411220852288853718717257 22808415639216640289037943)
    ·
      refine ⟨34212623458824960433556915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22808415639216640289037943 34212623458824960433556915)
      ·
        refine ⟨51318935188237440650335373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34212623458824960433556915 51318935188237440650335373)
        ·
          refine ⟨19244600695589040243875765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51318935188237440650335373 19244600695589040243875765)
          ·
            refine ⟨1804181315211472522863353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19244600695589040243875765 1804181315211472522863353)
            ·
              refine ⟨1353135986408604392147515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804181315211472522863353 1353135986408604392147515)
              ·
                refine ⟨2029703979612906588221273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353135986408604392147515 2029703979612906588221273)
                ·
                  refine ⟨1522277984709679941165955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2029703979612906588221273 1522277984709679941165955)
                  ·
                    refine ⟨2283416977064519911748933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522277984709679941165955 2283416977064519911748933)
                    ·
                      refine ⟨428140683199597483452925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2283416977064519911748933 428140683199597483452925)
                      ·
                        rfl

theorem cell23_833801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_833801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833801 prefixEnd_833801 := by exact prefixLift 833801
  have htrace : WordTrace (prefixWord ++ tailWord_833801) baseStart_833801 baseEnd_833801 := by
    simpa [prefixWord, tailWord_833801, baseEnd_833801] using wordTrace_append hprefix tailTrace_833801
  have hstable : (prefixWord ++ tailWord_833801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833801).length < 2 ^ (prefixWord ++ tailWord_833801).sum := by decide
  have hdescent : baseEnd_833801 < baseStart_833801 := by decide
  rcases family_descends (prefixWord ++ tailWord_833801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833807 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 10]
def baseStart_833807 : Nat := 118140960795 + 833807 * 2 ^ 59
def prefixEnd_833807 : Nat := 4983230072969 + 3 ^ 40 * 833807 * 2
def baseEnd_833807 : Nat := 47571529342613828886433

theorem tailTrace_833807 : CollatzResearch.WordTrace tailWord_833807 prefixEnd_833807 47571529342613828886433 := by
  unfold tailWord_833807
  simp only [CollatzResearch.WordTrace]
  refine ⟨30411439690267116743435675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20274293126844744495623783 30411439690267116743435675)
  ·
    refine ⟨45617159535400675115153513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30411439690267116743435675 45617159535400675115153513)
    ·
      refine ⟨34212869651550506336365135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45617159535400675115153513 34212869651550506336365135)
      ·
        refine ⟨51319304477325759504547703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34212869651550506336365135 51319304477325759504547703)
        ·
          refine ⟨76978956715988639256821555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51319304477325759504547703 76978956715988639256821555)
          ·
            refine ⟨115468435073982958885232333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76978956715988639256821555 115468435073982958885232333)
            ·
              refine ⟨43300663152743609581962125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115468435073982958885232333 43300663152743609581962125)
              ·
                refine ⟨16237748682278853593235797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43300663152743609581962125 16237748682278853593235797)
                ·
                  refine ⟨47571529342613828886433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 16237748682278853593235797 47571529342613828886433)
                  ·
                    rfl

theorem cell23_833807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 10].length) (baseStart_833807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833807 prefixEnd_833807 := by exact prefixLift 833807
  have htrace : WordTrace (prefixWord ++ tailWord_833807) baseStart_833807 baseEnd_833807 := by
    simpa [prefixWord, tailWord_833807, baseEnd_833807] using wordTrace_append hprefix tailTrace_833807
  have hstable : (prefixWord ++ tailWord_833807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833807).length < 2 ^ (prefixWord ++ tailWord_833807).sum := by decide
  have hdescent : baseEnd_833807 < baseStart_833807 := by decide
  rcases family_descends (prefixWord ++ tailWord_833807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833928 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_833928 : Nat := 118140960795 + 833928 * 2 ^ 59
def prefixEnd_833928 : Nat := 4983230072969 + 3 ^ 40 * 833928 * 2
def baseEnd_833928 : Nat := 428205895242718486564841

theorem tailTrace_833928 : CollatzResearch.WordTrace tailWord_833928 prefixEnd_833928 428205895242718486564841 := by
  unfold tailWord_833928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15207926461414377204295219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20277235281885836272393625 15207926461414377204295219)
  ·
    refine ⟨22811889692121565806442829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15207926461414377204295219 22811889692121565806442829)
    ·
      refine ⟨8554458634545587177416061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22811889692121565806442829 8554458634545587177416061)
      ·
        refine ⟨3207921987954595191531023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8554458634545587177416061 3207921987954595191531023)
        ·
          refine ⟨4811882981931892787296535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207921987954595191531023 4811882981931892787296535)
          ·
            refine ⟨7217824472897839180944803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811882981931892787296535 7217824472897839180944803)
            ·
              refine ⟨10826736709346758771417205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217824472897839180944803 10826736709346758771417205)
              ·
                refine ⟨1015006566501258634820363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10826736709346758771417205 1015006566501258634820363)
                ·
                  refine ⟨1522509849751887952230545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015006566501258634820363 1522509849751887952230545)
                  ·
                    refine ⟨1141882387313915964172909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1522509849751887952230545 1141882387313915964172909)
                    ·
                      refine ⟨428205895242718486564841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1141882387313915964172909 428205895242718486564841)
                      ·
                        rfl

theorem cell23_833928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_833928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833928 prefixEnd_833928 := by exact prefixLift 833928
  have htrace : WordTrace (prefixWord ++ tailWord_833928) baseStart_833928 baseEnd_833928 := by
    simpa [prefixWord, tailWord_833928, baseEnd_833928] using wordTrace_append hprefix tailTrace_833928
  have hstable : (prefixWord ++ tailWord_833928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833928).length < 2 ^ (prefixWord ++ tailWord_833928).sum := by decide
  have hdescent : baseEnd_833928 < baseStart_833928 := by decide
  rcases family_descends (prefixWord ++ tailWord_833928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833964 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_833964 : Nat := 118140960795 + 833964 * 2 ^ 59
def prefixEnd_833964 : Nat := 4983230072969 + 3 ^ 40 * 833964 * 2
def baseEnd_833964 : Nat := 428224380546280345714675

theorem tailTrace_833964 : CollatzResearch.WordTrace tailWord_833964 prefixEnd_833964 428224380546280345714675 := by
  unfold tailWord_833964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208582975349166278450473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20278110633798888371267297 15208582975349166278450473)
  ·
    refine ⟨11406437231511874708837855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15208582975349166278450473 11406437231511874708837855)
    ·
      refine ⟨17109655847267812063256783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11406437231511874708837855 17109655847267812063256783)
      ·
        refine ⟨25664483770901718094885175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17109655847267812063256783 25664483770901718094885175)
        ·
          refine ⟨38496725656352577142327763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25664483770901718094885175 38496725656352577142327763)
          ·
            refine ⟨57745088484528865713491645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38496725656352577142327763 57745088484528865713491645)
            ·
              refine ⟨21654408181698324642559367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57745088484528865713491645 21654408181698324642559367)
              ·
                refine ⟨32481612272547486963839051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21654408181698324642559367 32481612272547486963839051)
                ·
                  refine ⟨48722418408821230445758577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32481612272547486963839051 48722418408821230445758577)
                  ·
                    refine ⟨36541813806615922834318933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48722418408821230445758577 36541813806615922834318933)
                    ·
                      refine ⟨428224380546280345714675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36541813806615922834318933 428224380546280345714675)
                      ·
                        rfl

theorem cell23_833964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_833964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833964 prefixEnd_833964 := by exact prefixLift 833964
  have htrace : WordTrace (prefixWord ++ tailWord_833964) baseStart_833964 baseEnd_833964 := by
    simpa [prefixWord, tailWord_833964, baseEnd_833964] using wordTrace_append hprefix tailTrace_833964
  have hstable : (prefixWord ++ tailWord_833964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833964).length < 2 ^ (prefixWord ++ tailWord_833964).sum := by decide
  have hdescent : baseEnd_833964 < baseStart_833964 := by decide
  rcases family_descends (prefixWord ++ tailWord_833964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833972 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_833972 : Nat := 118140960795 + 833972 * 2 ^ 59
def prefixEnd_833972 : Nat := 4983230072969 + 3 ^ 40 * 833972 * 2
def baseEnd_833972 : Nat := 428228488391516314414639

theorem tailTrace_833972 : CollatzResearch.WordTrace tailWord_833972 prefixEnd_833972 428228488391516314414639 := by
  unfold tailWord_833972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208728867334674961596085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20278305156446233282128113 15208728867334674961596085)
  ·
    refine ⟨1425818331312625777649633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15208728867334674961596085 1425818331312625777649633)
    ·
      refine ⟨1069363748484469333237225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1425818331312625777649633 1069363748484469333237225)
      ·
        refine ⟨802022811363351999927919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069363748484469333237225 802022811363351999927919)
        ·
          refine ⟨1203034217045027999891879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802022811363351999927919 1203034217045027999891879)
          ·
            refine ⟨1804551325567541999837819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203034217045027999891879 1804551325567541999837819)
            ·
              refine ⟨2706826988351312999756729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804551325567541999837819 2706826988351312999756729)
              ·
                refine ⟨2030120241263484749817547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706826988351312999756729 2030120241263484749817547)
                ·
                  refine ⟨3045180361895227124726321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030120241263484749817547 3045180361895227124726321)
                  ·
                    refine ⟨2283885271421420343544741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3045180361895227124726321 2283885271421420343544741)
                    ·
                      refine ⟨428228488391516314414639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2283885271421420343544741 428228488391516314414639)
                      ·
                        rfl

theorem cell23_833972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_833972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833972 prefixEnd_833972 := by exact prefixLift 833972
  have htrace : WordTrace (prefixWord ++ tailWord_833972) baseStart_833972 baseEnd_833972 := by
    simpa [prefixWord, tailWord_833972, baseEnd_833972] using wordTrace_append hprefix tailTrace_833972
  have hstable : (prefixWord ++ tailWord_833972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833972).length < 2 ^ (prefixWord ++ tailWord_833972).sum := by decide
  have hdescent : baseEnd_833972 < baseStart_833972 := by decide
  rcases family_descends (prefixWord ++ tailWord_833972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
